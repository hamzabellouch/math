import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical110
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical116
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical119
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical120

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA896 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB896 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC896 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm896 : Integer.Sparse Master := [(Sum.inr 2577, 2), (Sum.inr 3729, 1), (Sum.inr 3840, 2), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

theorem sourceEq896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm896 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA896 + difference 1 0) (sourceB896 + difference 0 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2577) := by
    have ha : (tripleCharges (sourceA896 + difference 1 0) (sourceB896 + difference 0 1) sourceC896) = raw14798 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14798; decide +kernel
    rw [ha]
    exact (canonical14798 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA896 + difference 1 1) (sourceB896 + difference 1 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA896 + difference 1 1) (sourceB896 + difference 1 1) sourceC896) = raw14791 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14791; decide +kernel
    rw [ha]
    exact (canonical14791 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA896 + difference 1 2) (sourceB896 + difference 2 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3729) := by
    have ha : (tripleCharges (sourceA896 + difference 1 2) (sourceB896 + difference 2 1) sourceC896) = raw14799 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14799; decide +kernel
    rw [ha]
    exact (canonical14799 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA896 + difference 1 3) (sourceB896 + difference 3 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA896 + difference 1 3) (sourceB896 + difference 3 1) sourceC896) = raw14800 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14800; decide +kernel
    rw [ha]
    exact (canonical14800 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA896 + difference 1 4) (sourceB896 + difference 4 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA896 + difference 1 4) (sourceB896 + difference 4 1) sourceC896) = raw14801 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14801; decide +kernel
    rw [ha]
    exact (canonical14801 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA896 + difference 1 5) (sourceB896 + difference 5 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2577) := by
    have ha : (tripleCharges (sourceA896 + difference 1 5) (sourceB896 + difference 5 1) sourceC896) = raw14802 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14802; decide +kernel
    rw [ha]
    exact (canonical14802 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA896 + sourceB896) sourceC896) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA896 + sourceB896) sourceC896) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA896 sourceB896 sourceC896 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA896 sourceB896 sourceC896
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm896, Integer.Sparse.eval]
  linarith only [hs]

def sourceA897 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB897 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC897 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm897 : Integer.Sparse Master := [(Sum.inr 2974, 1), (Sum.inr 3780, 1), (Sum.inr 3781, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

theorem sourceEq897 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm897 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA897 + difference 0 1) (sourceB897 + difference 1 0) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA897 + difference 0 1) (sourceB897 + difference 1 0) sourceC897) = raw14792 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14792; decide +kernel
    rw [ha]
    exact (canonical14792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA897 + difference 1 1) (sourceB897 + difference 1 1) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA897 + difference 1 1) (sourceB897 + difference 1 1) sourceC897) = raw14791 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14791; decide +kernel
    rw [ha]
    exact (canonical14791 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA897 + difference 2 1) (sourceB897 + difference 1 2) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA897 + difference 2 1) (sourceB897 + difference 1 2) sourceC897) = raw14803 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14803; decide +kernel
    rw [ha]
    exact (canonical14803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA897 + difference 3 1) (sourceB897 + difference 1 3) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA897 + difference 3 1) (sourceB897 + difference 1 3) sourceC897) = raw14804 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14804; decide +kernel
    rw [ha]
    exact (canonical14804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA897 + difference 4 1) (sourceB897 + difference 1 4) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA897 + difference 4 1) (sourceB897 + difference 1 4) sourceC897) = raw14805 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14805; decide +kernel
    rw [ha]
    exact (canonical14805 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA897 + difference 5 1) (sourceB897 + difference 1 5) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA897 + difference 5 1) (sourceB897 + difference 1 5) sourceC897) = raw14806 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14806; decide +kernel
    rw [ha]
    exact (canonical14806 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA897 + sourceB897) sourceC897) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA897 + sourceB897) sourceC897) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA897 sourceB897 sourceC897 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA897 sourceB897 sourceC897
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm897, Integer.Sparse.eval]
  linarith only [hs]

def sourceA898 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB898 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC898 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm898 : Integer.Sparse Master := [(Sum.inr 2971, 1), (Sum.inr 3717, 1), (Sum.inr 3720, 1), (Sum.inr 3729, 1), (Sum.inr 3730, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

theorem sourceEq898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm898 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA898 + difference 0 2) (sourceB898 + difference 2 0) sourceC898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA898 + difference 0 2) (sourceB898 + difference 2 0) sourceC898) = raw14793 := by
      apply Matrix.ext; unfold tripleCharges sourceA898 sourceB898 sourceC898 difference raw14793; decide +kernel
    rw [ha]
    exact (canonical14793 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA898 + difference 1 2) (sourceB898 + difference 2 1) sourceC898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3729) := by
    have ha : (tripleCharges (sourceA898 + difference 1 2) (sourceB898 + difference 2 1) sourceC898) = raw14799 := by
      apply Matrix.ext; unfold tripleCharges sourceA898 sourceB898 sourceC898 difference raw14799; decide +kernel
    rw [ha]
    exact (canonical14799 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA898 + difference 2 2) (sourceB898 + difference 2 2) sourceC898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA898 + difference 2 2) (sourceB898 + difference 2 2) sourceC898) = raw14791 := by
      apply Matrix.ext; unfold tripleCharges sourceA898 sourceB898 sourceC898 difference raw14791; decide +kernel
    rw [ha]
    exact (canonical14791 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA898 + difference 3 2) (sourceB898 + difference 2 3) sourceC898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3717) := by
    have ha : (tripleCharges (sourceA898 + difference 3 2) (sourceB898 + difference 2 3) sourceC898) = raw14807 := by
      apply Matrix.ext; unfold tripleCharges sourceA898 sourceB898 sourceC898 difference raw14807; decide +kernel
    rw [ha]
    exact (canonical14807 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA898 + difference 4 2) (sourceB898 + difference 2 4) sourceC898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2971) := by
    have ha : (tripleCharges (sourceA898 + difference 4 2) (sourceB898 + difference 2 4) sourceC898) = raw14808 := by
      apply Matrix.ext; unfold tripleCharges sourceA898 sourceB898 sourceC898 difference raw14808; decide +kernel
    rw [ha]
    exact (canonical14808 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA898 + difference 5 2) (sourceB898 + difference 2 5) sourceC898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA898 + difference 5 2) (sourceB898 + difference 2 5) sourceC898) = raw14809 := by
      apply Matrix.ext; unfold tripleCharges sourceA898 sourceB898 sourceC898 difference raw14809; decide +kernel
    rw [ha]
    exact (canonical14809 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA898 + sourceB898) sourceC898) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA898 + sourceB898) sourceC898) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA898 sourceB898 sourceC898 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA898 sourceB898 sourceC898
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm898, Integer.Sparse.eval]
  linarith only [hs]

def sourceA899 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB899 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC899 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm899 : Integer.Sparse Master := [(Sum.inr 2549, 1), (Sum.inr 2578, 1), (Sum.inr 3717, 1), (Sum.inr 3780, 1), (Sum.inr 3840, 1), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

theorem sourceEq899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm899 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA899 + difference 3 0) (sourceB899 + difference 0 3) sourceC899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2549) := by
    have ha : (tripleCharges (sourceA899 + difference 3 0) (sourceB899 + difference 0 3) sourceC899) = raw14810 := by
      apply Matrix.ext; unfold tripleCharges sourceA899 sourceB899 sourceC899 difference raw14810; decide +kernel
    rw [ha]
    exact (canonical14810 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA899 + difference 3 1) (sourceB899 + difference 1 3) sourceC899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA899 + difference 3 1) (sourceB899 + difference 1 3) sourceC899) = raw14804 := by
      apply Matrix.ext; unfold tripleCharges sourceA899 sourceB899 sourceC899 difference raw14804; decide +kernel
    rw [ha]
    exact (canonical14804 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA899 + difference 3 2) (sourceB899 + difference 2 3) sourceC899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3717) := by
    have ha : (tripleCharges (sourceA899 + difference 3 2) (sourceB899 + difference 2 3) sourceC899) = raw14807 := by
      apply Matrix.ext; unfold tripleCharges sourceA899 sourceB899 sourceC899 difference raw14807; decide +kernel
    rw [ha]
    exact (canonical14807 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA899 + difference 3 3) (sourceB899 + difference 3 3) sourceC899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA899 + difference 3 3) (sourceB899 + difference 3 3) sourceC899) = raw14791 := by
      apply Matrix.ext; unfold tripleCharges sourceA899 sourceB899 sourceC899 difference raw14791; decide +kernel
    rw [ha]
    exact (canonical14791 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA899 + difference 3 4) (sourceB899 + difference 4 3) sourceC899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA899 + difference 3 4) (sourceB899 + difference 4 3) sourceC899) = raw14811 := by
      apply Matrix.ext; unfold tripleCharges sourceA899 sourceB899 sourceC899 difference raw14811; decide +kernel
    rw [ha]
    exact (canonical14811 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA899 + difference 3 5) (sourceB899 + difference 5 3) sourceC899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2578) := by
    have ha : (tripleCharges (sourceA899 + difference 3 5) (sourceB899 + difference 5 3) sourceC899) = raw14812 := by
      apply Matrix.ext; unfold tripleCharges sourceA899 sourceB899 sourceC899 difference raw14812; decide +kernel
    rw [ha]
    exact (canonical14812 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA899 + sourceB899) sourceC899) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA899 + sourceB899) sourceC899) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA899 sourceB899 sourceC899 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA899 sourceB899 sourceC899
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm899, Integer.Sparse.eval]
  linarith only [hs]

def sourceA900 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB900 : Charge := ![0, 1, -1, 2, 0, -2]
def sourceC900 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceForm900 : Integer.Sparse Master := [(Sum.inr 4783, 2), (Sum.inr 4784, 1), (Sum.inr 4816, 2), (Sum.inr 5131, 2), (Sum.inr 5138, 2), (Sum.inr 5154, 2), (Sum.inr 5267, 2), (Sum.inr 5342, 2), (Sum.inr 5360, 2), (Sum.inr 5381, 2), (Sum.inr 5397, 2), (Sum.inr 5412, 2), (Sum.inr 5424, 2), (Sum.inr 5425, 4), (Sum.inr 5435, 1)]

theorem sourceEq900 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm900 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA900 + difference 0 1) (sourceB900 + difference 1 0) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA900 + difference 0 1) (sourceB900 + difference 1 0) sourceC900) = raw14813 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14813; decide +kernel
    rw [ha]
    exact (canonical14813 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA900 + difference 0 2) (sourceB900 + difference 2 0) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA900 + difference 0 2) (sourceB900 + difference 2 0) sourceC900) = raw14814 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14814; decide +kernel
    rw [ha]
    exact (canonical14814 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA900 + difference 0 3) (sourceB900 + difference 3 0) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA900 + difference 0 3) (sourceB900 + difference 3 0) sourceC900) = raw14815 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14815; decide +kernel
    rw [ha]
    exact (canonical14815 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA900 + difference 0 4) (sourceB900 + difference 4 0) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA900 + difference 0 4) (sourceB900 + difference 4 0) sourceC900) = raw14816 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14816; decide +kernel
    rw [ha]
    exact (canonical14816 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA900 + difference 0 5) (sourceB900 + difference 5 0) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA900 + difference 0 5) (sourceB900 + difference 5 0) sourceC900) = raw14817 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14817; decide +kernel
    rw [ha]
    exact (canonical14817 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA900 + difference 1 0) (sourceB900 + difference 0 1) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA900 + difference 1 0) (sourceB900 + difference 0 1) sourceC900) = raw14101 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14101; decide +kernel
    rw [ha]
    exact (canonical14101 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA900 + difference 1 2) (sourceB900 + difference 2 1) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA900 + difference 1 2) (sourceB900 + difference 2 1) sourceC900) = raw14818 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14818; decide +kernel
    rw [ha]
    exact (canonical14818 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA900 + difference 1 3) (sourceB900 + difference 3 1) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA900 + difference 1 3) (sourceB900 + difference 3 1) sourceC900) = raw14819 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14819; decide +kernel
    rw [ha]
    exact (canonical14819 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA900 + difference 1 4) (sourceB900 + difference 4 1) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA900 + difference 1 4) (sourceB900 + difference 4 1) sourceC900) = raw14820 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14820; decide +kernel
    rw [ha]
    exact (canonical14820 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA900 + difference 1 5) (sourceB900 + difference 5 1) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA900 + difference 1 5) (sourceB900 + difference 5 1) sourceC900) = raw14075 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14075; decide +kernel
    rw [ha]
    exact (canonical14075 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA900 + difference 2 0) (sourceB900 + difference 0 2) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5154) := by
    have ha : (tripleCharges (sourceA900 + difference 2 0) (sourceB900 + difference 0 2) sourceC900) = raw14821 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14821; decide +kernel
    rw [ha]
    exact (canonical14821 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA900 + difference 2 1) (sourceB900 + difference 1 2) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5342) := by
    have ha : (tripleCharges (sourceA900 + difference 2 1) (sourceB900 + difference 1 2) sourceC900) = raw14822 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14822; decide +kernel
    rw [ha]
    exact (canonical14822 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA900 + difference 2 3) (sourceB900 + difference 3 2) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5131) := by
    have ha : (tripleCharges (sourceA900 + difference 2 3) (sourceB900 + difference 3 2) sourceC900) = raw14823 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14823; decide +kernel
    rw [ha]
    exact (canonical14823 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA900 + difference 2 4) (sourceB900 + difference 4 2) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA900 + difference 2 4) (sourceB900 + difference 4 2) sourceC900) = raw14824 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14824; decide +kernel
    rw [ha]
    exact (canonical14824 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA900 + difference 2 5) (sourceB900 + difference 5 2) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA900 + difference 2 5) (sourceB900 + difference 5 2) sourceC900) = raw14825 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14825; decide +kernel
    rw [ha]
    exact (canonical14825 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA900 + difference 3 0) (sourceB900 + difference 0 3) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA900 + difference 3 0) (sourceB900 + difference 0 3) sourceC900) = raw14099 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14099; decide +kernel
    rw [ha]
    exact (canonical14099 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA900 + difference 3 1) (sourceB900 + difference 1 3) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA900 + difference 3 1) (sourceB900 + difference 1 3) sourceC900) = raw14826 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14826; decide +kernel
    rw [ha]
    exact (canonical14826 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA900 + difference 3 2) (sourceB900 + difference 2 3) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA900 + difference 3 2) (sourceB900 + difference 2 3) sourceC900) = raw14827 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14827; decide +kernel
    rw [ha]
    exact (canonical14827 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA900 + difference 3 4) (sourceB900 + difference 4 3) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA900 + difference 3 4) (sourceB900 + difference 4 3) sourceC900) = raw14828 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14828; decide +kernel
    rw [ha]
    exact (canonical14828 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA900 + difference 3 5) (sourceB900 + difference 5 3) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA900 + difference 3 5) (sourceB900 + difference 5 3) sourceC900) = raw14073 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14073; decide +kernel
    rw [ha]
    exact (canonical14073 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA900 + difference 4 0) (sourceB900 + difference 0 4) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5131) := by
    have ha : (tripleCharges (sourceA900 + difference 4 0) (sourceB900 + difference 0 4) sourceC900) = raw14829 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14829; decide +kernel
    rw [ha]
    exact (canonical14829 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA900 + difference 4 1) (sourceB900 + difference 1 4) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5342) := by
    have ha : (tripleCharges (sourceA900 + difference 4 1) (sourceB900 + difference 1 4) sourceC900) = raw14830 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14830; decide +kernel
    rw [ha]
    exact (canonical14830 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA900 + difference 4 2) (sourceB900 + difference 2 4) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA900 + difference 4 2) (sourceB900 + difference 2 4) sourceC900) = raw14831 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14831; decide +kernel
    rw [ha]
    exact (canonical14831 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA900 + difference 4 3) (sourceB900 + difference 3 4) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5154) := by
    have ha : (tripleCharges (sourceA900 + difference 4 3) (sourceB900 + difference 3 4) sourceC900) = raw14832 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14832; decide +kernel
    rw [ha]
    exact (canonical14832 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA900 + difference 4 5) (sourceB900 + difference 5 4) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA900 + difference 4 5) (sourceB900 + difference 5 4) sourceC900) = raw14833 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14833; decide +kernel
    rw [ha]
    exact (canonical14833 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA900 + difference 5 0) (sourceB900 + difference 0 5) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4783) := by
    have ha : (tripleCharges (sourceA900 + difference 5 0) (sourceB900 + difference 0 5) sourceC900) = raw14834 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14834; decide +kernel
    rw [ha]
    exact (canonical14834 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA900 + difference 5 1) (sourceB900 + difference 1 5) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4784) := by
    have ha : (tripleCharges (sourceA900 + difference 5 1) (sourceB900 + difference 1 5) sourceC900) = raw14835 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14835; decide +kernel
    rw [ha]
    exact (canonical14835 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA900 + difference 5 2) (sourceB900 + difference 2 5) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA900 + difference 5 2) (sourceB900 + difference 2 5) sourceC900) = raw14836 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14836; decide +kernel
    rw [ha]
    exact (canonical14836 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA900 + difference 5 3) (sourceB900 + difference 3 5) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4783) := by
    have ha : (tripleCharges (sourceA900 + difference 5 3) (sourceB900 + difference 3 5) sourceC900) = raw14837 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14837; decide +kernel
    rw [ha]
    exact (canonical14837 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA900 + difference 5 4) (sourceB900 + difference 4 5) sourceC900) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA900 + difference 5 4) (sourceB900 + difference 4 5) sourceC900) = raw14838 := by
      apply Matrix.ext; unfold tripleCharges sourceA900 sourceB900 sourceC900 difference raw14838; decide +kernel
    rw [ha]
    exact (canonical14838 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA900 sourceB900 sourceC900
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm900, Integer.Sparse.eval]
  linarith only [hs]

def sourceA901 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB901 : Charge := ![0, 1, -1, 2, 0, -2]
def sourceC901 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceForm901 : Integer.Sparse Master := [(Sum.inr 1992, 1), (Sum.inr 1993, 1), (Sum.inr 2001, 1), (Sum.inr 2034, 1), (Sum.inr 2196, 1), (Sum.inr 2905, 1), (Sum.inr 2907, 1), (Sum.inr 2933, 1), (Sum.inr 3038, 1), (Sum.inr 3517, 1), (Sum.inr 3518, 1), (Sum.inr 3541, 1), (Sum.inr 3561, 1), (Sum.inr 3679, 1), (Sum.inr 3698, 1), (Sum.inr 3712, 1), (Sum.inr 3723, 1), (Sum.inr 3762, 1), (Sum.inr 3796, 1), (Sum.inr 3814, 1), (Sum.inr 3830, 1), (Sum.inr 3834, 1), (Sum.inr 3838, 1), (Sum.inr 3839, 1), (Sum.inr 3840, 1), (Sum.inr 3853, 1), (Sum.inr 3856, 1), (Sum.inr 3872, 2), (Sum.inr 3990, 1)]

theorem sourceEq901 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm901 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA901 + difference 0 1) (sourceB901 + difference 1 0) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA901 + difference 0 1) (sourceB901 + difference 1 0) sourceC901) = raw14839 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14839; decide +kernel
    rw [ha]
    exact (canonical14839 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA901 + difference 0 2) (sourceB901 + difference 2 0) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA901 + difference 0 2) (sourceB901 + difference 2 0) sourceC901) = raw14840 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14840; decide +kernel
    rw [ha]
    exact (canonical14840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA901 + difference 0 3) (sourceB901 + difference 3 0) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA901 + difference 0 3) (sourceB901 + difference 3 0) sourceC901) = raw14841 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14841; decide +kernel
    rw [ha]
    exact (canonical14841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA901 + difference 0 4) (sourceB901 + difference 4 0) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA901 + difference 0 4) (sourceB901 + difference 4 0) sourceC901) = raw14842 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14842; decide +kernel
    rw [ha]
    exact (canonical14842 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA901 + difference 0 5) (sourceB901 + difference 5 0) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA901 + difference 0 5) (sourceB901 + difference 5 0) sourceC901) = raw14843 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14843; decide +kernel
    rw [ha]
    exact (canonical14843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA901 + difference 1 0) (sourceB901 + difference 0 1) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA901 + difference 1 0) (sourceB901 + difference 0 1) sourceC901) = raw14844 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14844; decide +kernel
    rw [ha]
    exact (canonical14844 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA901 + difference 1 2) (sourceB901 + difference 2 1) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA901 + difference 1 2) (sourceB901 + difference 2 1) sourceC901) = raw14845 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14845; decide +kernel
    rw [ha]
    exact (canonical14845 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA901 + difference 1 3) (sourceB901 + difference 3 1) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA901 + difference 1 3) (sourceB901 + difference 3 1) sourceC901) = raw14846 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14846; decide +kernel
    rw [ha]
    exact (canonical14846 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA901 + difference 1 4) (sourceB901 + difference 4 1) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA901 + difference 1 4) (sourceB901 + difference 4 1) sourceC901) = raw14847 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14847; decide +kernel
    rw [ha]
    exact (canonical14847 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA901 + difference 1 5) (sourceB901 + difference 5 1) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA901 + difference 1 5) (sourceB901 + difference 5 1) sourceC901) = raw14848 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14848; decide +kernel
    rw [ha]
    exact (canonical14848 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA901 + difference 2 0) (sourceB901 + difference 0 2) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2907) := by
    have ha : (tripleCharges (sourceA901 + difference 2 0) (sourceB901 + difference 0 2) sourceC901) = raw14849 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14849; decide +kernel
    rw [ha]
    exact (canonical14849 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA901 + difference 2 1) (sourceB901 + difference 1 2) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3712) := by
    have ha : (tripleCharges (sourceA901 + difference 2 1) (sourceB901 + difference 1 2) sourceC901) = raw14850 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14850; decide +kernel
    rw [ha]
    exact (canonical14850 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA901 + difference 2 3) (sourceB901 + difference 3 2) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3518) := by
    have ha : (tripleCharges (sourceA901 + difference 2 3) (sourceB901 + difference 3 2) sourceC901) = raw14851 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14851; decide +kernel
    rw [ha]
    exact (canonical14851 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA901 + difference 2 4) (sourceB901 + difference 4 2) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA901 + difference 2 4) (sourceB901 + difference 4 2) sourceC901) = raw14852 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14852; decide +kernel
    rw [ha]
    exact (canonical14852 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA901 + difference 2 5) (sourceB901 + difference 5 2) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA901 + difference 2 5) (sourceB901 + difference 5 2) sourceC901) = raw14853 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14853; decide +kernel
    rw [ha]
    exact (canonical14853 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA901 + difference 3 0) (sourceB901 + difference 0 3) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA901 + difference 3 0) (sourceB901 + difference 0 3) sourceC901) = raw14854 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14854; decide +kernel
    rw [ha]
    exact (canonical14854 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA901 + difference 3 1) (sourceB901 + difference 1 3) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA901 + difference 3 1) (sourceB901 + difference 1 3) sourceC901) = raw14855 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14855; decide +kernel
    rw [ha]
    exact (canonical14855 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA901 + difference 3 2) (sourceB901 + difference 2 3) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3830) := by
    have ha : (tripleCharges (sourceA901 + difference 3 2) (sourceB901 + difference 2 3) sourceC901) = raw14856 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14856; decide +kernel
    rw [ha]
    exact (canonical14856 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA901 + difference 3 4) (sourceB901 + difference 4 3) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA901 + difference 3 4) (sourceB901 + difference 4 3) sourceC901) = raw14857 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14857; decide +kernel
    rw [ha]
    exact (canonical14857 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA901 + difference 3 5) (sourceB901 + difference 5 3) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA901 + difference 3 5) (sourceB901 + difference 5 3) sourceC901) = raw14858 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14858; decide +kernel
    rw [ha]
    exact (canonical14858 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA901 + difference 4 0) (sourceB901 + difference 0 4) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2905) := by
    have ha : (tripleCharges (sourceA901 + difference 4 0) (sourceB901 + difference 0 4) sourceC901) = raw14859 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14859; decide +kernel
    rw [ha]
    exact (canonical14859 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA901 + difference 4 1) (sourceB901 + difference 1 4) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3679) := by
    have ha : (tripleCharges (sourceA901 + difference 4 1) (sourceB901 + difference 1 4) sourceC901) = raw14860 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14860; decide +kernel
    rw [ha]
    exact (canonical14860 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA901 + difference 4 2) (sourceB901 + difference 2 4) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA901 + difference 4 2) (sourceB901 + difference 2 4) sourceC901) = raw14861 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14861; decide +kernel
    rw [ha]
    exact (canonical14861 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA901 + difference 4 3) (sourceB901 + difference 3 4) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3561) := by
    have ha : (tripleCharges (sourceA901 + difference 4 3) (sourceB901 + difference 3 4) sourceC901) = raw14862 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14862; decide +kernel
    rw [ha]
    exact (canonical14862 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA901 + difference 4 5) (sourceB901 + difference 5 4) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA901 + difference 4 5) (sourceB901 + difference 5 4) sourceC901) = raw14863 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14863; decide +kernel
    rw [ha]
    exact (canonical14863 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA901 + difference 5 0) (sourceB901 + difference 0 5) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1992) := by
    have ha : (tripleCharges (sourceA901 + difference 5 0) (sourceB901 + difference 0 5) sourceC901) = raw14864 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14864; decide +kernel
    rw [ha]
    exact (canonical14864 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA901 + difference 5 1) (sourceB901 + difference 1 5) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1993) := by
    have ha : (tripleCharges (sourceA901 + difference 5 1) (sourceB901 + difference 1 5) sourceC901) = raw14865 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14865; decide +kernel
    rw [ha]
    exact (canonical14865 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA901 + difference 5 2) (sourceB901 + difference 2 5) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA901 + difference 5 2) (sourceB901 + difference 2 5) sourceC901) = raw14866 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14866; decide +kernel
    rw [ha]
    exact (canonical14866 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA901 + difference 5 3) (sourceB901 + difference 3 5) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2001) := by
    have ha : (tripleCharges (sourceA901 + difference 5 3) (sourceB901 + difference 3 5) sourceC901) = raw14867 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14867; decide +kernel
    rw [ha]
    exact (canonical14867 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA901 + difference 5 4) (sourceB901 + difference 4 5) sourceC901) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA901 + difference 5 4) (sourceB901 + difference 4 5) sourceC901) = raw14868 := by
      apply Matrix.ext; unfold tripleCharges sourceA901 sourceB901 sourceC901 difference raw14868; decide +kernel
    rw [ha]
    exact (canonical14868 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA901 sourceB901 sourceC901
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm901, Integer.Sparse.eval]
  linarith only [hs]

def sourceA902 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB902 : Charge := ![0, 1, -1, 2, 0, -2]
def sourceC902 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceForm902 : Integer.Sparse Master := [(Sum.inr 3194, 1), (Sum.inr 3717, 2), (Sum.inr 3722, 2), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

theorem sourceEq902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm902 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA902 + difference 0 1) (sourceB902 + difference 1 0) sourceC902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA902 + difference 0 1) (sourceB902 + difference 1 0) sourceC902) = raw14869 := by
      apply Matrix.ext; unfold tripleCharges sourceA902 sourceB902 sourceC902 difference raw14869; decide +kernel
    rw [ha]
    exact (canonical14869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA902 + difference 1 1) (sourceB902 + difference 1 1) sourceC902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA902 + difference 1 1) (sourceB902 + difference 1 1) sourceC902) = raw14870 := by
      apply Matrix.ext; unfold tripleCharges sourceA902 sourceB902 sourceC902 difference raw14870; decide +kernel
    rw [ha]
    exact (canonical14870 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA902 + difference 2 1) (sourceB902 + difference 1 2) sourceC902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3717) := by
    have ha : (tripleCharges (sourceA902 + difference 2 1) (sourceB902 + difference 1 2) sourceC902) = raw14871 := by
      apply Matrix.ext; unfold tripleCharges sourceA902 sourceB902 sourceC902 difference raw14871; decide +kernel
    rw [ha]
    exact (canonical14871 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA902 + difference 3 1) (sourceB902 + difference 1 3) sourceC902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA902 + difference 3 1) (sourceB902 + difference 1 3) sourceC902) = raw14872 := by
      apply Matrix.ext; unfold tripleCharges sourceA902 sourceB902 sourceC902 difference raw14872; decide +kernel
    rw [ha]
    exact (canonical14872 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA902 + difference 4 1) (sourceB902 + difference 1 4) sourceC902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3717) := by
    have ha : (tripleCharges (sourceA902 + difference 4 1) (sourceB902 + difference 1 4) sourceC902) = raw14873 := by
      apply Matrix.ext; unfold tripleCharges sourceA902 sourceB902 sourceC902 difference raw14873; decide +kernel
    rw [ha]
    exact (canonical14873 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA902 + difference 5 1) (sourceB902 + difference 1 5) sourceC902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3194) := by
    have ha : (tripleCharges (sourceA902 + difference 5 1) (sourceB902 + difference 1 5) sourceC902) = raw14874 := by
      apply Matrix.ext; unfold tripleCharges sourceA902 sourceB902 sourceC902 difference raw14874; decide +kernel
    rw [ha]
    exact (canonical14874 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA902 + sourceB902) sourceC902) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA902 + sourceB902) sourceC902) = raw14875 := by
      apply Matrix.ext; unfold doubleCharges sourceA902 sourceB902 sourceC902 raw14875; decide +kernel
    rw [ha]
    exact (canonical14875 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA902 sourceB902 sourceC902
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm902, Integer.Sparse.eval]
  linarith only [hs]

def sourceA903 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB903 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC903 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm903 : Integer.Sparse Master := [(Sum.inr 4869, 2), (Sum.inr 4871, 1), (Sum.inr 4874, 1), (Sum.inr 4898, 1), (Sum.inr 5170, 2), (Sum.inr 5176, 1), (Sum.inr 5310, 1), (Sum.inr 5384, 2), (Sum.inr 5387, 2), (Sum.inr 5389, 1), (Sum.inr 5403, 2), (Sum.inr 5412, 2), (Sum.inr 5439, 2), (Sum.inr 5441, 1), (Sum.inr 5443, 3), (Sum.inr 5448, 2), (Sum.inr 5449, 1), (Sum.inr 5455, 1), (Sum.inr 5456, 1), (Sum.inr 5491, 1)]

theorem sourceEq903 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm903 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA903 + difference 0 1) (sourceB903 + difference 1 0) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA903 + difference 0 1) (sourceB903 + difference 1 0) sourceC903) = raw14876 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14876; decide +kernel
    rw [ha]
    exact (canonical14876 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA903 + difference 0 2) (sourceB903 + difference 2 0) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA903 + difference 0 2) (sourceB903 + difference 2 0) sourceC903) = raw14877 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14877; decide +kernel
    rw [ha]
    exact (canonical14877 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA903 + difference 0 3) (sourceB903 + difference 3 0) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA903 + difference 0 3) (sourceB903 + difference 3 0) sourceC903) = raw14878 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14878; decide +kernel
    rw [ha]
    exact (canonical14878 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA903 + difference 0 4) (sourceB903 + difference 4 0) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA903 + difference 0 4) (sourceB903 + difference 4 0) sourceC903) = raw2631 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw2631; decide +kernel
    rw [ha]
    exact (canonical2631 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA903 + difference 0 5) (sourceB903 + difference 5 0) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA903 + difference 0 5) (sourceB903 + difference 5 0) sourceC903) = raw14879 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14879; decide +kernel
    rw [ha]
    exact (canonical14879 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA903 + difference 1 0) (sourceB903 + difference 0 1) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA903 + difference 1 0) (sourceB903 + difference 0 1) sourceC903) = raw2651 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw2651; decide +kernel
    rw [ha]
    exact (canonical2651 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA903 + difference 1 2) (sourceB903 + difference 2 1) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA903 + difference 1 2) (sourceB903 + difference 2 1) sourceC903) = raw2653 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw2653; decide +kernel
    rw [ha]
    exact (canonical2653 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA903 + difference 1 3) (sourceB903 + difference 3 1) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA903 + difference 1 3) (sourceB903 + difference 3 1) sourceC903) = raw2654 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw2654; decide +kernel
    rw [ha]
    exact (canonical2654 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA903 + difference 1 4) (sourceB903 + difference 4 1) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA903 + difference 1 4) (sourceB903 + difference 4 1) sourceC903) = raw4379 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw4379; decide +kernel
    rw [ha]
    exact (canonical4379 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA903 + difference 1 5) (sourceB903 + difference 5 1) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA903 + difference 1 5) (sourceB903 + difference 5 1) sourceC903) = raw2655 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw2655; decide +kernel
    rw [ha]
    exact (canonical2655 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA903 + difference 2 0) (sourceB903 + difference 0 2) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA903 + difference 2 0) (sourceB903 + difference 0 2) sourceC903) = raw7563 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw7563; decide +kernel
    rw [ha]
    exact (canonical7563 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA903 + difference 2 1) (sourceB903 + difference 1 2) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA903 + difference 2 1) (sourceB903 + difference 1 2) sourceC903) = raw14880 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14880; decide +kernel
    rw [ha]
    exact (canonical14880 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA903 + difference 2 3) (sourceB903 + difference 3 2) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA903 + difference 2 3) (sourceB903 + difference 3 2) sourceC903) = raw14881 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14881; decide +kernel
    rw [ha]
    exact (canonical14881 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA903 + difference 2 4) (sourceB903 + difference 4 2) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA903 + difference 2 4) (sourceB903 + difference 4 2) sourceC903) = raw2642 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw2642; decide +kernel
    rw [ha]
    exact (canonical2642 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA903 + difference 2 5) (sourceB903 + difference 5 2) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA903 + difference 2 5) (sourceB903 + difference 5 2) sourceC903) = raw14882 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14882; decide +kernel
    rw [ha]
    exact (canonical14882 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA903 + difference 3 0) (sourceB903 + difference 0 3) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA903 + difference 3 0) (sourceB903 + difference 0 3) sourceC903) = raw7567 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw7567; decide +kernel
    rw [ha]
    exact (canonical7567 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA903 + difference 3 1) (sourceB903 + difference 1 3) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA903 + difference 3 1) (sourceB903 + difference 1 3) sourceC903) = raw14883 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14883; decide +kernel
    rw [ha]
    exact (canonical14883 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA903 + difference 3 2) (sourceB903 + difference 2 3) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA903 + difference 3 2) (sourceB903 + difference 2 3) sourceC903) = raw14884 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14884; decide +kernel
    rw [ha]
    exact (canonical14884 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA903 + difference 3 4) (sourceB903 + difference 4 3) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA903 + difference 3 4) (sourceB903 + difference 4 3) sourceC903) = raw2647 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw2647; decide +kernel
    rw [ha]
    exact (canonical2647 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA903 + difference 3 5) (sourceB903 + difference 5 3) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA903 + difference 3 5) (sourceB903 + difference 5 3) sourceC903) = raw14885 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14885; decide +kernel
    rw [ha]
    exact (canonical14885 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA903 + difference 4 0) (sourceB903 + difference 0 4) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA903 + difference 4 0) (sourceB903 + difference 0 4) sourceC903) = raw7571 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw7571; decide +kernel
    rw [ha]
    exact (canonical7571 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA903 + difference 4 1) (sourceB903 + difference 1 4) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA903 + difference 4 1) (sourceB903 + difference 1 4) sourceC903) = raw14886 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14886; decide +kernel
    rw [ha]
    exact (canonical14886 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA903 + difference 4 2) (sourceB903 + difference 2 4) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA903 + difference 4 2) (sourceB903 + difference 2 4) sourceC903) = raw14887 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14887; decide +kernel
    rw [ha]
    exact (canonical14887 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA903 + difference 4 3) (sourceB903 + difference 3 4) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA903 + difference 4 3) (sourceB903 + difference 3 4) sourceC903) = raw14888 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14888; decide +kernel
    rw [ha]
    exact (canonical14888 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA903 + difference 4 5) (sourceB903 + difference 5 4) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA903 + difference 4 5) (sourceB903 + difference 5 4) sourceC903) = raw14889 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14889; decide +kernel
    rw [ha]
    exact (canonical14889 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA903 + difference 5 0) (sourceB903 + difference 0 5) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA903 + difference 5 0) (sourceB903 + difference 0 5) sourceC903) = raw4393 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw4393; decide +kernel
    rw [ha]
    exact (canonical4393 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA903 + difference 5 1) (sourceB903 + difference 1 5) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA903 + difference 5 1) (sourceB903 + difference 1 5) sourceC903) = raw14890 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14890; decide +kernel
    rw [ha]
    exact (canonical14890 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA903 + difference 5 2) (sourceB903 + difference 2 5) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA903 + difference 5 2) (sourceB903 + difference 2 5) sourceC903) = raw14891 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14891; decide +kernel
    rw [ha]
    exact (canonical14891 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA903 + difference 5 3) (sourceB903 + difference 3 5) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA903 + difference 5 3) (sourceB903 + difference 3 5) sourceC903) = raw14892 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw14892; decide +kernel
    rw [ha]
    exact (canonical14892 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA903 + difference 5 4) (sourceB903 + difference 4 5) sourceC903) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA903 + difference 5 4) (sourceB903 + difference 4 5) sourceC903) = raw2657 := by
      apply Matrix.ext; unfold tripleCharges sourceA903 sourceB903 sourceC903 difference raw2657; decide +kernel
    rw [ha]
    exact (canonical2657 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA903 sourceB903 sourceC903
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm903, Integer.Sparse.eval]
  linarith only [hs]

def sourceA904 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB904 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC904 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm904 : Integer.Sparse Master := [(Sum.inr 2110, 2), (Sum.inr 2112, 1), (Sum.inr 2115, 1), (Sum.inr 2279, 1), (Sum.inr 2954, 2), (Sum.inr 2968, 1), (Sum.inr 3121, 1), (Sum.inr 3732, 2), (Sum.inr 3739, 2), (Sum.inr 3740, 1), (Sum.inr 3789, 2), (Sum.inr 3814, 2), (Sum.inr 3885, 2), (Sum.inr 3886, 1), (Sum.inr 3889, 2), (Sum.inr 3907, 1), (Sum.inr 3916, 1), (Sum.inr 4012, 2), (Sum.inr 4014, 1), (Sum.inr 4019, 1), (Sum.inr 4037, 1)]

theorem sourceEq904 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm904 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA904 + difference 0 1) (sourceB904 + difference 1 0) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA904 + difference 0 1) (sourceB904 + difference 1 0) sourceC904) = raw14893 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14893; decide +kernel
    rw [ha]
    exact (canonical14893 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA904 + difference 0 2) (sourceB904 + difference 2 0) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA904 + difference 0 2) (sourceB904 + difference 2 0) sourceC904) = raw14894 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14894; decide +kernel
    rw [ha]
    exact (canonical14894 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA904 + difference 0 3) (sourceB904 + difference 3 0) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA904 + difference 0 3) (sourceB904 + difference 3 0) sourceC904) = raw14895 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14895; decide +kernel
    rw [ha]
    exact (canonical14895 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA904 + difference 0 4) (sourceB904 + difference 4 0) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA904 + difference 0 4) (sourceB904 + difference 4 0) sourceC904) = raw14896 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14896; decide +kernel
    rw [ha]
    exact (canonical14896 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA904 + difference 0 5) (sourceB904 + difference 5 0) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4014) := by
    have ha : (tripleCharges (sourceA904 + difference 0 5) (sourceB904 + difference 5 0) sourceC904) = raw14897 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14897; decide +kernel
    rw [ha]
    exact (canonical14897 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA904 + difference 1 0) (sourceB904 + difference 0 1) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA904 + difference 1 0) (sourceB904 + difference 0 1) sourceC904) = raw4425 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw4425; decide +kernel
    rw [ha]
    exact (canonical4425 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA904 + difference 1 2) (sourceB904 + difference 2 1) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA904 + difference 1 2) (sourceB904 + difference 2 1) sourceC904) = raw7576 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw7576; decide +kernel
    rw [ha]
    exact (canonical7576 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA904 + difference 1 3) (sourceB904 + difference 3 1) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA904 + difference 1 3) (sourceB904 + difference 3 1) sourceC904) = raw7577 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw7577; decide +kernel
    rw [ha]
    exact (canonical7577 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA904 + difference 1 4) (sourceB904 + difference 4 1) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3916) := by
    have ha : (tripleCharges (sourceA904 + difference 1 4) (sourceB904 + difference 4 1) sourceC904) = raw4405 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw4405; decide +kernel
    rw [ha]
    exact (canonical4405 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA904 + difference 1 5) (sourceB904 + difference 5 1) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA904 + difference 1 5) (sourceB904 + difference 5 1) sourceC904) = raw7578 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw7578; decide +kernel
    rw [ha]
    exact (canonical7578 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA904 + difference 2 0) (sourceB904 + difference 0 2) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA904 + difference 2 0) (sourceB904 + difference 0 2) sourceC904) = raw7584 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw7584; decide +kernel
    rw [ha]
    exact (canonical7584 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA904 + difference 2 1) (sourceB904 + difference 1 2) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA904 + difference 2 1) (sourceB904 + difference 1 2) sourceC904) = raw14898 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14898; decide +kernel
    rw [ha]
    exact (canonical14898 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA904 + difference 2 3) (sourceB904 + difference 3 2) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA904 + difference 2 3) (sourceB904 + difference 3 2) sourceC904) = raw14899 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14899; decide +kernel
    rw [ha]
    exact (canonical14899 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA904 + difference 2 4) (sourceB904 + difference 4 2) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA904 + difference 2 4) (sourceB904 + difference 4 2) sourceC904) = raw14900 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14900; decide +kernel
    rw [ha]
    exact (canonical14900 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA904 + difference 2 5) (sourceB904 + difference 5 2) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA904 + difference 2 5) (sourceB904 + difference 5 2) sourceC904) = raw14901 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14901; decide +kernel
    rw [ha]
    exact (canonical14901 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA904 + difference 3 0) (sourceB904 + difference 0 3) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA904 + difference 3 0) (sourceB904 + difference 0 3) sourceC904) = raw7588 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw7588; decide +kernel
    rw [ha]
    exact (canonical7588 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA904 + difference 3 1) (sourceB904 + difference 1 3) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA904 + difference 3 1) (sourceB904 + difference 1 3) sourceC904) = raw14902 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14902; decide +kernel
    rw [ha]
    exact (canonical14902 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA904 + difference 3 2) (sourceB904 + difference 2 3) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA904 + difference 3 2) (sourceB904 + difference 2 3) sourceC904) = raw14903 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14903; decide +kernel
    rw [ha]
    exact (canonical14903 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA904 + difference 3 4) (sourceB904 + difference 4 3) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA904 + difference 3 4) (sourceB904 + difference 4 3) sourceC904) = raw14904 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14904; decide +kernel
    rw [ha]
    exact (canonical14904 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA904 + difference 3 5) (sourceB904 + difference 5 3) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA904 + difference 3 5) (sourceB904 + difference 5 3) sourceC904) = raw14905 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14905; decide +kernel
    rw [ha]
    exact (canonical14905 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA904 + difference 4 0) (sourceB904 + difference 0 4) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA904 + difference 4 0) (sourceB904 + difference 0 4) sourceC904) = raw7592 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw7592; decide +kernel
    rw [ha]
    exact (canonical7592 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA904 + difference 4 1) (sourceB904 + difference 1 4) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3740) := by
    have ha : (tripleCharges (sourceA904 + difference 4 1) (sourceB904 + difference 1 4) sourceC904) = raw14906 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14906; decide +kernel
    rw [ha]
    exact (canonical14906 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA904 + difference 4 2) (sourceB904 + difference 2 4) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3739) := by
    have ha : (tripleCharges (sourceA904 + difference 4 2) (sourceB904 + difference 2 4) sourceC904) = raw14907 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14907; decide +kernel
    rw [ha]
    exact (canonical14907 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA904 + difference 4 3) (sourceB904 + difference 3 4) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3739) := by
    have ha : (tripleCharges (sourceA904 + difference 4 3) (sourceB904 + difference 3 4) sourceC904) = raw14908 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14908; decide +kernel
    rw [ha]
    exact (canonical14908 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA904 + difference 4 5) (sourceB904 + difference 5 4) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4037) := by
    have ha : (tripleCharges (sourceA904 + difference 4 5) (sourceB904 + difference 5 4) sourceC904) = raw14909 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14909; decide +kernel
    rw [ha]
    exact (canonical14909 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA904 + difference 5 0) (sourceB904 + difference 0 5) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA904 + difference 5 0) (sourceB904 + difference 0 5) sourceC904) = raw4422 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw4422; decide +kernel
    rw [ha]
    exact (canonical4422 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA904 + difference 5 1) (sourceB904 + difference 1 5) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA904 + difference 5 1) (sourceB904 + difference 1 5) sourceC904) = raw14910 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14910; decide +kernel
    rw [ha]
    exact (canonical14910 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA904 + difference 5 2) (sourceB904 + difference 2 5) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA904 + difference 5 2) (sourceB904 + difference 2 5) sourceC904) = raw14911 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14911; decide +kernel
    rw [ha]
    exact (canonical14911 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA904 + difference 5 3) (sourceB904 + difference 3 5) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA904 + difference 5 3) (sourceB904 + difference 3 5) sourceC904) = raw14912 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw14912; decide +kernel
    rw [ha]
    exact (canonical14912 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA904 + difference 5 4) (sourceB904 + difference 4 5) sourceC904) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA904 + difference 5 4) (sourceB904 + difference 4 5) sourceC904) = raw4401 := by
      apply Matrix.ext; unfold tripleCharges sourceA904 sourceB904 sourceC904 difference raw4401; decide +kernel
    rw [ha]
    exact (canonical4401 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA904 sourceB904 sourceC904
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm904, Integer.Sparse.eval]
  linarith only [hs]

def sourceA905 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB905 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC905 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceForm905 : Integer.Sparse Master := [(Sum.inr 4839, 2), (Sum.inr 4843, 1), (Sum.inr 4845, 1), (Sum.inr 4896, 1), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5370, 2), (Sum.inr 5397, 2), (Sum.inr 5411, 2), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5450, 2), (Sum.inr 5451, 2), (Sum.inr 5453, 1), (Sum.inr 5454, 1), (Sum.inr 5492, 1)]

theorem sourceEq905 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm905 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA905 + difference 0 1) (sourceB905 + difference 1 0) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA905 + difference 0 1) (sourceB905 + difference 1 0) sourceC905) = raw14913 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14913; decide +kernel
    rw [ha]
    exact (canonical14913 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA905 + difference 0 2) (sourceB905 + difference 2 0) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA905 + difference 0 2) (sourceB905 + difference 2 0) sourceC905) = raw14914 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14914; decide +kernel
    rw [ha]
    exact (canonical14914 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA905 + difference 0 3) (sourceB905 + difference 3 0) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA905 + difference 0 3) (sourceB905 + difference 3 0) sourceC905) = raw14915 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14915; decide +kernel
    rw [ha]
    exact (canonical14915 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA905 + difference 0 4) (sourceB905 + difference 4 0) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA905 + difference 0 4) (sourceB905 + difference 4 0) sourceC905) = raw14916 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14916; decide +kernel
    rw [ha]
    exact (canonical14916 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA905 + difference 0 5) (sourceB905 + difference 5 0) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA905 + difference 0 5) (sourceB905 + difference 5 0) sourceC905) = raw14917 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14917; decide +kernel
    rw [ha]
    exact (canonical14917 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA905 + difference 1 0) (sourceB905 + difference 0 1) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA905 + difference 1 0) (sourceB905 + difference 0 1) sourceC905) = raw14918 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14918; decide +kernel
    rw [ha]
    exact (canonical14918 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA905 + difference 1 2) (sourceB905 + difference 2 1) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA905 + difference 1 2) (sourceB905 + difference 2 1) sourceC905) = raw14919 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14919; decide +kernel
    rw [ha]
    exact (canonical14919 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA905 + difference 1 3) (sourceB905 + difference 3 1) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA905 + difference 1 3) (sourceB905 + difference 3 1) sourceC905) = raw14920 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14920; decide +kernel
    rw [ha]
    exact (canonical14920 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA905 + difference 1 4) (sourceB905 + difference 4 1) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA905 + difference 1 4) (sourceB905 + difference 4 1) sourceC905) = raw14921 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14921; decide +kernel
    rw [ha]
    exact (canonical14921 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA905 + difference 1 5) (sourceB905 + difference 5 1) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA905 + difference 1 5) (sourceB905 + difference 5 1) sourceC905) = raw14922 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14922; decide +kernel
    rw [ha]
    exact (canonical14922 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA905 + difference 2 0) (sourceB905 + difference 0 2) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA905 + difference 2 0) (sourceB905 + difference 0 2) sourceC905) = raw14923 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14923; decide +kernel
    rw [ha]
    exact (canonical14923 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA905 + difference 2 1) (sourceB905 + difference 1 2) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA905 + difference 2 1) (sourceB905 + difference 1 2) sourceC905) = raw14924 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14924; decide +kernel
    rw [ha]
    exact (canonical14924 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA905 + difference 2 3) (sourceB905 + difference 3 2) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA905 + difference 2 3) (sourceB905 + difference 3 2) sourceC905) = raw14925 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14925; decide +kernel
    rw [ha]
    exact (canonical14925 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA905 + difference 2 4) (sourceB905 + difference 4 2) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA905 + difference 2 4) (sourceB905 + difference 4 2) sourceC905) = raw14926 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14926; decide +kernel
    rw [ha]
    exact (canonical14926 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA905 + difference 2 5) (sourceB905 + difference 5 2) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA905 + difference 2 5) (sourceB905 + difference 5 2) sourceC905) = raw14927 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14927; decide +kernel
    rw [ha]
    exact (canonical14927 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA905 + difference 3 0) (sourceB905 + difference 0 3) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA905 + difference 3 0) (sourceB905 + difference 0 3) sourceC905) = raw14928 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14928; decide +kernel
    rw [ha]
    exact (canonical14928 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA905 + difference 3 1) (sourceB905 + difference 1 3) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA905 + difference 3 1) (sourceB905 + difference 1 3) sourceC905) = raw14929 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14929; decide +kernel
    rw [ha]
    exact (canonical14929 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA905 + difference 3 2) (sourceB905 + difference 2 3) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA905 + difference 3 2) (sourceB905 + difference 2 3) sourceC905) = raw14930 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14930; decide +kernel
    rw [ha]
    exact (canonical14930 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA905 + difference 3 4) (sourceB905 + difference 4 3) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA905 + difference 3 4) (sourceB905 + difference 4 3) sourceC905) = raw14931 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14931; decide +kernel
    rw [ha]
    exact (canonical14931 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA905 + difference 3 5) (sourceB905 + difference 5 3) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA905 + difference 3 5) (sourceB905 + difference 5 3) sourceC905) = raw14932 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14932; decide +kernel
    rw [ha]
    exact (canonical14932 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA905 + difference 4 0) (sourceB905 + difference 0 4) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA905 + difference 4 0) (sourceB905 + difference 0 4) sourceC905) = raw14933 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14933; decide +kernel
    rw [ha]
    exact (canonical14933 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA905 + difference 4 1) (sourceB905 + difference 1 4) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA905 + difference 4 1) (sourceB905 + difference 1 4) sourceC905) = raw14934 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14934; decide +kernel
    rw [ha]
    exact (canonical14934 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA905 + difference 4 2) (sourceB905 + difference 2 4) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA905 + difference 4 2) (sourceB905 + difference 2 4) sourceC905) = raw14935 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14935; decide +kernel
    rw [ha]
    exact (canonical14935 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA905 + difference 4 3) (sourceB905 + difference 3 4) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA905 + difference 4 3) (sourceB905 + difference 3 4) sourceC905) = raw14936 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14936; decide +kernel
    rw [ha]
    exact (canonical14936 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA905 + difference 4 5) (sourceB905 + difference 5 4) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA905 + difference 4 5) (sourceB905 + difference 5 4) sourceC905) = raw14937 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14937; decide +kernel
    rw [ha]
    exact (canonical14937 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA905 + difference 5 0) (sourceB905 + difference 0 5) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA905 + difference 5 0) (sourceB905 + difference 0 5) sourceC905) = raw14938 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14938; decide +kernel
    rw [ha]
    exact (canonical14938 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA905 + difference 5 1) (sourceB905 + difference 1 5) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA905 + difference 5 1) (sourceB905 + difference 1 5) sourceC905) = raw14939 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14939; decide +kernel
    rw [ha]
    exact (canonical14939 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA905 + difference 5 2) (sourceB905 + difference 2 5) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA905 + difference 5 2) (sourceB905 + difference 2 5) sourceC905) = raw14940 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14940; decide +kernel
    rw [ha]
    exact (canonical14940 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA905 + difference 5 3) (sourceB905 + difference 3 5) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA905 + difference 5 3) (sourceB905 + difference 3 5) sourceC905) = raw14941 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14941; decide +kernel
    rw [ha]
    exact (canonical14941 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA905 + difference 5 4) (sourceB905 + difference 4 5) sourceC905) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA905 + difference 5 4) (sourceB905 + difference 4 5) sourceC905) = raw14942 := by
      apply Matrix.ext; unfold tripleCharges sourceA905 sourceB905 sourceC905 difference raw14942; decide +kernel
    rw [ha]
    exact (canonical14942 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA905 sourceB905 sourceC905
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm905, Integer.Sparse.eval]
  linarith only [hs]

def sourceA906 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB906 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC906 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceForm906 : Integer.Sparse Master := [(Sum.inr 2058, 2), (Sum.inr 2062, 1), (Sum.inr 2065, 1), (Sum.inr 2266, 1), (Sum.inr 2881, 2), (Sum.inr 2889, 1), (Sum.inr 3101, 1), (Sum.inr 3391, 2), (Sum.inr 3397, 1), (Sum.inr 3582, 1), (Sum.inr 3706, 2), (Sum.inr 3782, 2), (Sum.inr 3809, 2), (Sum.inr 3853, 2), (Sum.inr 3857, 2), (Sum.inr 3912, 1), (Sum.inr 3913, 1), (Sum.inr 3987, 1), (Sum.inr 4015, 1), (Sum.inr 4029, 2), (Sum.inr 4040, 1)]

theorem sourceEq906 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm906 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA906 + difference 0 1) (sourceB906 + difference 1 0) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA906 + difference 0 1) (sourceB906 + difference 1 0) sourceC906) = raw14943 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14943; decide +kernel
    rw [ha]
    exact (canonical14943 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA906 + difference 0 2) (sourceB906 + difference 2 0) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA906 + difference 0 2) (sourceB906 + difference 2 0) sourceC906) = raw14944 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14944; decide +kernel
    rw [ha]
    exact (canonical14944 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA906 + difference 0 3) (sourceB906 + difference 3 0) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA906 + difference 0 3) (sourceB906 + difference 3 0) sourceC906) = raw14945 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14945; decide +kernel
    rw [ha]
    exact (canonical14945 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA906 + difference 0 4) (sourceB906 + difference 4 0) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA906 + difference 0 4) (sourceB906 + difference 4 0) sourceC906) = raw14946 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14946; decide +kernel
    rw [ha]
    exact (canonical14946 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA906 + difference 0 5) (sourceB906 + difference 5 0) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA906 + difference 0 5) (sourceB906 + difference 5 0) sourceC906) = raw14947 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14947; decide +kernel
    rw [ha]
    exact (canonical14947 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA906 + difference 1 0) (sourceB906 + difference 0 1) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA906 + difference 1 0) (sourceB906 + difference 0 1) sourceC906) = raw14948 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14948; decide +kernel
    rw [ha]
    exact (canonical14948 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA906 + difference 1 2) (sourceB906 + difference 2 1) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA906 + difference 1 2) (sourceB906 + difference 2 1) sourceC906) = raw14949 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14949; decide +kernel
    rw [ha]
    exact (canonical14949 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA906 + difference 1 3) (sourceB906 + difference 3 1) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA906 + difference 1 3) (sourceB906 + difference 3 1) sourceC906) = raw14950 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14950; decide +kernel
    rw [ha]
    exact (canonical14950 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA906 + difference 1 4) (sourceB906 + difference 4 1) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA906 + difference 1 4) (sourceB906 + difference 4 1) sourceC906) = raw14951 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14951; decide +kernel
    rw [ha]
    exact (canonical14951 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA906 + difference 1 5) (sourceB906 + difference 5 1) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA906 + difference 1 5) (sourceB906 + difference 5 1) sourceC906) = raw14952 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14952; decide +kernel
    rw [ha]
    exact (canonical14952 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA906 + difference 2 0) (sourceB906 + difference 0 2) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA906 + difference 2 0) (sourceB906 + difference 0 2) sourceC906) = raw14953 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14953; decide +kernel
    rw [ha]
    exact (canonical14953 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA906 + difference 2 1) (sourceB906 + difference 1 2) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA906 + difference 2 1) (sourceB906 + difference 1 2) sourceC906) = raw14954 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14954; decide +kernel
    rw [ha]
    exact (canonical14954 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA906 + difference 2 3) (sourceB906 + difference 3 2) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA906 + difference 2 3) (sourceB906 + difference 3 2) sourceC906) = raw14955 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14955; decide +kernel
    rw [ha]
    exact (canonical14955 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA906 + difference 2 4) (sourceB906 + difference 4 2) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA906 + difference 2 4) (sourceB906 + difference 4 2) sourceC906) = raw14956 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14956; decide +kernel
    rw [ha]
    exact (canonical14956 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA906 + difference 2 5) (sourceB906 + difference 5 2) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA906 + difference 2 5) (sourceB906 + difference 5 2) sourceC906) = raw14957 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14957; decide +kernel
    rw [ha]
    exact (canonical14957 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA906 + difference 3 0) (sourceB906 + difference 0 3) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA906 + difference 3 0) (sourceB906 + difference 0 3) sourceC906) = raw14958 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14958; decide +kernel
    rw [ha]
    exact (canonical14958 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA906 + difference 3 1) (sourceB906 + difference 1 3) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA906 + difference 3 1) (sourceB906 + difference 1 3) sourceC906) = raw14959 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14959; decide +kernel
    rw [ha]
    exact (canonical14959 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA906 + difference 3 2) (sourceB906 + difference 2 3) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA906 + difference 3 2) (sourceB906 + difference 2 3) sourceC906) = raw14960 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14960; decide +kernel
    rw [ha]
    exact (canonical14960 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA906 + difference 3 4) (sourceB906 + difference 4 3) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA906 + difference 3 4) (sourceB906 + difference 4 3) sourceC906) = raw14961 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14961; decide +kernel
    rw [ha]
    exact (canonical14961 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA906 + difference 3 5) (sourceB906 + difference 5 3) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA906 + difference 3 5) (sourceB906 + difference 5 3) sourceC906) = raw14962 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14962; decide +kernel
    rw [ha]
    exact (canonical14962 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA906 + difference 4 0) (sourceB906 + difference 0 4) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA906 + difference 4 0) (sourceB906 + difference 0 4) sourceC906) = raw14963 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14963; decide +kernel
    rw [ha]
    exact (canonical14963 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA906 + difference 4 1) (sourceB906 + difference 1 4) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA906 + difference 4 1) (sourceB906 + difference 1 4) sourceC906) = raw14964 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14964; decide +kernel
    rw [ha]
    exact (canonical14964 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA906 + difference 4 2) (sourceB906 + difference 2 4) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA906 + difference 4 2) (sourceB906 + difference 2 4) sourceC906) = raw14965 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14965; decide +kernel
    rw [ha]
    exact (canonical14965 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA906 + difference 4 3) (sourceB906 + difference 3 4) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA906 + difference 4 3) (sourceB906 + difference 3 4) sourceC906) = raw14966 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14966; decide +kernel
    rw [ha]
    exact (canonical14966 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA906 + difference 4 5) (sourceB906 + difference 5 4) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA906 + difference 4 5) (sourceB906 + difference 5 4) sourceC906) = raw14967 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14967; decide +kernel
    rw [ha]
    exact (canonical14967 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA906 + difference 5 0) (sourceB906 + difference 0 5) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA906 + difference 5 0) (sourceB906 + difference 0 5) sourceC906) = raw14968 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14968; decide +kernel
    rw [ha]
    exact (canonical14968 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA906 + difference 5 1) (sourceB906 + difference 1 5) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA906 + difference 5 1) (sourceB906 + difference 1 5) sourceC906) = raw14969 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14969; decide +kernel
    rw [ha]
    exact (canonical14969 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA906 + difference 5 2) (sourceB906 + difference 2 5) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA906 + difference 5 2) (sourceB906 + difference 2 5) sourceC906) = raw14970 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14970; decide +kernel
    rw [ha]
    exact (canonical14970 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA906 + difference 5 3) (sourceB906 + difference 3 5) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA906 + difference 5 3) (sourceB906 + difference 3 5) sourceC906) = raw14971 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14971; decide +kernel
    rw [ha]
    exact (canonical14971 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA906 + difference 5 4) (sourceB906 + difference 4 5) sourceC906) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA906 + difference 5 4) (sourceB906 + difference 4 5) sourceC906) = raw14972 := by
      apply Matrix.ext; unfold tripleCharges sourceA906 sourceB906 sourceC906 difference raw14972; decide +kernel
    rw [ha]
    exact (canonical14972 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA906 sourceB906 sourceC906
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm906, Integer.Sparse.eval]
  linarith only [hs]

def sourceA907 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceB907 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC907 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm907 : Integer.Sparse Master := [(Sum.inr 5266, 2), (Sum.inr 5267, 2), (Sum.inr 5268, 1), (Sum.inr 5275, 1), (Sum.inr 5276, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 2), (Sum.inr 5302, 1), (Sum.inr 5304, 1), (Sum.inr 5411, 2), (Sum.inr 5413, 1), (Sum.inr 5425, 2), (Sum.inr 5428, 2), (Sum.inr 5435, 2), (Sum.inr 5436, 2), (Sum.inr 5438, 2), (Sum.inr 5442, 2), (Sum.inr 5443, 1), (Sum.inr 5451, 1)]

theorem sourceEq907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm907 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA907 + difference 0 1) (sourceB907 + difference 1 0) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA907 + difference 0 1) (sourceB907 + difference 1 0) sourceC907) = raw14973 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14973; decide +kernel
    rw [ha]
    exact (canonical14973 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA907 + difference 0 2) (sourceB907 + difference 2 0) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA907 + difference 0 2) (sourceB907 + difference 2 0) sourceC907) = raw14703 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14703; decide +kernel
    rw [ha]
    exact (canonical14703 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA907 + difference 0 3) (sourceB907 + difference 3 0) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA907 + difference 0 3) (sourceB907 + difference 3 0) sourceC907) = raw14974 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14974; decide +kernel
    rw [ha]
    exact (canonical14974 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA907 + difference 0 4) (sourceB907 + difference 4 0) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA907 + difference 0 4) (sourceB907 + difference 4 0) sourceC907) = raw14975 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14975; decide +kernel
    rw [ha]
    exact (canonical14975 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA907 + difference 0 5) (sourceB907 + difference 5 0) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA907 + difference 0 5) (sourceB907 + difference 5 0) sourceC907) = raw14976 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14976; decide +kernel
    rw [ha]
    exact (canonical14976 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA907 + difference 1 0) (sourceB907 + difference 0 1) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA907 + difference 1 0) (sourceB907 + difference 0 1) sourceC907) = raw14977 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14977; decide +kernel
    rw [ha]
    exact (canonical14977 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA907 + difference 1 2) (sourceB907 + difference 2 1) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA907 + difference 1 2) (sourceB907 + difference 2 1) sourceC907) = raw14708 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14708; decide +kernel
    rw [ha]
    exact (canonical14708 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA907 + difference 1 3) (sourceB907 + difference 3 1) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA907 + difference 1 3) (sourceB907 + difference 3 1) sourceC907) = raw14978 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14978; decide +kernel
    rw [ha]
    exact (canonical14978 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA907 + difference 1 4) (sourceB907 + difference 4 1) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA907 + difference 1 4) (sourceB907 + difference 4 1) sourceC907) = raw14979 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14979; decide +kernel
    rw [ha]
    exact (canonical14979 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA907 + difference 1 5) (sourceB907 + difference 5 1) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA907 + difference 1 5) (sourceB907 + difference 5 1) sourceC907) = raw14980 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14980; decide +kernel
    rw [ha]
    exact (canonical14980 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA907 + difference 2 0) (sourceB907 + difference 0 2) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA907 + difference 2 0) (sourceB907 + difference 0 2) sourceC907) = raw14981 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14981; decide +kernel
    rw [ha]
    exact (canonical14981 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA907 + difference 2 1) (sourceB907 + difference 1 2) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA907 + difference 2 1) (sourceB907 + difference 1 2) sourceC907) = raw14982 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14982; decide +kernel
    rw [ha]
    exact (canonical14982 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA907 + difference 2 3) (sourceB907 + difference 3 2) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA907 + difference 2 3) (sourceB907 + difference 3 2) sourceC907) = raw14983 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14983; decide +kernel
    rw [ha]
    exact (canonical14983 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA907 + difference 2 4) (sourceB907 + difference 4 2) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA907 + difference 2 4) (sourceB907 + difference 4 2) sourceC907) = raw14984 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14984; decide +kernel
    rw [ha]
    exact (canonical14984 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA907 + difference 2 5) (sourceB907 + difference 5 2) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA907 + difference 2 5) (sourceB907 + difference 5 2) sourceC907) = raw14985 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14985; decide +kernel
    rw [ha]
    exact (canonical14985 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA907 + difference 3 0) (sourceB907 + difference 0 3) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA907 + difference 3 0) (sourceB907 + difference 0 3) sourceC907) = raw14711 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14711; decide +kernel
    rw [ha]
    exact (canonical14711 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA907 + difference 3 1) (sourceB907 + difference 1 3) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA907 + difference 3 1) (sourceB907 + difference 1 3) sourceC907) = raw14712 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14712; decide +kernel
    rw [ha]
    exact (canonical14712 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA907 + difference 3 2) (sourceB907 + difference 2 3) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA907 + difference 3 2) (sourceB907 + difference 2 3) sourceC907) = raw14986 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14986; decide +kernel
    rw [ha]
    exact (canonical14986 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA907 + difference 3 4) (sourceB907 + difference 4 3) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA907 + difference 3 4) (sourceB907 + difference 4 3) sourceC907) = raw14714 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14714; decide +kernel
    rw [ha]
    exact (canonical14714 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA907 + difference 3 5) (sourceB907 + difference 5 3) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA907 + difference 3 5) (sourceB907 + difference 5 3) sourceC907) = raw14715 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14715; decide +kernel
    rw [ha]
    exact (canonical14715 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA907 + difference 4 0) (sourceB907 + difference 0 4) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA907 + difference 4 0) (sourceB907 + difference 0 4) sourceC907) = raw14987 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14987; decide +kernel
    rw [ha]
    exact (canonical14987 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA907 + difference 4 1) (sourceB907 + difference 1 4) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA907 + difference 4 1) (sourceB907 + difference 1 4) sourceC907) = raw14988 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14988; decide +kernel
    rw [ha]
    exact (canonical14988 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA907 + difference 4 2) (sourceB907 + difference 2 4) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA907 + difference 4 2) (sourceB907 + difference 2 4) sourceC907) = raw14724 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14724; decide +kernel
    rw [ha]
    exact (canonical14724 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA907 + difference 4 3) (sourceB907 + difference 3 4) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA907 + difference 4 3) (sourceB907 + difference 3 4) sourceC907) = raw14989 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14989; decide +kernel
    rw [ha]
    exact (canonical14989 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA907 + difference 4 5) (sourceB907 + difference 5 4) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA907 + difference 4 5) (sourceB907 + difference 5 4) sourceC907) = raw14990 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14990; decide +kernel
    rw [ha]
    exact (canonical14990 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA907 + difference 5 0) (sourceB907 + difference 0 5) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA907 + difference 5 0) (sourceB907 + difference 0 5) sourceC907) = raw14991 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14991; decide +kernel
    rw [ha]
    exact (canonical14991 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA907 + difference 5 1) (sourceB907 + difference 1 5) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA907 + difference 5 1) (sourceB907 + difference 1 5) sourceC907) = raw14992 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14992; decide +kernel
    rw [ha]
    exact (canonical14992 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA907 + difference 5 2) (sourceB907 + difference 2 5) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA907 + difference 5 2) (sourceB907 + difference 2 5) sourceC907) = raw14729 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14729; decide +kernel
    rw [ha]
    exact (canonical14729 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA907 + difference 5 3) (sourceB907 + difference 3 5) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA907 + difference 5 3) (sourceB907 + difference 3 5) sourceC907) = raw14993 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14993; decide +kernel
    rw [ha]
    exact (canonical14993 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA907 + difference 5 4) (sourceB907 + difference 4 5) sourceC907) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA907 + difference 5 4) (sourceB907 + difference 4 5) sourceC907) = raw14994 := by
      apply Matrix.ext; unfold tripleCharges sourceA907 sourceB907 sourceC907 difference raw14994; decide +kernel
    rw [ha]
    exact (canonical14994 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA907 sourceB907 sourceC907
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm907, Integer.Sparse.eval]
  linarith only [hs]

def sourceA908 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceB908 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC908 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm908 : Integer.Sparse Master := [(Sum.inr 2732, 2), (Sum.inr 2734, 1), (Sum.inr 2744, 1), (Sum.inr 2776, 1), (Sum.inr 3039, 2), (Sum.inr 3055, 1), (Sum.inr 3110, 1), (Sum.inr 3573, 2), (Sum.inr 3583, 1), (Sum.inr 3584, 1), (Sum.inr 3853, 2), (Sum.inr 3861, 1), (Sum.inr 3862, 1), (Sum.inr 3872, 2), (Sum.inr 3876, 2), (Sum.inr 3877, 2), (Sum.inr 3883, 2), (Sum.inr 3888, 1), (Sum.inr 4001, 1), (Sum.inr 4003, 2), (Sum.inr 4006, 1)]

theorem sourceEq908 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm908 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA908 + difference 0 1) (sourceB908 + difference 1 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA908 + difference 0 1) (sourceB908 + difference 1 0) sourceC908) = raw14995 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14995; decide +kernel
    rw [ha]
    exact (canonical14995 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA908 + difference 0 2) (sourceB908 + difference 2 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA908 + difference 0 2) (sourceB908 + difference 2 0) sourceC908) = raw14763 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14763; decide +kernel
    rw [ha]
    exact (canonical14763 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA908 + difference 0 3) (sourceB908 + difference 3 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA908 + difference 0 3) (sourceB908 + difference 3 0) sourceC908) = raw14996 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14996; decide +kernel
    rw [ha]
    exact (canonical14996 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA908 + difference 0 4) (sourceB908 + difference 4 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA908 + difference 0 4) (sourceB908 + difference 4 0) sourceC908) = raw14997 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14997; decide +kernel
    rw [ha]
    exact (canonical14997 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA908 + difference 0 5) (sourceB908 + difference 5 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA908 + difference 0 5) (sourceB908 + difference 5 0) sourceC908) = raw14998 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14998; decide +kernel
    rw [ha]
    exact (canonical14998 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA908 + difference 1 0) (sourceB908 + difference 0 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA908 + difference 1 0) (sourceB908 + difference 0 1) sourceC908) = raw14999 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14999; decide +kernel
    rw [ha]
    exact (canonical14999 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA908 + difference 1 2) (sourceB908 + difference 2 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA908 + difference 1 2) (sourceB908 + difference 2 1) sourceC908) = raw14768 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14768; decide +kernel
    rw [ha]
    exact (canonical14768 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA908 + difference 1 3) (sourceB908 + difference 3 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA908 + difference 1 3) (sourceB908 + difference 3 1) sourceC908) = raw15000 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15000; decide +kernel
    rw [ha]
    exact (canonical15000 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA908 + difference 1 4) (sourceB908 + difference 4 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA908 + difference 1 4) (sourceB908 + difference 4 1) sourceC908) = raw15001 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15001; decide +kernel
    rw [ha]
    exact (canonical15001 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA908 + difference 1 5) (sourceB908 + difference 5 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA908 + difference 1 5) (sourceB908 + difference 5 1) sourceC908) = raw15002 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15002; decide +kernel
    rw [ha]
    exact (canonical15002 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA908 + difference 2 0) (sourceB908 + difference 0 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA908 + difference 2 0) (sourceB908 + difference 0 2) sourceC908) = raw15003 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15003; decide +kernel
    rw [ha]
    exact (canonical15003 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA908 + difference 2 1) (sourceB908 + difference 1 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA908 + difference 2 1) (sourceB908 + difference 1 2) sourceC908) = raw15004 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15004; decide +kernel
    rw [ha]
    exact (canonical15004 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA908 + difference 2 3) (sourceB908 + difference 3 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA908 + difference 2 3) (sourceB908 + difference 3 2) sourceC908) = raw15005 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15005; decide +kernel
    rw [ha]
    exact (canonical15005 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA908 + difference 2 4) (sourceB908 + difference 4 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA908 + difference 2 4) (sourceB908 + difference 4 2) sourceC908) = raw15006 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15006; decide +kernel
    rw [ha]
    exact (canonical15006 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA908 + difference 2 5) (sourceB908 + difference 5 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA908 + difference 2 5) (sourceB908 + difference 5 2) sourceC908) = raw15007 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15007; decide +kernel
    rw [ha]
    exact (canonical15007 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA908 + difference 3 0) (sourceB908 + difference 0 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA908 + difference 3 0) (sourceB908 + difference 0 3) sourceC908) = raw14771 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14771; decide +kernel
    rw [ha]
    exact (canonical14771 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA908 + difference 3 1) (sourceB908 + difference 1 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA908 + difference 3 1) (sourceB908 + difference 1 3) sourceC908) = raw14772 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14772; decide +kernel
    rw [ha]
    exact (canonical14772 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA908 + difference 3 2) (sourceB908 + difference 2 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA908 + difference 3 2) (sourceB908 + difference 2 3) sourceC908) = raw15008 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15008; decide +kernel
    rw [ha]
    exact (canonical15008 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA908 + difference 3 4) (sourceB908 + difference 4 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA908 + difference 3 4) (sourceB908 + difference 4 3) sourceC908) = raw14774 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14774; decide +kernel
    rw [ha]
    exact (canonical14774 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA908 + difference 3 5) (sourceB908 + difference 5 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA908 + difference 3 5) (sourceB908 + difference 5 3) sourceC908) = raw14775 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14775; decide +kernel
    rw [ha]
    exact (canonical14775 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA908 + difference 4 0) (sourceB908 + difference 0 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA908 + difference 4 0) (sourceB908 + difference 0 4) sourceC908) = raw15009 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15009; decide +kernel
    rw [ha]
    exact (canonical15009 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA908 + difference 4 1) (sourceB908 + difference 1 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA908 + difference 4 1) (sourceB908 + difference 1 4) sourceC908) = raw15010 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15010; decide +kernel
    rw [ha]
    exact (canonical15010 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA908 + difference 4 2) (sourceB908 + difference 2 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA908 + difference 4 2) (sourceB908 + difference 2 4) sourceC908) = raw14784 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14784; decide +kernel
    rw [ha]
    exact (canonical14784 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA908 + difference 4 3) (sourceB908 + difference 3 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA908 + difference 4 3) (sourceB908 + difference 3 4) sourceC908) = raw15011 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15011; decide +kernel
    rw [ha]
    exact (canonical15011 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA908 + difference 4 5) (sourceB908 + difference 5 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA908 + difference 4 5) (sourceB908 + difference 5 4) sourceC908) = raw15012 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15012; decide +kernel
    rw [ha]
    exact (canonical15012 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA908 + difference 5 0) (sourceB908 + difference 0 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA908 + difference 5 0) (sourceB908 + difference 0 5) sourceC908) = raw15013 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15013; decide +kernel
    rw [ha]
    exact (canonical15013 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA908 + difference 5 1) (sourceB908 + difference 1 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4006) := by
    have ha : (tripleCharges (sourceA908 + difference 5 1) (sourceB908 + difference 1 5) sourceC908) = raw15014 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15014; decide +kernel
    rw [ha]
    exact (canonical15014 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA908 + difference 5 2) (sourceB908 + difference 2 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA908 + difference 5 2) (sourceB908 + difference 2 5) sourceC908) = raw14789 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14789; decide +kernel
    rw [ha]
    exact (canonical14789 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA908 + difference 5 3) (sourceB908 + difference 3 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA908 + difference 5 3) (sourceB908 + difference 3 5) sourceC908) = raw15015 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15015; decide +kernel
    rw [ha]
    exact (canonical15015 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA908 + difference 5 4) (sourceB908 + difference 4 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA908 + difference 5 4) (sourceB908 + difference 4 5) sourceC908) = raw15016 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15016; decide +kernel
    rw [ha]
    exact (canonical15016 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA908 sourceB908 sourceC908
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm908, Integer.Sparse.eval]
  linarith only [hs]

def sourceA909 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB909 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC909 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm909 : Integer.Sparse Master := [(Sum.inr 5076, 1), (Sum.inr 5078, 1), (Sum.inr 5080, 1), (Sum.inr 5105, 1), (Sum.inr 5148, 1), (Sum.inr 5152, 1), (Sum.inr 5169, 1), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5354, 1), (Sum.inr 5355, 1), (Sum.inr 5370, 1), (Sum.inr 5380, 1), (Sum.inr 5388, 1), (Sum.inr 5416, 1), (Sum.inr 5422, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 1), (Sum.inr 5438, 1), (Sum.inr 5440, 1), (Sum.inr 5442, 1), (Sum.inr 5451, 1), (Sum.inr 5454, 1), (Sum.inr 5455, 1), (Sum.inr 5481, 1), (Sum.inr 5484, 1), (Sum.inr 5490, 1), (Sum.inr 5492, 1)]

theorem sourceEq909 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm909 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA909 + difference 0 1) (sourceB909 + difference 1 0) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA909 + difference 0 1) (sourceB909 + difference 1 0) sourceC909) = raw15017 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15017; decide +kernel
    rw [ha]
    exact (canonical15017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA909 + difference 0 2) (sourceB909 + difference 2 0) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA909 + difference 0 2) (sourceB909 + difference 2 0) sourceC909) = raw15018 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15018; decide +kernel
    rw [ha]
    exact (canonical15018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA909 + difference 0 3) (sourceB909 + difference 3 0) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA909 + difference 0 3) (sourceB909 + difference 3 0) sourceC909) = raw15019 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15019; decide +kernel
    rw [ha]
    exact (canonical15019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA909 + difference 0 4) (sourceB909 + difference 4 0) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA909 + difference 0 4) (sourceB909 + difference 4 0) sourceC909) = raw15020 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15020; decide +kernel
    rw [ha]
    exact (canonical15020 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA909 + difference 0 5) (sourceB909 + difference 5 0) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA909 + difference 0 5) (sourceB909 + difference 5 0) sourceC909) = raw15021 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15021; decide +kernel
    rw [ha]
    exact (canonical15021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA909 + difference 1 0) (sourceB909 + difference 0 1) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA909 + difference 1 0) (sourceB909 + difference 0 1) sourceC909) = raw15022 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15022; decide +kernel
    rw [ha]
    exact (canonical15022 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA909 + difference 1 2) (sourceB909 + difference 2 1) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA909 + difference 1 2) (sourceB909 + difference 2 1) sourceC909) = raw7807 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw7807; decide +kernel
    rw [ha]
    exact (canonical7807 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA909 + difference 1 3) (sourceB909 + difference 3 1) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA909 + difference 1 3) (sourceB909 + difference 3 1) sourceC909) = raw7808 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw7808; decide +kernel
    rw [ha]
    exact (canonical7808 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA909 + difference 1 4) (sourceB909 + difference 4 1) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA909 + difference 1 4) (sourceB909 + difference 4 1) sourceC909) = raw7809 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw7809; decide +kernel
    rw [ha]
    exact (canonical7809 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA909 + difference 1 5) (sourceB909 + difference 5 1) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA909 + difference 1 5) (sourceB909 + difference 5 1) sourceC909) = raw7810 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw7810; decide +kernel
    rw [ha]
    exact (canonical7810 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA909 + difference 2 0) (sourceB909 + difference 0 2) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA909 + difference 2 0) (sourceB909 + difference 0 2) sourceC909) = raw7817 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw7817; decide +kernel
    rw [ha]
    exact (canonical7817 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA909 + difference 2 1) (sourceB909 + difference 1 2) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA909 + difference 2 1) (sourceB909 + difference 1 2) sourceC909) = raw15023 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15023; decide +kernel
    rw [ha]
    exact (canonical15023 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA909 + difference 2 3) (sourceB909 + difference 3 2) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA909 + difference 2 3) (sourceB909 + difference 3 2) sourceC909) = raw15024 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15024; decide +kernel
    rw [ha]
    exact (canonical15024 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA909 + difference 2 4) (sourceB909 + difference 4 2) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA909 + difference 2 4) (sourceB909 + difference 4 2) sourceC909) = raw15025 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15025; decide +kernel
    rw [ha]
    exact (canonical15025 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA909 + difference 2 5) (sourceB909 + difference 5 2) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA909 + difference 2 5) (sourceB909 + difference 5 2) sourceC909) = raw15026 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15026; decide +kernel
    rw [ha]
    exact (canonical15026 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA909 + difference 3 0) (sourceB909 + difference 0 3) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA909 + difference 3 0) (sourceB909 + difference 0 3) sourceC909) = raw7822 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw7822; decide +kernel
    rw [ha]
    exact (canonical7822 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA909 + difference 3 1) (sourceB909 + difference 1 3) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA909 + difference 3 1) (sourceB909 + difference 1 3) sourceC909) = raw15027 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15027; decide +kernel
    rw [ha]
    exact (canonical15027 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA909 + difference 3 2) (sourceB909 + difference 2 3) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA909 + difference 3 2) (sourceB909 + difference 2 3) sourceC909) = raw15028 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15028; decide +kernel
    rw [ha]
    exact (canonical15028 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA909 + difference 3 4) (sourceB909 + difference 4 3) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA909 + difference 3 4) (sourceB909 + difference 4 3) sourceC909) = raw15029 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15029; decide +kernel
    rw [ha]
    exact (canonical15029 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA909 + difference 3 5) (sourceB909 + difference 5 3) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA909 + difference 3 5) (sourceB909 + difference 5 3) sourceC909) = raw15030 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15030; decide +kernel
    rw [ha]
    exact (canonical15030 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA909 + difference 4 0) (sourceB909 + difference 0 4) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA909 + difference 4 0) (sourceB909 + difference 0 4) sourceC909) = raw7827 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw7827; decide +kernel
    rw [ha]
    exact (canonical7827 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA909 + difference 4 1) (sourceB909 + difference 1 4) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA909 + difference 4 1) (sourceB909 + difference 1 4) sourceC909) = raw15031 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15031; decide +kernel
    rw [ha]
    exact (canonical15031 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA909 + difference 4 2) (sourceB909 + difference 2 4) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA909 + difference 4 2) (sourceB909 + difference 2 4) sourceC909) = raw15032 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15032; decide +kernel
    rw [ha]
    exact (canonical15032 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA909 + difference 4 3) (sourceB909 + difference 3 4) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA909 + difference 4 3) (sourceB909 + difference 3 4) sourceC909) = raw15033 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15033; decide +kernel
    rw [ha]
    exact (canonical15033 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA909 + difference 4 5) (sourceB909 + difference 5 4) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA909 + difference 4 5) (sourceB909 + difference 5 4) sourceC909) = raw15034 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15034; decide +kernel
    rw [ha]
    exact (canonical15034 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA909 + difference 5 0) (sourceB909 + difference 0 5) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA909 + difference 5 0) (sourceB909 + difference 0 5) sourceC909) = raw7832 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw7832; decide +kernel
    rw [ha]
    exact (canonical7832 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA909 + difference 5 1) (sourceB909 + difference 1 5) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA909 + difference 5 1) (sourceB909 + difference 1 5) sourceC909) = raw15035 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15035; decide +kernel
    rw [ha]
    exact (canonical15035 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA909 + difference 5 2) (sourceB909 + difference 2 5) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA909 + difference 5 2) (sourceB909 + difference 2 5) sourceC909) = raw15036 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15036; decide +kernel
    rw [ha]
    exact (canonical15036 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA909 + difference 5 3) (sourceB909 + difference 3 5) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA909 + difference 5 3) (sourceB909 + difference 3 5) sourceC909) = raw15037 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15037; decide +kernel
    rw [ha]
    exact (canonical15037 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA909 + difference 5 4) (sourceB909 + difference 4 5) sourceC909) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA909 + difference 5 4) (sourceB909 + difference 4 5) sourceC909) = raw15038 := by
      apply Matrix.ext; unfold tripleCharges sourceA909 sourceB909 sourceC909 difference raw15038; decide +kernel
    rw [ha]
    exact (canonical15038 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA909 sourceB909 sourceC909
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm909, Integer.Sparse.eval]
  linarith only [hs]

def sourceA910 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB910 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC910 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm910 : Integer.Sparse Master := [(Sum.inr 2483, 1), (Sum.inr 2485, 1), (Sum.inr 2488, 1), (Sum.inr 2515, 1), (Sum.inr 2768, 1), (Sum.inr 2927, 1), (Sum.inr 2931, 1), (Sum.inr 2960, 1), (Sum.inr 3102, 1), (Sum.inr 3692, 1), (Sum.inr 3693, 1), (Sum.inr 3706, 1), (Sum.inr 3721, 1), (Sum.inr 3737, 1), (Sum.inr 3853, 1), (Sum.inr 3876, 1), (Sum.inr 3964, 1), (Sum.inr 3967, 1), (Sum.inr 3979, 1), (Sum.inr 3982, 2), (Sum.inr 3983, 1), (Sum.inr 3987, 1), (Sum.inr 4001, 1), (Sum.inr 4013, 1), (Sum.inr 4017, 1), (Sum.inr 4019, 1), (Sum.inr 4033, 1), (Sum.inr 4036, 1), (Sum.inr 4040, 1)]

theorem sourceEq910 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm910 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA910 + difference 0 1) (sourceB910 + difference 1 0) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA910 + difference 0 1) (sourceB910 + difference 1 0) sourceC910) = raw15039 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15039; decide +kernel
    rw [ha]
    exact (canonical15039 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA910 + difference 0 2) (sourceB910 + difference 2 0) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA910 + difference 0 2) (sourceB910 + difference 2 0) sourceC910) = raw15040 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15040; decide +kernel
    rw [ha]
    exact (canonical15040 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA910 + difference 0 3) (sourceB910 + difference 3 0) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA910 + difference 0 3) (sourceB910 + difference 3 0) sourceC910) = raw15041 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15041; decide +kernel
    rw [ha]
    exact (canonical15041 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA910 + difference 0 4) (sourceB910 + difference 4 0) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA910 + difference 0 4) (sourceB910 + difference 4 0) sourceC910) = raw15042 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15042; decide +kernel
    rw [ha]
    exact (canonical15042 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA910 + difference 0 5) (sourceB910 + difference 5 0) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA910 + difference 0 5) (sourceB910 + difference 5 0) sourceC910) = raw15043 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15043; decide +kernel
    rw [ha]
    exact (canonical15043 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA910 + difference 1 0) (sourceB910 + difference 0 1) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA910 + difference 1 0) (sourceB910 + difference 0 1) sourceC910) = raw15044 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15044; decide +kernel
    rw [ha]
    exact (canonical15044 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA910 + difference 1 2) (sourceB910 + difference 2 1) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA910 + difference 1 2) (sourceB910 + difference 2 1) sourceC910) = raw7837 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw7837; decide +kernel
    rw [ha]
    exact (canonical7837 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA910 + difference 1 3) (sourceB910 + difference 3 1) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA910 + difference 1 3) (sourceB910 + difference 3 1) sourceC910) = raw7838 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw7838; decide +kernel
    rw [ha]
    exact (canonical7838 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA910 + difference 1 4) (sourceB910 + difference 4 1) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA910 + difference 1 4) (sourceB910 + difference 4 1) sourceC910) = raw7839 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw7839; decide +kernel
    rw [ha]
    exact (canonical7839 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA910 + difference 1 5) (sourceB910 + difference 5 1) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA910 + difference 1 5) (sourceB910 + difference 5 1) sourceC910) = raw7840 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw7840; decide +kernel
    rw [ha]
    exact (canonical7840 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA910 + difference 2 0) (sourceB910 + difference 0 2) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA910 + difference 2 0) (sourceB910 + difference 0 2) sourceC910) = raw7847 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw7847; decide +kernel
    rw [ha]
    exact (canonical7847 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA910 + difference 2 1) (sourceB910 + difference 1 2) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA910 + difference 2 1) (sourceB910 + difference 1 2) sourceC910) = raw15045 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15045; decide +kernel
    rw [ha]
    exact (canonical15045 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA910 + difference 2 3) (sourceB910 + difference 3 2) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA910 + difference 2 3) (sourceB910 + difference 3 2) sourceC910) = raw15046 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15046; decide +kernel
    rw [ha]
    exact (canonical15046 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA910 + difference 2 4) (sourceB910 + difference 4 2) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA910 + difference 2 4) (sourceB910 + difference 4 2) sourceC910) = raw15047 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15047; decide +kernel
    rw [ha]
    exact (canonical15047 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA910 + difference 2 5) (sourceB910 + difference 5 2) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA910 + difference 2 5) (sourceB910 + difference 5 2) sourceC910) = raw15048 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15048; decide +kernel
    rw [ha]
    exact (canonical15048 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA910 + difference 3 0) (sourceB910 + difference 0 3) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA910 + difference 3 0) (sourceB910 + difference 0 3) sourceC910) = raw7852 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw7852; decide +kernel
    rw [ha]
    exact (canonical7852 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA910 + difference 3 1) (sourceB910 + difference 1 3) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA910 + difference 3 1) (sourceB910 + difference 1 3) sourceC910) = raw15049 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15049; decide +kernel
    rw [ha]
    exact (canonical15049 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA910 + difference 3 2) (sourceB910 + difference 2 3) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3967) := by
    have ha : (tripleCharges (sourceA910 + difference 3 2) (sourceB910 + difference 2 3) sourceC910) = raw15050 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15050; decide +kernel
    rw [ha]
    exact (canonical15050 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA910 + difference 3 4) (sourceB910 + difference 4 3) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA910 + difference 3 4) (sourceB910 + difference 4 3) sourceC910) = raw15051 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15051; decide +kernel
    rw [ha]
    exact (canonical15051 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA910 + difference 3 5) (sourceB910 + difference 5 3) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4036) := by
    have ha : (tripleCharges (sourceA910 + difference 3 5) (sourceB910 + difference 5 3) sourceC910) = raw15052 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15052; decide +kernel
    rw [ha]
    exact (canonical15052 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA910 + difference 4 0) (sourceB910 + difference 0 4) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA910 + difference 4 0) (sourceB910 + difference 0 4) sourceC910) = raw7857 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw7857; decide +kernel
    rw [ha]
    exact (canonical7857 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA910 + difference 4 1) (sourceB910 + difference 1 4) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA910 + difference 4 1) (sourceB910 + difference 1 4) sourceC910) = raw15053 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15053; decide +kernel
    rw [ha]
    exact (canonical15053 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA910 + difference 4 2) (sourceB910 + difference 2 4) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA910 + difference 4 2) (sourceB910 + difference 2 4) sourceC910) = raw15054 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15054; decide +kernel
    rw [ha]
    exact (canonical15054 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA910 + difference 4 3) (sourceB910 + difference 3 4) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA910 + difference 4 3) (sourceB910 + difference 3 4) sourceC910) = raw15055 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15055; decide +kernel
    rw [ha]
    exact (canonical15055 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA910 + difference 4 5) (sourceB910 + difference 5 4) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA910 + difference 4 5) (sourceB910 + difference 5 4) sourceC910) = raw15056 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15056; decide +kernel
    rw [ha]
    exact (canonical15056 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA910 + difference 5 0) (sourceB910 + difference 0 5) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA910 + difference 5 0) (sourceB910 + difference 0 5) sourceC910) = raw7862 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw7862; decide +kernel
    rw [ha]
    exact (canonical7862 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA910 + difference 5 1) (sourceB910 + difference 1 5) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA910 + difference 5 1) (sourceB910 + difference 1 5) sourceC910) = raw15057 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15057; decide +kernel
    rw [ha]
    exact (canonical15057 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA910 + difference 5 2) (sourceB910 + difference 2 5) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA910 + difference 5 2) (sourceB910 + difference 2 5) sourceC910) = raw15058 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15058; decide +kernel
    rw [ha]
    exact (canonical15058 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA910 + difference 5 3) (sourceB910 + difference 3 5) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA910 + difference 5 3) (sourceB910 + difference 3 5) sourceC910) = raw15059 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15059; decide +kernel
    rw [ha]
    exact (canonical15059 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA910 + difference 5 4) (sourceB910 + difference 4 5) sourceC910) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA910 + difference 5 4) (sourceB910 + difference 4 5) sourceC910) = raw15060 := by
      apply Matrix.ext; unfold tripleCharges sourceA910 sourceB910 sourceC910 difference raw15060; decide +kernel
    rw [ha]
    exact (canonical15060 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA910 sourceB910 sourceC910
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm910, Integer.Sparse.eval]
  linarith only [hs]

def sourceA911 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB911 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC911 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceForm911 : Integer.Sparse Master := [(Sum.inr 4802, 1), (Sum.inr 4804, 1), (Sum.inr 4811, 1), (Sum.inr 4835, 1), (Sum.inr 4888, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5168, 1), (Sum.inr 5258, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5368, 1), (Sum.inr 5393, 1), (Sum.inr 5395, 1), (Sum.inr 5405, 1), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5424, 1), (Sum.inr 5428, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2), (Sum.inr 5439, 2), (Sum.inr 5452, 1), (Sum.inr 5482, 1), (Sum.inr 5483, 1), (Sum.inr 5486, 1), (Sum.inr 5490, 1), (Sum.inr 5499, 1)]

theorem sourceEq911 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm911 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA911 + difference 0 1) (sourceB911 + difference 1 0) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA911 + difference 0 1) (sourceB911 + difference 1 0) sourceC911) = raw3427 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw3427; decide +kernel
    rw [ha]
    exact (canonical3427 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA911 + difference 0 2) (sourceB911 + difference 2 0) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA911 + difference 0 2) (sourceB911 + difference 2 0) sourceC911) = raw3428 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw3428; decide +kernel
    rw [ha]
    exact (canonical3428 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA911 + difference 0 3) (sourceB911 + difference 3 0) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA911 + difference 0 3) (sourceB911 + difference 3 0) sourceC911) = raw3429 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw3429; decide +kernel
    rw [ha]
    exact (canonical3429 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA911 + difference 0 4) (sourceB911 + difference 4 0) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA911 + difference 0 4) (sourceB911 + difference 4 0) sourceC911) = raw3430 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw3430; decide +kernel
    rw [ha]
    exact (canonical3430 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA911 + difference 0 5) (sourceB911 + difference 5 0) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA911 + difference 0 5) (sourceB911 + difference 5 0) sourceC911) = raw15061 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15061; decide +kernel
    rw [ha]
    exact (canonical15061 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA911 + difference 1 0) (sourceB911 + difference 0 1) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA911 + difference 1 0) (sourceB911 + difference 0 1) sourceC911) = raw15062 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15062; decide +kernel
    rw [ha]
    exact (canonical15062 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA911 + difference 1 2) (sourceB911 + difference 2 1) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA911 + difference 1 2) (sourceB911 + difference 2 1) sourceC911) = raw15063 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15063; decide +kernel
    rw [ha]
    exact (canonical15063 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA911 + difference 1 3) (sourceB911 + difference 3 1) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA911 + difference 1 3) (sourceB911 + difference 3 1) sourceC911) = raw15064 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15064; decide +kernel
    rw [ha]
    exact (canonical15064 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA911 + difference 1 4) (sourceB911 + difference 4 1) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA911 + difference 1 4) (sourceB911 + difference 4 1) sourceC911) = raw15065 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15065; decide +kernel
    rw [ha]
    exact (canonical15065 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA911 + difference 1 5) (sourceB911 + difference 5 1) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA911 + difference 1 5) (sourceB911 + difference 5 1) sourceC911) = raw3406 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw3406; decide +kernel
    rw [ha]
    exact (canonical3406 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA911 + difference 2 0) (sourceB911 + difference 0 2) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA911 + difference 2 0) (sourceB911 + difference 0 2) sourceC911) = raw15066 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15066; decide +kernel
    rw [ha]
    exact (canonical15066 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA911 + difference 2 1) (sourceB911 + difference 1 2) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA911 + difference 2 1) (sourceB911 + difference 1 2) sourceC911) = raw15067 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15067; decide +kernel
    rw [ha]
    exact (canonical15067 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA911 + difference 2 3) (sourceB911 + difference 3 2) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA911 + difference 2 3) (sourceB911 + difference 3 2) sourceC911) = raw15068 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15068; decide +kernel
    rw [ha]
    exact (canonical15068 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA911 + difference 2 4) (sourceB911 + difference 4 2) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA911 + difference 2 4) (sourceB911 + difference 4 2) sourceC911) = raw15069 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15069; decide +kernel
    rw [ha]
    exact (canonical15069 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA911 + difference 2 5) (sourceB911 + difference 5 2) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA911 + difference 2 5) (sourceB911 + difference 5 2) sourceC911) = raw3411 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw3411; decide +kernel
    rw [ha]
    exact (canonical3411 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA911 + difference 3 0) (sourceB911 + difference 0 3) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA911 + difference 3 0) (sourceB911 + difference 0 3) sourceC911) = raw15070 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15070; decide +kernel
    rw [ha]
    exact (canonical15070 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA911 + difference 3 1) (sourceB911 + difference 1 3) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA911 + difference 3 1) (sourceB911 + difference 1 3) sourceC911) = raw15071 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15071; decide +kernel
    rw [ha]
    exact (canonical15071 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA911 + difference 3 2) (sourceB911 + difference 2 3) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA911 + difference 3 2) (sourceB911 + difference 2 3) sourceC911) = raw15072 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15072; decide +kernel
    rw [ha]
    exact (canonical15072 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA911 + difference 3 4) (sourceB911 + difference 4 3) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA911 + difference 3 4) (sourceB911 + difference 4 3) sourceC911) = raw15073 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15073; decide +kernel
    rw [ha]
    exact (canonical15073 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA911 + difference 3 5) (sourceB911 + difference 5 3) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA911 + difference 3 5) (sourceB911 + difference 5 3) sourceC911) = raw3416 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw3416; decide +kernel
    rw [ha]
    exact (canonical3416 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA911 + difference 4 0) (sourceB911 + difference 0 4) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA911 + difference 4 0) (sourceB911 + difference 0 4) sourceC911) = raw15074 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15074; decide +kernel
    rw [ha]
    exact (canonical15074 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA911 + difference 4 1) (sourceB911 + difference 1 4) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA911 + difference 4 1) (sourceB911 + difference 1 4) sourceC911) = raw15075 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15075; decide +kernel
    rw [ha]
    exact (canonical15075 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA911 + difference 4 2) (sourceB911 + difference 2 4) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA911 + difference 4 2) (sourceB911 + difference 2 4) sourceC911) = raw15076 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15076; decide +kernel
    rw [ha]
    exact (canonical15076 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA911 + difference 4 3) (sourceB911 + difference 3 4) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA911 + difference 4 3) (sourceB911 + difference 3 4) sourceC911) = raw15077 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15077; decide +kernel
    rw [ha]
    exact (canonical15077 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA911 + difference 4 5) (sourceB911 + difference 5 4) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA911 + difference 4 5) (sourceB911 + difference 5 4) sourceC911) = raw3421 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw3421; decide +kernel
    rw [ha]
    exact (canonical3421 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA911 + difference 5 0) (sourceB911 + difference 0 5) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA911 + difference 5 0) (sourceB911 + difference 0 5) sourceC911) = raw15078 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15078; decide +kernel
    rw [ha]
    exact (canonical15078 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA911 + difference 5 1) (sourceB911 + difference 1 5) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA911 + difference 5 1) (sourceB911 + difference 1 5) sourceC911) = raw15079 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15079; decide +kernel
    rw [ha]
    exact (canonical15079 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA911 + difference 5 2) (sourceB911 + difference 2 5) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA911 + difference 5 2) (sourceB911 + difference 2 5) sourceC911) = raw15080 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15080; decide +kernel
    rw [ha]
    exact (canonical15080 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA911 + difference 5 3) (sourceB911 + difference 3 5) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA911 + difference 5 3) (sourceB911 + difference 3 5) sourceC911) = raw15081 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15081; decide +kernel
    rw [ha]
    exact (canonical15081 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA911 + difference 5 4) (sourceB911 + difference 4 5) sourceC911) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA911 + difference 5 4) (sourceB911 + difference 4 5) sourceC911) = raw15082 := by
      apply Matrix.ext; unfold tripleCharges sourceA911 sourceB911 sourceC911 difference raw15082; decide +kernel
    rw [ha]
    exact (canonical15082 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA911 sourceB911 sourceC911
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm911, Integer.Sparse.eval]
  linarith only [hs]

def sourceA912 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB912 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC912 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceForm912 : Integer.Sparse Master := [(Sum.inr 2020, 1), (Sum.inr 2022, 1), (Sum.inr 2029, 1), (Sum.inr 2054, 1), (Sum.inr 2244, 1), (Sum.inr 2553, 1), (Sum.inr 2561, 1), (Sum.inr 2594, 1), (Sum.inr 2722, 1), (Sum.inr 3690, 1), (Sum.inr 3694, 1), (Sum.inr 3705, 1), (Sum.inr 3779, 1), (Sum.inr 3781, 1), (Sum.inr 3800, 1), (Sum.inr 3821, 1), (Sum.inr 3824, 1), (Sum.inr 3838, 1), (Sum.inr 3845, 1), (Sum.inr 3851, 1), (Sum.inr 3852, 2), (Sum.inr 3858, 1), (Sum.inr 3902, 1), (Sum.inr 3911, 1), (Sum.inr 3981, 1), (Sum.inr 3992, 1), (Sum.inr 3999, 1), (Sum.inr 4013, 1), (Sum.inr 4054, 1)]

theorem sourceEq912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm912 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA912 + difference 0 1) (sourceB912 + difference 1 0) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA912 + difference 0 1) (sourceB912 + difference 1 0) sourceC912) = raw15083 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15083; decide +kernel
    rw [ha]
    exact (canonical15083 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA912 + difference 0 2) (sourceB912 + difference 2 0) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA912 + difference 0 2) (sourceB912 + difference 2 0) sourceC912) = raw15084 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15084; decide +kernel
    rw [ha]
    exact (canonical15084 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA912 + difference 0 3) (sourceB912 + difference 3 0) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3999) := by
    have ha : (tripleCharges (sourceA912 + difference 0 3) (sourceB912 + difference 3 0) sourceC912) = raw15085 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15085; decide +kernel
    rw [ha]
    exact (canonical15085 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA912 + difference 0 4) (sourceB912 + difference 4 0) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA912 + difference 0 4) (sourceB912 + difference 4 0) sourceC912) = raw15086 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15086; decide +kernel
    rw [ha]
    exact (canonical15086 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA912 + difference 0 5) (sourceB912 + difference 5 0) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4054) := by
    have ha : (tripleCharges (sourceA912 + difference 0 5) (sourceB912 + difference 5 0) sourceC912) = raw15087 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15087; decide +kernel
    rw [ha]
    exact (canonical15087 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA912 + difference 1 0) (sourceB912 + difference 0 1) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA912 + difference 1 0) (sourceB912 + difference 0 1) sourceC912) = raw15088 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15088; decide +kernel
    rw [ha]
    exact (canonical15088 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA912 + difference 1 2) (sourceB912 + difference 2 1) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA912 + difference 1 2) (sourceB912 + difference 2 1) sourceC912) = raw15089 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15089; decide +kernel
    rw [ha]
    exact (canonical15089 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA912 + difference 1 3) (sourceB912 + difference 3 1) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA912 + difference 1 3) (sourceB912 + difference 3 1) sourceC912) = raw15090 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15090; decide +kernel
    rw [ha]
    exact (canonical15090 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA912 + difference 1 4) (sourceB912 + difference 4 1) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA912 + difference 1 4) (sourceB912 + difference 4 1) sourceC912) = raw15091 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15091; decide +kernel
    rw [ha]
    exact (canonical15091 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA912 + difference 1 5) (sourceB912 + difference 5 1) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3911) := by
    have ha : (tripleCharges (sourceA912 + difference 1 5) (sourceB912 + difference 5 1) sourceC912) = raw15092 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15092; decide +kernel
    rw [ha]
    exact (canonical15092 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA912 + difference 2 0) (sourceB912 + difference 0 2) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA912 + difference 2 0) (sourceB912 + difference 0 2) sourceC912) = raw15093 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15093; decide +kernel
    rw [ha]
    exact (canonical15093 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA912 + difference 2 1) (sourceB912 + difference 1 2) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA912 + difference 2 1) (sourceB912 + difference 1 2) sourceC912) = raw15094 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15094; decide +kernel
    rw [ha]
    exact (canonical15094 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA912 + difference 2 3) (sourceB912 + difference 3 2) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3821) := by
    have ha : (tripleCharges (sourceA912 + difference 2 3) (sourceB912 + difference 3 2) sourceC912) = raw15095 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15095; decide +kernel
    rw [ha]
    exact (canonical15095 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA912 + difference 2 4) (sourceB912 + difference 4 2) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA912 + difference 2 4) (sourceB912 + difference 4 2) sourceC912) = raw15096 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15096; decide +kernel
    rw [ha]
    exact (canonical15096 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA912 + difference 2 5) (sourceB912 + difference 5 2) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA912 + difference 2 5) (sourceB912 + difference 5 2) sourceC912) = raw15097 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15097; decide +kernel
    rw [ha]
    exact (canonical15097 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA912 + difference 3 0) (sourceB912 + difference 0 3) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA912 + difference 3 0) (sourceB912 + difference 0 3) sourceC912) = raw15098 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15098; decide +kernel
    rw [ha]
    exact (canonical15098 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA912 + difference 3 1) (sourceB912 + difference 1 3) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA912 + difference 3 1) (sourceB912 + difference 1 3) sourceC912) = raw15099 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15099; decide +kernel
    rw [ha]
    exact (canonical15099 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA912 + difference 3 2) (sourceB912 + difference 2 3) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA912 + difference 3 2) (sourceB912 + difference 2 3) sourceC912) = raw15100 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15100; decide +kernel
    rw [ha]
    exact (canonical15100 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA912 + difference 3 4) (sourceB912 + difference 4 3) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA912 + difference 3 4) (sourceB912 + difference 4 3) sourceC912) = raw15101 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15101; decide +kernel
    rw [ha]
    exact (canonical15101 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA912 + difference 3 5) (sourceB912 + difference 5 3) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA912 + difference 3 5) (sourceB912 + difference 5 3) sourceC912) = raw15102 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15102; decide +kernel
    rw [ha]
    exact (canonical15102 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA912 + difference 4 0) (sourceB912 + difference 0 4) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA912 + difference 4 0) (sourceB912 + difference 0 4) sourceC912) = raw15103 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15103; decide +kernel
    rw [ha]
    exact (canonical15103 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA912 + difference 4 1) (sourceB912 + difference 1 4) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA912 + difference 4 1) (sourceB912 + difference 1 4) sourceC912) = raw15104 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15104; decide +kernel
    rw [ha]
    exact (canonical15104 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA912 + difference 4 2) (sourceB912 + difference 2 4) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA912 + difference 4 2) (sourceB912 + difference 2 4) sourceC912) = raw15105 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15105; decide +kernel
    rw [ha]
    exact (canonical15105 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA912 + difference 4 3) (sourceB912 + difference 3 4) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3824) := by
    have ha : (tripleCharges (sourceA912 + difference 4 3) (sourceB912 + difference 3 4) sourceC912) = raw15106 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15106; decide +kernel
    rw [ha]
    exact (canonical15106 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA912 + difference 4 5) (sourceB912 + difference 5 4) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA912 + difference 4 5) (sourceB912 + difference 5 4) sourceC912) = raw15107 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15107; decide +kernel
    rw [ha]
    exact (canonical15107 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA912 + difference 5 0) (sourceB912 + difference 0 5) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA912 + difference 5 0) (sourceB912 + difference 0 5) sourceC912) = raw15108 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15108; decide +kernel
    rw [ha]
    exact (canonical15108 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA912 + difference 5 1) (sourceB912 + difference 1 5) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA912 + difference 5 1) (sourceB912 + difference 1 5) sourceC912) = raw15109 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15109; decide +kernel
    rw [ha]
    exact (canonical15109 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA912 + difference 5 2) (sourceB912 + difference 2 5) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA912 + difference 5 2) (sourceB912 + difference 2 5) sourceC912) = raw15110 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15110; decide +kernel
    rw [ha]
    exact (canonical15110 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA912 + difference 5 3) (sourceB912 + difference 3 5) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2594) := by
    have ha : (tripleCharges (sourceA912 + difference 5 3) (sourceB912 + difference 3 5) sourceC912) = raw15111 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15111; decide +kernel
    rw [ha]
    exact (canonical15111 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA912 + difference 5 4) (sourceB912 + difference 4 5) sourceC912) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA912 + difference 5 4) (sourceB912 + difference 4 5) sourceC912) = raw15112 := by
      apply Matrix.ext; unfold tripleCharges sourceA912 sourceB912 sourceC912 difference raw15112; decide +kernel
    rw [ha]
    exact (canonical15112 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA912 sourceB912 sourceC912
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm912, Integer.Sparse.eval]
  linarith only [hs]

def sourceA913 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceB913 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC913 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm913 : Integer.Sparse Master := [(Sum.inr 5256, 1), (Sum.inr 5258, 1), (Sum.inr 5260, 1), (Sum.inr 5271, 1), (Sum.inr 5289, 1), (Sum.inr 5405, 1), (Sum.inr 5406, 1), (Sum.inr 5409, 1), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5412, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5425, 1), (Sum.inr 5429, 1), (Sum.inr 5430, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5436, 1), (Sum.inr 5441, 1), (Sum.inr 5442, 1), (Sum.inr 5446, 1), (Sum.inr 5451, 1), (Sum.inr 5473, 1), (Sum.inr 5477, 1), (Sum.inr 5483, 1), (Sum.inr 5487, 1)]

theorem sourceEq913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm913 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA913 + difference 0 1) (sourceB913 + difference 1 0) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA913 + difference 0 1) (sourceB913 + difference 1 0) sourceC913) = raw15113 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15113; decide +kernel
    rw [ha]
    exact (canonical15113 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA913 + difference 0 2) (sourceB913 + difference 2 0) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA913 + difference 0 2) (sourceB913 + difference 2 0) sourceC913) = raw15114 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15114; decide +kernel
    rw [ha]
    exact (canonical15114 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA913 + difference 0 3) (sourceB913 + difference 3 0) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA913 + difference 0 3) (sourceB913 + difference 3 0) sourceC913) = raw15115 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15115; decide +kernel
    rw [ha]
    exact (canonical15115 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA913 + difference 0 4) (sourceB913 + difference 4 0) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA913 + difference 0 4) (sourceB913 + difference 4 0) sourceC913) = raw15116 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15116; decide +kernel
    rw [ha]
    exact (canonical15116 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA913 + difference 0 5) (sourceB913 + difference 5 0) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA913 + difference 0 5) (sourceB913 + difference 5 0) sourceC913) = raw15117 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15117; decide +kernel
    rw [ha]
    exact (canonical15117 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA913 + difference 1 0) (sourceB913 + difference 0 1) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA913 + difference 1 0) (sourceB913 + difference 0 1) sourceC913) = raw15118 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15118; decide +kernel
    rw [ha]
    exact (canonical15118 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA913 + difference 1 2) (sourceB913 + difference 2 1) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA913 + difference 1 2) (sourceB913 + difference 2 1) sourceC913) = raw15119 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15119; decide +kernel
    rw [ha]
    exact (canonical15119 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA913 + difference 1 3) (sourceB913 + difference 3 1) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA913 + difference 1 3) (sourceB913 + difference 3 1) sourceC913) = raw15120 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15120; decide +kernel
    rw [ha]
    exact (canonical15120 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA913 + difference 1 4) (sourceB913 + difference 4 1) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA913 + difference 1 4) (sourceB913 + difference 4 1) sourceC913) = raw15121 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15121; decide +kernel
    rw [ha]
    exact (canonical15121 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA913 + difference 1 5) (sourceB913 + difference 5 1) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA913 + difference 1 5) (sourceB913 + difference 5 1) sourceC913) = raw15122 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15122; decide +kernel
    rw [ha]
    exact (canonical15122 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA913 + difference 2 0) (sourceB913 + difference 0 2) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA913 + difference 2 0) (sourceB913 + difference 0 2) sourceC913) = raw15123 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15123; decide +kernel
    rw [ha]
    exact (canonical15123 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA913 + difference 2 1) (sourceB913 + difference 1 2) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA913 + difference 2 1) (sourceB913 + difference 1 2) sourceC913) = raw15124 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15124; decide +kernel
    rw [ha]
    exact (canonical15124 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA913 + difference 2 3) (sourceB913 + difference 3 2) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA913 + difference 2 3) (sourceB913 + difference 3 2) sourceC913) = raw15125 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15125; decide +kernel
    rw [ha]
    exact (canonical15125 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA913 + difference 2 4) (sourceB913 + difference 4 2) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA913 + difference 2 4) (sourceB913 + difference 4 2) sourceC913) = raw15126 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15126; decide +kernel
    rw [ha]
    exact (canonical15126 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA913 + difference 2 5) (sourceB913 + difference 5 2) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA913 + difference 2 5) (sourceB913 + difference 5 2) sourceC913) = raw15127 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15127; decide +kernel
    rw [ha]
    exact (canonical15127 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA913 + difference 3 0) (sourceB913 + difference 0 3) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA913 + difference 3 0) (sourceB913 + difference 0 3) sourceC913) = raw15128 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15128; decide +kernel
    rw [ha]
    exact (canonical15128 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA913 + difference 3 1) (sourceB913 + difference 1 3) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA913 + difference 3 1) (sourceB913 + difference 1 3) sourceC913) = raw15129 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15129; decide +kernel
    rw [ha]
    exact (canonical15129 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA913 + difference 3 2) (sourceB913 + difference 2 3) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA913 + difference 3 2) (sourceB913 + difference 2 3) sourceC913) = raw15130 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15130; decide +kernel
    rw [ha]
    exact (canonical15130 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA913 + difference 3 4) (sourceB913 + difference 4 3) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA913 + difference 3 4) (sourceB913 + difference 4 3) sourceC913) = raw15131 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15131; decide +kernel
    rw [ha]
    exact (canonical15131 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA913 + difference 3 5) (sourceB913 + difference 5 3) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA913 + difference 3 5) (sourceB913 + difference 5 3) sourceC913) = raw15132 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15132; decide +kernel
    rw [ha]
    exact (canonical15132 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA913 + difference 4 0) (sourceB913 + difference 0 4) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA913 + difference 4 0) (sourceB913 + difference 0 4) sourceC913) = raw15133 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15133; decide +kernel
    rw [ha]
    exact (canonical15133 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA913 + difference 4 1) (sourceB913 + difference 1 4) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA913 + difference 4 1) (sourceB913 + difference 1 4) sourceC913) = raw15134 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15134; decide +kernel
    rw [ha]
    exact (canonical15134 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA913 + difference 4 2) (sourceB913 + difference 2 4) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA913 + difference 4 2) (sourceB913 + difference 2 4) sourceC913) = raw14730 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw14730; decide +kernel
    rw [ha]
    exact (canonical14730 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA913 + difference 4 3) (sourceB913 + difference 3 4) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA913 + difference 4 3) (sourceB913 + difference 3 4) sourceC913) = raw14994 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw14994; decide +kernel
    rw [ha]
    exact (canonical14994 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA913 + difference 4 5) (sourceB913 + difference 5 4) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA913 + difference 4 5) (sourceB913 + difference 5 4) sourceC913) = raw14714 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw14714; decide +kernel
    rw [ha]
    exact (canonical14714 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA913 + difference 5 0) (sourceB913 + difference 0 5) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA913 + difference 5 0) (sourceB913 + difference 0 5) sourceC913) = raw15135 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15135; decide +kernel
    rw [ha]
    exact (canonical15135 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA913 + difference 5 1) (sourceB913 + difference 1 5) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA913 + difference 5 1) (sourceB913 + difference 1 5) sourceC913) = raw15136 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15136; decide +kernel
    rw [ha]
    exact (canonical15136 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA913 + difference 5 2) (sourceB913 + difference 2 5) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA913 + difference 5 2) (sourceB913 + difference 2 5) sourceC913) = raw15137 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15137; decide +kernel
    rw [ha]
    exact (canonical15137 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA913 + difference 5 3) (sourceB913 + difference 3 5) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA913 + difference 5 3) (sourceB913 + difference 3 5) sourceC913) = raw15138 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15138; decide +kernel
    rw [ha]
    exact (canonical15138 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA913 + difference 5 4) (sourceB913 + difference 4 5) sourceC913) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA913 + difference 5 4) (sourceB913 + difference 4 5) sourceC913) = raw15139 := by
      apply Matrix.ext; unfold tripleCharges sourceA913 sourceB913 sourceC913 difference raw15139; decide +kernel
    rw [ha]
    exact (canonical15139 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA913 sourceB913 sourceC913
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm913, Integer.Sparse.eval]
  linarith only [hs]

def sourceA914 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceB914 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC914 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm914 : Integer.Sparse Master := [(Sum.inr 3085, 1), (Sum.inr 3086, 1), (Sum.inr 3089, 1), (Sum.inr 3097, 1), (Sum.inr 3109, 1), (Sum.inr 3801, 1), (Sum.inr 3808, 1), (Sum.inr 3809, 1), (Sum.inr 3814, 1), (Sum.inr 3853, 1), (Sum.inr 3872, 1), (Sum.inr 3877, 1), (Sum.inr 3883, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3971, 1), (Sum.inr 3972, 1), (Sum.inr 3977, 1), (Sum.inr 3981, 1), (Sum.inr 3982, 1), (Sum.inr 3986, 1), (Sum.inr 3987, 1), (Sum.inr 3990, 1), (Sum.inr 3996, 1), (Sum.inr 4001, 1), (Sum.inr 4027, 1), (Sum.inr 4032, 1), (Sum.inr 4035, 1), (Sum.inr 4037, 1)]

theorem sourceEq914 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm914 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA914 + difference 0 1) (sourceB914 + difference 1 0) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA914 + difference 0 1) (sourceB914 + difference 1 0) sourceC914) = raw15140 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15140; decide +kernel
    rw [ha]
    exact (canonical15140 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA914 + difference 0 2) (sourceB914 + difference 2 0) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA914 + difference 0 2) (sourceB914 + difference 2 0) sourceC914) = raw15141 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15141; decide +kernel
    rw [ha]
    exact (canonical15141 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA914 + difference 0 3) (sourceB914 + difference 3 0) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3986) := by
    have ha : (tripleCharges (sourceA914 + difference 0 3) (sourceB914 + difference 3 0) sourceC914) = raw15142 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15142; decide +kernel
    rw [ha]
    exact (canonical15142 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA914 + difference 0 4) (sourceB914 + difference 4 0) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA914 + difference 0 4) (sourceB914 + difference 4 0) sourceC914) = raw15143 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15143; decide +kernel
    rw [ha]
    exact (canonical15143 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA914 + difference 0 5) (sourceB914 + difference 5 0) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA914 + difference 0 5) (sourceB914 + difference 5 0) sourceC914) = raw15144 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15144; decide +kernel
    rw [ha]
    exact (canonical15144 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA914 + difference 1 0) (sourceB914 + difference 0 1) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA914 + difference 1 0) (sourceB914 + difference 0 1) sourceC914) = raw15145 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15145; decide +kernel
    rw [ha]
    exact (canonical15145 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA914 + difference 1 2) (sourceB914 + difference 2 1) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA914 + difference 1 2) (sourceB914 + difference 2 1) sourceC914) = raw15146 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15146; decide +kernel
    rw [ha]
    exact (canonical15146 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA914 + difference 1 3) (sourceB914 + difference 3 1) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA914 + difference 1 3) (sourceB914 + difference 3 1) sourceC914) = raw15147 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15147; decide +kernel
    rw [ha]
    exact (canonical15147 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA914 + difference 1 4) (sourceB914 + difference 4 1) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA914 + difference 1 4) (sourceB914 + difference 4 1) sourceC914) = raw15148 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15148; decide +kernel
    rw [ha]
    exact (canonical15148 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA914 + difference 1 5) (sourceB914 + difference 5 1) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA914 + difference 1 5) (sourceB914 + difference 5 1) sourceC914) = raw15149 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15149; decide +kernel
    rw [ha]
    exact (canonical15149 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA914 + difference 2 0) (sourceB914 + difference 0 2) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA914 + difference 2 0) (sourceB914 + difference 0 2) sourceC914) = raw15150 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15150; decide +kernel
    rw [ha]
    exact (canonical15150 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA914 + difference 2 1) (sourceB914 + difference 1 2) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA914 + difference 2 1) (sourceB914 + difference 1 2) sourceC914) = raw15151 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15151; decide +kernel
    rw [ha]
    exact (canonical15151 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA914 + difference 2 3) (sourceB914 + difference 3 2) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA914 + difference 2 3) (sourceB914 + difference 3 2) sourceC914) = raw15152 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15152; decide +kernel
    rw [ha]
    exact (canonical15152 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA914 + difference 2 4) (sourceB914 + difference 4 2) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA914 + difference 2 4) (sourceB914 + difference 4 2) sourceC914) = raw15153 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15153; decide +kernel
    rw [ha]
    exact (canonical15153 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA914 + difference 2 5) (sourceB914 + difference 5 2) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA914 + difference 2 5) (sourceB914 + difference 5 2) sourceC914) = raw15154 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15154; decide +kernel
    rw [ha]
    exact (canonical15154 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA914 + difference 3 0) (sourceB914 + difference 0 3) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA914 + difference 3 0) (sourceB914 + difference 0 3) sourceC914) = raw15155 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15155; decide +kernel
    rw [ha]
    exact (canonical15155 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA914 + difference 3 1) (sourceB914 + difference 1 3) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA914 + difference 3 1) (sourceB914 + difference 1 3) sourceC914) = raw15156 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15156; decide +kernel
    rw [ha]
    exact (canonical15156 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA914 + difference 3 2) (sourceB914 + difference 2 3) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA914 + difference 3 2) (sourceB914 + difference 2 3) sourceC914) = raw15157 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15157; decide +kernel
    rw [ha]
    exact (canonical15157 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA914 + difference 3 4) (sourceB914 + difference 4 3) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA914 + difference 3 4) (sourceB914 + difference 4 3) sourceC914) = raw15158 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15158; decide +kernel
    rw [ha]
    exact (canonical15158 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA914 + difference 3 5) (sourceB914 + difference 5 3) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA914 + difference 3 5) (sourceB914 + difference 5 3) sourceC914) = raw15159 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15159; decide +kernel
    rw [ha]
    exact (canonical15159 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA914 + difference 4 0) (sourceB914 + difference 0 4) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA914 + difference 4 0) (sourceB914 + difference 0 4) sourceC914) = raw15160 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15160; decide +kernel
    rw [ha]
    exact (canonical15160 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA914 + difference 4 1) (sourceB914 + difference 1 4) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA914 + difference 4 1) (sourceB914 + difference 1 4) sourceC914) = raw15161 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15161; decide +kernel
    rw [ha]
    exact (canonical15161 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA914 + difference 4 2) (sourceB914 + difference 2 4) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA914 + difference 4 2) (sourceB914 + difference 2 4) sourceC914) = raw14790 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw14790; decide +kernel
    rw [ha]
    exact (canonical14790 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA914 + difference 4 3) (sourceB914 + difference 3 4) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA914 + difference 4 3) (sourceB914 + difference 3 4) sourceC914) = raw15016 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15016; decide +kernel
    rw [ha]
    exact (canonical15016 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA914 + difference 4 5) (sourceB914 + difference 5 4) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA914 + difference 4 5) (sourceB914 + difference 5 4) sourceC914) = raw14774 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw14774; decide +kernel
    rw [ha]
    exact (canonical14774 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA914 + difference 5 0) (sourceB914 + difference 0 5) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA914 + difference 5 0) (sourceB914 + difference 0 5) sourceC914) = raw15162 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15162; decide +kernel
    rw [ha]
    exact (canonical15162 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA914 + difference 5 1) (sourceB914 + difference 1 5) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4035) := by
    have ha : (tripleCharges (sourceA914 + difference 5 1) (sourceB914 + difference 1 5) sourceC914) = raw15163 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15163; decide +kernel
    rw [ha]
    exact (canonical15163 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA914 + difference 5 2) (sourceB914 + difference 2 5) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4032) := by
    have ha : (tripleCharges (sourceA914 + difference 5 2) (sourceB914 + difference 2 5) sourceC914) = raw15164 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15164; decide +kernel
    rw [ha]
    exact (canonical15164 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA914 + difference 5 3) (sourceB914 + difference 3 5) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4037) := by
    have ha : (tripleCharges (sourceA914 + difference 5 3) (sourceB914 + difference 3 5) sourceC914) = raw15165 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15165; decide +kernel
    rw [ha]
    exact (canonical15165 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA914 + difference 5 4) (sourceB914 + difference 4 5) sourceC914) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA914 + difference 5 4) (sourceB914 + difference 4 5) sourceC914) = raw15166 := by
      apply Matrix.ext; unfold tripleCharges sourceA914 sourceB914 sourceC914 difference raw15166; decide +kernel
    rw [ha]
    exact (canonical15166 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA914 sourceB914 sourceC914
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm914, Integer.Sparse.eval]
  linarith only [hs]

def sourceA915 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB915 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC915 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm915 : Integer.Sparse Master := [(Sum.inr 4805, 1), (Sum.inr 4807, 1), (Sum.inr 4810, 1), (Sum.inr 4839, 1), (Sum.inr 4889, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5172, 1), (Sum.inr 5294, 1), (Sum.inr 5354, 1), (Sum.inr 5355, 1), (Sum.inr 5370, 1), (Sum.inr 5378, 1), (Sum.inr 5387, 1), (Sum.inr 5397, 1), (Sum.inr 5406, 1), (Sum.inr 5417, 1), (Sum.inr 5431, 1), (Sum.inr 5432, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 2), (Sum.inr 5438, 1), (Sum.inr 5440, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 1), (Sum.inr 5453, 1), (Sum.inr 5454, 1), (Sum.inr 5490, 1)]

theorem sourceEq915 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm915 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA915 + difference 0 1) (sourceB915 + difference 1 0) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA915 + difference 0 1) (sourceB915 + difference 1 0) sourceC915) = raw15167 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15167; decide +kernel
    rw [ha]
    exact (canonical15167 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA915 + difference 0 2) (sourceB915 + difference 2 0) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA915 + difference 0 2) (sourceB915 + difference 2 0) sourceC915) = raw15168 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15168; decide +kernel
    rw [ha]
    exact (canonical15168 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA915 + difference 0 3) (sourceB915 + difference 3 0) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA915 + difference 0 3) (sourceB915 + difference 3 0) sourceC915) = raw15169 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15169; decide +kernel
    rw [ha]
    exact (canonical15169 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA915 + difference 0 4) (sourceB915 + difference 4 0) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA915 + difference 0 4) (sourceB915 + difference 4 0) sourceC915) = raw2661 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw2661; decide +kernel
    rw [ha]
    exact (canonical2661 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA915 + difference 0 5) (sourceB915 + difference 5 0) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA915 + difference 0 5) (sourceB915 + difference 5 0) sourceC915) = raw15170 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15170; decide +kernel
    rw [ha]
    exact (canonical15170 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA915 + difference 1 0) (sourceB915 + difference 0 1) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA915 + difference 1 0) (sourceB915 + difference 0 1) sourceC915) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA915 + difference 1 2) (sourceB915 + difference 2 1) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA915 + difference 1 2) (sourceB915 + difference 2 1) sourceC915) = raw2683 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw2683; decide +kernel
    rw [ha]
    exact (canonical2683 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA915 + difference 1 3) (sourceB915 + difference 3 1) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA915 + difference 1 3) (sourceB915 + difference 3 1) sourceC915) = raw2684 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw2684; decide +kernel
    rw [ha]
    exact (canonical2684 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA915 + difference 1 4) (sourceB915 + difference 4 1) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA915 + difference 1 4) (sourceB915 + difference 4 1) sourceC915) = raw4604 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw4604; decide +kernel
    rw [ha]
    exact (canonical4604 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA915 + difference 1 5) (sourceB915 + difference 5 1) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA915 + difference 1 5) (sourceB915 + difference 5 1) sourceC915) = raw2685 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw2685; decide +kernel
    rw [ha]
    exact (canonical2685 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA915 + difference 2 0) (sourceB915 + difference 0 2) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA915 + difference 2 0) (sourceB915 + difference 0 2) sourceC915) = raw7973 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw7973; decide +kernel
    rw [ha]
    exact (canonical7973 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA915 + difference 2 1) (sourceB915 + difference 1 2) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA915 + difference 2 1) (sourceB915 + difference 1 2) sourceC915) = raw15171 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15171; decide +kernel
    rw [ha]
    exact (canonical15171 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA915 + difference 2 3) (sourceB915 + difference 3 2) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA915 + difference 2 3) (sourceB915 + difference 3 2) sourceC915) = raw15172 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15172; decide +kernel
    rw [ha]
    exact (canonical15172 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA915 + difference 2 4) (sourceB915 + difference 4 2) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA915 + difference 2 4) (sourceB915 + difference 4 2) sourceC915) = raw2672 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw2672; decide +kernel
    rw [ha]
    exact (canonical2672 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA915 + difference 2 5) (sourceB915 + difference 5 2) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA915 + difference 2 5) (sourceB915 + difference 5 2) sourceC915) = raw15173 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15173; decide +kernel
    rw [ha]
    exact (canonical15173 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA915 + difference 3 0) (sourceB915 + difference 0 3) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA915 + difference 3 0) (sourceB915 + difference 0 3) sourceC915) = raw7977 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw7977; decide +kernel
    rw [ha]
    exact (canonical7977 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA915 + difference 3 1) (sourceB915 + difference 1 3) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA915 + difference 3 1) (sourceB915 + difference 1 3) sourceC915) = raw15174 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15174; decide +kernel
    rw [ha]
    exact (canonical15174 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA915 + difference 3 2) (sourceB915 + difference 2 3) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA915 + difference 3 2) (sourceB915 + difference 2 3) sourceC915) = raw15175 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15175; decide +kernel
    rw [ha]
    exact (canonical15175 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA915 + difference 3 4) (sourceB915 + difference 4 3) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA915 + difference 3 4) (sourceB915 + difference 4 3) sourceC915) = raw2677 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw2677; decide +kernel
    rw [ha]
    exact (canonical2677 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA915 + difference 3 5) (sourceB915 + difference 5 3) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA915 + difference 3 5) (sourceB915 + difference 5 3) sourceC915) = raw14053 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw14053; decide +kernel
    rw [ha]
    exact (canonical14053 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA915 + difference 4 0) (sourceB915 + difference 0 4) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA915 + difference 4 0) (sourceB915 + difference 0 4) sourceC915) = raw7981 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw7981; decide +kernel
    rw [ha]
    exact (canonical7981 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA915 + difference 4 1) (sourceB915 + difference 1 4) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA915 + difference 4 1) (sourceB915 + difference 1 4) sourceC915) = raw15176 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15176; decide +kernel
    rw [ha]
    exact (canonical15176 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA915 + difference 4 2) (sourceB915 + difference 2 4) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA915 + difference 4 2) (sourceB915 + difference 2 4) sourceC915) = raw15177 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15177; decide +kernel
    rw [ha]
    exact (canonical15177 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA915 + difference 4 3) (sourceB915 + difference 3 4) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA915 + difference 4 3) (sourceB915 + difference 3 4) sourceC915) = raw15178 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15178; decide +kernel
    rw [ha]
    exact (canonical15178 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA915 + difference 4 5) (sourceB915 + difference 5 4) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA915 + difference 4 5) (sourceB915 + difference 5 4) sourceC915) = raw15179 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15179; decide +kernel
    rw [ha]
    exact (canonical15179 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA915 + difference 5 0) (sourceB915 + difference 0 5) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA915 + difference 5 0) (sourceB915 + difference 0 5) sourceC915) = raw4618 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw4618; decide +kernel
    rw [ha]
    exact (canonical4618 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA915 + difference 5 1) (sourceB915 + difference 1 5) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA915 + difference 5 1) (sourceB915 + difference 1 5) sourceC915) = raw15180 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15180; decide +kernel
    rw [ha]
    exact (canonical15180 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA915 + difference 5 2) (sourceB915 + difference 2 5) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA915 + difference 5 2) (sourceB915 + difference 2 5) sourceC915) = raw15181 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15181; decide +kernel
    rw [ha]
    exact (canonical15181 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA915 + difference 5 3) (sourceB915 + difference 3 5) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA915 + difference 5 3) (sourceB915 + difference 3 5) sourceC915) = raw15182 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw15182; decide +kernel
    rw [ha]
    exact (canonical15182 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA915 + difference 5 4) (sourceB915 + difference 4 5) sourceC915) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA915 + difference 5 4) (sourceB915 + difference 4 5) sourceC915) = raw2687 := by
      apply Matrix.ext; unfold tripleCharges sourceA915 sourceB915 sourceC915 difference raw2687; decide +kernel
    rw [ha]
    exact (canonical2687 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA915 sourceB915 sourceC915
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm915, Integer.Sparse.eval]
  linarith only [hs]

def sourceA916 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB916 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC916 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm916 : Integer.Sparse Master := [(Sum.inr 2023, 1), (Sum.inr 2025, 1), (Sum.inr 2028, 1), (Sum.inr 2058, 1), (Sum.inr 2245, 1), (Sum.inr 2924, 1), (Sum.inr 2931, 1), (Sum.inr 2959, 1), (Sum.inr 3101, 1), (Sum.inr 3692, 1), (Sum.inr 3693, 1), (Sum.inr 3706, 1), (Sum.inr 3719, 1), (Sum.inr 3736, 1), (Sum.inr 3782, 1), (Sum.inr 3801, 1), (Sum.inr 3823, 1), (Sum.inr 3849, 1), (Sum.inr 3850, 1), (Sum.inr 3853, 2), (Sum.inr 3857, 1), (Sum.inr 3862, 1), (Sum.inr 3910, 1), (Sum.inr 3912, 1), (Sum.inr 3982, 1), (Sum.inr 4013, 1), (Sum.inr 4033, 1), (Sum.inr 4036, 1), (Sum.inr 4040, 1)]

theorem sourceEq916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm916 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA916 + difference 0 1) (sourceB916 + difference 1 0) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA916 + difference 0 1) (sourceB916 + difference 1 0) sourceC916) = raw15183 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15183; decide +kernel
    rw [ha]
    exact (canonical15183 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA916 + difference 0 2) (sourceB916 + difference 2 0) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA916 + difference 0 2) (sourceB916 + difference 2 0) sourceC916) = raw15184 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15184; decide +kernel
    rw [ha]
    exact (canonical15184 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA916 + difference 0 3) (sourceB916 + difference 3 0) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA916 + difference 0 3) (sourceB916 + difference 3 0) sourceC916) = raw15185 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15185; decide +kernel
    rw [ha]
    exact (canonical15185 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA916 + difference 0 4) (sourceB916 + difference 4 0) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA916 + difference 0 4) (sourceB916 + difference 4 0) sourceC916) = raw2691 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw2691; decide +kernel
    rw [ha]
    exact (canonical2691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA916 + difference 0 5) (sourceB916 + difference 5 0) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA916 + difference 0 5) (sourceB916 + difference 5 0) sourceC916) = raw15186 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15186; decide +kernel
    rw [ha]
    exact (canonical15186 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA916 + difference 1 0) (sourceB916 + difference 0 1) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA916 + difference 1 0) (sourceB916 + difference 0 1) sourceC916) = raw2711 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw2711; decide +kernel
    rw [ha]
    exact (canonical2711 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA916 + difference 1 2) (sourceB916 + difference 2 1) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA916 + difference 1 2) (sourceB916 + difference 2 1) sourceC916) = raw2713 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw2713; decide +kernel
    rw [ha]
    exact (canonical2713 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA916 + difference 1 3) (sourceB916 + difference 3 1) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA916 + difference 1 3) (sourceB916 + difference 3 1) sourceC916) = raw2714 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw2714; decide +kernel
    rw [ha]
    exact (canonical2714 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA916 + difference 1 4) (sourceB916 + difference 4 1) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA916 + difference 1 4) (sourceB916 + difference 4 1) sourceC916) = raw4626 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw4626; decide +kernel
    rw [ha]
    exact (canonical4626 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA916 + difference 1 5) (sourceB916 + difference 5 1) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA916 + difference 1 5) (sourceB916 + difference 5 1) sourceC916) = raw2715 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw2715; decide +kernel
    rw [ha]
    exact (canonical2715 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA916 + difference 2 0) (sourceB916 + difference 0 2) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA916 + difference 2 0) (sourceB916 + difference 0 2) sourceC916) = raw7990 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw7990; decide +kernel
    rw [ha]
    exact (canonical7990 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA916 + difference 2 1) (sourceB916 + difference 1 2) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA916 + difference 2 1) (sourceB916 + difference 1 2) sourceC916) = raw15187 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15187; decide +kernel
    rw [ha]
    exact (canonical15187 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA916 + difference 2 3) (sourceB916 + difference 3 2) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA916 + difference 2 3) (sourceB916 + difference 3 2) sourceC916) = raw15188 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15188; decide +kernel
    rw [ha]
    exact (canonical15188 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA916 + difference 2 4) (sourceB916 + difference 4 2) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA916 + difference 2 4) (sourceB916 + difference 4 2) sourceC916) = raw2702 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw2702; decide +kernel
    rw [ha]
    exact (canonical2702 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA916 + difference 2 5) (sourceB916 + difference 5 2) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA916 + difference 2 5) (sourceB916 + difference 5 2) sourceC916) = raw15189 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15189; decide +kernel
    rw [ha]
    exact (canonical15189 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA916 + difference 3 0) (sourceB916 + difference 0 3) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA916 + difference 3 0) (sourceB916 + difference 0 3) sourceC916) = raw7994 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw7994; decide +kernel
    rw [ha]
    exact (canonical7994 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA916 + difference 3 1) (sourceB916 + difference 1 3) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3736) := by
    have ha : (tripleCharges (sourceA916 + difference 3 1) (sourceB916 + difference 1 3) sourceC916) = raw15190 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15190; decide +kernel
    rw [ha]
    exact (canonical15190 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA916 + difference 3 2) (sourceB916 + difference 2 3) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3823) := by
    have ha : (tripleCharges (sourceA916 + difference 3 2) (sourceB916 + difference 2 3) sourceC916) = raw15191 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15191; decide +kernel
    rw [ha]
    exact (canonical15191 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA916 + difference 3 4) (sourceB916 + difference 4 3) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA916 + difference 3 4) (sourceB916 + difference 4 3) sourceC916) = raw2707 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw2707; decide +kernel
    rw [ha]
    exact (canonical2707 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA916 + difference 3 5) (sourceB916 + difference 5 3) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4036) := by
    have ha : (tripleCharges (sourceA916 + difference 3 5) (sourceB916 + difference 5 3) sourceC916) = raw15192 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15192; decide +kernel
    rw [ha]
    exact (canonical15192 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA916 + difference 4 0) (sourceB916 + difference 0 4) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA916 + difference 4 0) (sourceB916 + difference 0 4) sourceC916) = raw7998 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw7998; decide +kernel
    rw [ha]
    exact (canonical7998 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA916 + difference 4 1) (sourceB916 + difference 1 4) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA916 + difference 4 1) (sourceB916 + difference 1 4) sourceC916) = raw15193 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15193; decide +kernel
    rw [ha]
    exact (canonical15193 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA916 + difference 4 2) (sourceB916 + difference 2 4) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA916 + difference 4 2) (sourceB916 + difference 2 4) sourceC916) = raw15194 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15194; decide +kernel
    rw [ha]
    exact (canonical15194 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA916 + difference 4 3) (sourceB916 + difference 3 4) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA916 + difference 4 3) (sourceB916 + difference 3 4) sourceC916) = raw15195 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15195; decide +kernel
    rw [ha]
    exact (canonical15195 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA916 + difference 4 5) (sourceB916 + difference 5 4) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA916 + difference 4 5) (sourceB916 + difference 5 4) sourceC916) = raw15196 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15196; decide +kernel
    rw [ha]
    exact (canonical15196 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA916 + difference 5 0) (sourceB916 + difference 0 5) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA916 + difference 5 0) (sourceB916 + difference 0 5) sourceC916) = raw4640 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw4640; decide +kernel
    rw [ha]
    exact (canonical4640 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA916 + difference 5 1) (sourceB916 + difference 1 5) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA916 + difference 5 1) (sourceB916 + difference 1 5) sourceC916) = raw15197 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15197; decide +kernel
    rw [ha]
    exact (canonical15197 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA916 + difference 5 2) (sourceB916 + difference 2 5) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA916 + difference 5 2) (sourceB916 + difference 2 5) sourceC916) = raw15198 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15198; decide +kernel
    rw [ha]
    exact (canonical15198 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA916 + difference 5 3) (sourceB916 + difference 3 5) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA916 + difference 5 3) (sourceB916 + difference 3 5) sourceC916) = raw15199 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw15199; decide +kernel
    rw [ha]
    exact (canonical15199 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA916 + difference 5 4) (sourceB916 + difference 4 5) sourceC916) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA916 + difference 5 4) (sourceB916 + difference 4 5) sourceC916) = raw2717 := by
      apply Matrix.ext; unfold tripleCharges sourceA916 sourceB916 sourceC916 difference raw2717; decide +kernel
    rw [ha]
    exact (canonical2717 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA916 sourceB916 sourceC916
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm916, Integer.Sparse.eval]
  linarith only [hs]

def sourceA917 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceB917 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC917 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm917 : Integer.Sparse Master := [(Sum.inr 5265, 2), (Sum.inr 5266, 2), (Sum.inr 5267, 2), (Sum.inr 5271, 2), (Sum.inr 5299, 2), (Sum.inr 5406, 2), (Sum.inr 5410, 2), (Sum.inr 5411, 2), (Sum.inr 5412, 2), (Sum.inr 5424, 2), (Sum.inr 5425, 2), (Sum.inr 5426, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 1), (Sum.inr 5442, 2), (Sum.inr 5443, 2)]

theorem sourceEq917 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm917 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA917 + difference 0 1) (sourceB917 + difference 1 0) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA917 + difference 0 1) (sourceB917 + difference 1 0) sourceC917) = raw15200 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15200; decide +kernel
    rw [ha]
    exact (canonical15200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA917 + difference 0 2) (sourceB917 + difference 2 0) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA917 + difference 0 2) (sourceB917 + difference 2 0) sourceC917) = raw14704 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14704; decide +kernel
    rw [ha]
    exact (canonical14704 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA917 + difference 0 3) (sourceB917 + difference 3 0) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA917 + difference 0 3) (sourceB917 + difference 3 0) sourceC917) = raw14975 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14975; decide +kernel
    rw [ha]
    exact (canonical14975 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA917 + difference 0 4) (sourceB917 + difference 4 0) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA917 + difference 0 4) (sourceB917 + difference 4 0) sourceC917) = raw15117 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15117; decide +kernel
    rw [ha]
    exact (canonical15117 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA917 + difference 0 5) (sourceB917 + difference 5 0) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA917 + difference 0 5) (sourceB917 + difference 5 0) sourceC917) = raw15201 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15201; decide +kernel
    rw [ha]
    exact (canonical15201 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA917 + difference 1 0) (sourceB917 + difference 0 1) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA917 + difference 1 0) (sourceB917 + difference 0 1) sourceC917) = raw15202 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15202; decide +kernel
    rw [ha]
    exact (canonical15202 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA917 + difference 1 2) (sourceB917 + difference 2 1) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA917 + difference 1 2) (sourceB917 + difference 2 1) sourceC917) = raw14709 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14709; decide +kernel
    rw [ha]
    exact (canonical14709 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA917 + difference 1 3) (sourceB917 + difference 3 1) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA917 + difference 1 3) (sourceB917 + difference 3 1) sourceC917) = raw14979 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14979; decide +kernel
    rw [ha]
    exact (canonical14979 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA917 + difference 1 4) (sourceB917 + difference 4 1) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA917 + difference 1 4) (sourceB917 + difference 4 1) sourceC917) = raw15122 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15122; decide +kernel
    rw [ha]
    exact (canonical15122 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA917 + difference 1 5) (sourceB917 + difference 5 1) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA917 + difference 1 5) (sourceB917 + difference 5 1) sourceC917) = raw15203 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15203; decide +kernel
    rw [ha]
    exact (canonical15203 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA917 + difference 2 0) (sourceB917 + difference 0 2) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA917 + difference 2 0) (sourceB917 + difference 0 2) sourceC917) = raw15204 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15204; decide +kernel
    rw [ha]
    exact (canonical15204 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA917 + difference 2 1) (sourceB917 + difference 1 2) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA917 + difference 2 1) (sourceB917 + difference 1 2) sourceC917) = raw15205 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15205; decide +kernel
    rw [ha]
    exact (canonical15205 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA917 + difference 2 3) (sourceB917 + difference 3 2) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA917 + difference 2 3) (sourceB917 + difference 3 2) sourceC917) = raw14984 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14984; decide +kernel
    rw [ha]
    exact (canonical14984 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA917 + difference 2 4) (sourceB917 + difference 4 2) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA917 + difference 2 4) (sourceB917 + difference 4 2) sourceC917) = raw15127 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15127; decide +kernel
    rw [ha]
    exact (canonical15127 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA917 + difference 2 5) (sourceB917 + difference 5 2) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA917 + difference 2 5) (sourceB917 + difference 5 2) sourceC917) = raw15206 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15206; decide +kernel
    rw [ha]
    exact (canonical15206 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA917 + difference 3 0) (sourceB917 + difference 0 3) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA917 + difference 3 0) (sourceB917 + difference 0 3) sourceC917) = raw15207 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15207; decide +kernel
    rw [ha]
    exact (canonical15207 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA917 + difference 3 1) (sourceB917 + difference 1 3) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA917 + difference 3 1) (sourceB917 + difference 1 3) sourceC917) = raw15208 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15208; decide +kernel
    rw [ha]
    exact (canonical15208 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA917 + difference 3 2) (sourceB917 + difference 2 3) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5426) := by
    have ha : (tripleCharges (sourceA917 + difference 3 2) (sourceB917 + difference 2 3) sourceC917) = raw14719 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14719; decide +kernel
    rw [ha]
    exact (canonical14719 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA917 + difference 3 4) (sourceB917 + difference 4 3) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA917 + difference 3 4) (sourceB917 + difference 4 3) sourceC917) = raw15132 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15132; decide +kernel
    rw [ha]
    exact (canonical15132 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA917 + difference 3 5) (sourceB917 + difference 5 3) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA917 + difference 3 5) (sourceB917 + difference 5 3) sourceC917) = raw15209 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15209; decide +kernel
    rw [ha]
    exact (canonical15209 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA917 + difference 4 0) (sourceB917 + difference 0 4) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA917 + difference 4 0) (sourceB917 + difference 0 4) sourceC917) = raw14711 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14711; decide +kernel
    rw [ha]
    exact (canonical14711 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA917 + difference 4 1) (sourceB917 + difference 1 4) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA917 + difference 4 1) (sourceB917 + difference 1 4) sourceC917) = raw14712 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14712; decide +kernel
    rw [ha]
    exact (canonical14712 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA917 + difference 4 2) (sourceB917 + difference 2 4) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA917 + difference 4 2) (sourceB917 + difference 2 4) sourceC917) = raw14986 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14986; decide +kernel
    rw [ha]
    exact (canonical14986 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA917 + difference 4 3) (sourceB917 + difference 3 4) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA917 + difference 4 3) (sourceB917 + difference 3 4) sourceC917) = raw14713 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14713; decide +kernel
    rw [ha]
    exact (canonical14713 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA917 + difference 4 5) (sourceB917 + difference 5 4) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA917 + difference 4 5) (sourceB917 + difference 5 4) sourceC917) = raw14715 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14715; decide +kernel
    rw [ha]
    exact (canonical14715 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA917 + difference 5 0) (sourceB917 + difference 0 5) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA917 + difference 5 0) (sourceB917 + difference 0 5) sourceC917) = raw15133 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15133; decide +kernel
    rw [ha]
    exact (canonical15133 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA917 + difference 5 1) (sourceB917 + difference 1 5) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA917 + difference 5 1) (sourceB917 + difference 1 5) sourceC917) = raw15134 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15134; decide +kernel
    rw [ha]
    exact (canonical15134 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA917 + difference 5 2) (sourceB917 + difference 2 5) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA917 + difference 5 2) (sourceB917 + difference 2 5) sourceC917) = raw14730 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14730; decide +kernel
    rw [ha]
    exact (canonical14730 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA917 + difference 5 3) (sourceB917 + difference 3 5) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA917 + difference 5 3) (sourceB917 + difference 3 5) sourceC917) = raw14994 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw14994; decide +kernel
    rw [ha]
    exact (canonical14994 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA917 + difference 5 4) (sourceB917 + difference 4 5) sourceC917) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA917 + difference 5 4) (sourceB917 + difference 4 5) sourceC917) = raw15210 := by
      apply Matrix.ext; unfold tripleCharges sourceA917 sourceB917 sourceC917 difference raw15210; decide +kernel
    rw [ha]
    exact (canonical15210 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA917 sourceB917 sourceC917
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm917, Integer.Sparse.eval]
  linarith only [hs]

def sourceA918 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB918 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC918 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm918 : Integer.Sparse Master := [(Sum.inr 5007, 2), (Sum.inr 5008, 2), (Sum.inr 5009, 2), (Sum.inr 5019, 2), (Sum.inr 5153, 2), (Sum.inr 5164, 2), (Sum.inr 5267, 2), (Sum.inr 5300, 2), (Sum.inr 5375, 1), (Sum.inr 5385, 2), (Sum.inr 5414, 2), (Sum.inr 5425, 2), (Sum.inr 5428, 2), (Sum.inr 5436, 1), (Sum.inr 5438, 2), (Sum.inr 5443, 2)]

theorem sourceEq918 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm918 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA918 + difference 0 1) (sourceB918 + difference 1 0) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA918 + difference 0 1) (sourceB918 + difference 1 0) sourceC918) = raw15211 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15211; decide +kernel
    rw [ha]
    exact (canonical15211 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA918 + difference 0 2) (sourceB918 + difference 2 0) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA918 + difference 0 2) (sourceB918 + difference 2 0) sourceC918) = raw15212 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15212; decide +kernel
    rw [ha]
    exact (canonical15212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA918 + difference 0 3) (sourceB918 + difference 3 0) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA918 + difference 0 3) (sourceB918 + difference 3 0) sourceC918) = raw15213 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15213; decide +kernel
    rw [ha]
    exact (canonical15213 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA918 + difference 0 4) (sourceB918 + difference 4 0) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA918 + difference 0 4) (sourceB918 + difference 4 0) sourceC918) = raw15214 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15214; decide +kernel
    rw [ha]
    exact (canonical15214 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA918 + difference 0 5) (sourceB918 + difference 5 0) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA918 + difference 0 5) (sourceB918 + difference 5 0) sourceC918) = raw15215 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15215; decide +kernel
    rw [ha]
    exact (canonical15215 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA918 + difference 1 0) (sourceB918 + difference 0 1) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA918 + difference 1 0) (sourceB918 + difference 0 1) sourceC918) = raw15216 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15216; decide +kernel
    rw [ha]
    exact (canonical15216 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA918 + difference 1 2) (sourceB918 + difference 2 1) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA918 + difference 1 2) (sourceB918 + difference 2 1) sourceC918) = raw8327 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw8327; decide +kernel
    rw [ha]
    exact (canonical8327 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA918 + difference 1 3) (sourceB918 + difference 3 1) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA918 + difference 1 3) (sourceB918 + difference 3 1) sourceC918) = raw8328 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw8328; decide +kernel
    rw [ha]
    exact (canonical8328 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA918 + difference 1 4) (sourceB918 + difference 4 1) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA918 + difference 1 4) (sourceB918 + difference 4 1) sourceC918) = raw8329 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw8329; decide +kernel
    rw [ha]
    exact (canonical8329 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA918 + difference 1 5) (sourceB918 + difference 5 1) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA918 + difference 1 5) (sourceB918 + difference 5 1) sourceC918) = raw8330 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw8330; decide +kernel
    rw [ha]
    exact (canonical8330 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA918 + difference 2 0) (sourceB918 + difference 0 2) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA918 + difference 2 0) (sourceB918 + difference 0 2) sourceC918) = raw8337 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw8337; decide +kernel
    rw [ha]
    exact (canonical8337 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA918 + difference 2 1) (sourceB918 + difference 1 2) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5375) := by
    have ha : (tripleCharges (sourceA918 + difference 2 1) (sourceB918 + difference 1 2) sourceC918) = raw15217 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15217; decide +kernel
    rw [ha]
    exact (canonical15217 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA918 + difference 2 3) (sourceB918 + difference 3 2) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA918 + difference 2 3) (sourceB918 + difference 3 2) sourceC918) = raw15218 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15218; decide +kernel
    rw [ha]
    exact (canonical15218 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA918 + difference 2 4) (sourceB918 + difference 4 2) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA918 + difference 2 4) (sourceB918 + difference 4 2) sourceC918) = raw15219 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15219; decide +kernel
    rw [ha]
    exact (canonical15219 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA918 + difference 2 5) (sourceB918 + difference 5 2) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA918 + difference 2 5) (sourceB918 + difference 5 2) sourceC918) = raw15220 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15220; decide +kernel
    rw [ha]
    exact (canonical15220 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA918 + difference 3 0) (sourceB918 + difference 0 3) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA918 + difference 3 0) (sourceB918 + difference 0 3) sourceC918) = raw8342 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw8342; decide +kernel
    rw [ha]
    exact (canonical8342 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA918 + difference 3 1) (sourceB918 + difference 1 3) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA918 + difference 3 1) (sourceB918 + difference 1 3) sourceC918) = raw15221 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15221; decide +kernel
    rw [ha]
    exact (canonical15221 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA918 + difference 3 2) (sourceB918 + difference 2 3) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA918 + difference 3 2) (sourceB918 + difference 2 3) sourceC918) = raw15222 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15222; decide +kernel
    rw [ha]
    exact (canonical15222 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA918 + difference 3 4) (sourceB918 + difference 4 3) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA918 + difference 3 4) (sourceB918 + difference 4 3) sourceC918) = raw15223 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15223; decide +kernel
    rw [ha]
    exact (canonical15223 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA918 + difference 3 5) (sourceB918 + difference 5 3) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA918 + difference 3 5) (sourceB918 + difference 5 3) sourceC918) = raw15224 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15224; decide +kernel
    rw [ha]
    exact (canonical15224 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA918 + difference 4 0) (sourceB918 + difference 0 4) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5019) := by
    have ha : (tripleCharges (sourceA918 + difference 4 0) (sourceB918 + difference 0 4) sourceC918) = raw8347 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw8347; decide +kernel
    rw [ha]
    exact (canonical8347 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA918 + difference 4 1) (sourceB918 + difference 1 4) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5009) := by
    have ha : (tripleCharges (sourceA918 + difference 4 1) (sourceB918 + difference 1 4) sourceC918) = raw15225 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15225; decide +kernel
    rw [ha]
    exact (canonical15225 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA918 + difference 4 2) (sourceB918 + difference 2 4) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5007) := by
    have ha : (tripleCharges (sourceA918 + difference 4 2) (sourceB918 + difference 2 4) sourceC918) = raw15226 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15226; decide +kernel
    rw [ha]
    exact (canonical15226 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA918 + difference 4 3) (sourceB918 + difference 3 4) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5008) := by
    have ha : (tripleCharges (sourceA918 + difference 4 3) (sourceB918 + difference 3 4) sourceC918) = raw15227 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15227; decide +kernel
    rw [ha]
    exact (canonical15227 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA918 + difference 4 5) (sourceB918 + difference 5 4) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA918 + difference 4 5) (sourceB918 + difference 5 4) sourceC918) = raw15228 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15228; decide +kernel
    rw [ha]
    exact (canonical15228 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA918 + difference 5 0) (sourceB918 + difference 0 5) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5008) := by
    have ha : (tripleCharges (sourceA918 + difference 5 0) (sourceB918 + difference 0 5) sourceC918) = raw8352 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw8352; decide +kernel
    rw [ha]
    exact (canonical8352 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA918 + difference 5 1) (sourceB918 + difference 1 5) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5009) := by
    have ha : (tripleCharges (sourceA918 + difference 5 1) (sourceB918 + difference 1 5) sourceC918) = raw15229 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15229; decide +kernel
    rw [ha]
    exact (canonical15229 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA918 + difference 5 2) (sourceB918 + difference 2 5) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5007) := by
    have ha : (tripleCharges (sourceA918 + difference 5 2) (sourceB918 + difference 2 5) sourceC918) = raw15230 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15230; decide +kernel
    rw [ha]
    exact (canonical15230 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA918 + difference 5 3) (sourceB918 + difference 3 5) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5019) := by
    have ha : (tripleCharges (sourceA918 + difference 5 3) (sourceB918 + difference 3 5) sourceC918) = raw15231 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15231; decide +kernel
    rw [ha]
    exact (canonical15231 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA918 + difference 5 4) (sourceB918 + difference 4 5) sourceC918) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA918 + difference 5 4) (sourceB918 + difference 4 5) sourceC918) = raw15232 := by
      apply Matrix.ext; unfold tripleCharges sourceA918 sourceB918 sourceC918 difference raw15232; decide +kernel
    rw [ha]
    exact (canonical15232 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA918 sourceB918 sourceC918
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm918, Integer.Sparse.eval]
  linarith only [hs]

def sourceA919 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB919 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC919 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm919 : Integer.Sparse Master := [(Sum.inr 2392, 1), (Sum.inr 2393, 1), (Sum.inr 2394, 1), (Sum.inr 2405, 1), (Sum.inr 2732, 1), (Sum.inr 2909, 1), (Sum.inr 2910, 1), (Sum.inr 2955, 1), (Sum.inr 3055, 1), (Sum.inr 3347, 1), (Sum.inr 3348, 1), (Sum.inr 3358, 1), (Sum.inr 3541, 1), (Sum.inr 3559, 1), (Sum.inr 3565, 1), (Sum.inr 3584, 1), (Sum.inr 3714, 1), (Sum.inr 3733, 1), (Sum.inr 3839, 1), (Sum.inr 3845, 1), (Sum.inr 3862, 1), (Sum.inr 3868, 1), (Sum.inr 3869, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3889, 1), (Sum.inr 3949, 1), (Sum.inr 3993, 1), (Sum.inr 4003, 1)]

theorem sourceEq919 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm919 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA919 + difference 0 1) (sourceB919 + difference 1 0) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA919 + difference 0 1) (sourceB919 + difference 1 0) sourceC919) = raw15233 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15233; decide +kernel
    rw [ha]
    exact (canonical15233 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA919 + difference 0 2) (sourceB919 + difference 2 0) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA919 + difference 0 2) (sourceB919 + difference 2 0) sourceC919) = raw15234 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15234; decide +kernel
    rw [ha]
    exact (canonical15234 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA919 + difference 0 3) (sourceB919 + difference 3 0) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA919 + difference 0 3) (sourceB919 + difference 3 0) sourceC919) = raw15235 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15235; decide +kernel
    rw [ha]
    exact (canonical15235 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA919 + difference 0 4) (sourceB919 + difference 4 0) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA919 + difference 0 4) (sourceB919 + difference 4 0) sourceC919) = raw15236 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15236; decide +kernel
    rw [ha]
    exact (canonical15236 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA919 + difference 0 5) (sourceB919 + difference 5 0) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA919 + difference 0 5) (sourceB919 + difference 5 0) sourceC919) = raw15237 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15237; decide +kernel
    rw [ha]
    exact (canonical15237 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA919 + difference 1 0) (sourceB919 + difference 0 1) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA919 + difference 1 0) (sourceB919 + difference 0 1) sourceC919) = raw15238 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15238; decide +kernel
    rw [ha]
    exact (canonical15238 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA919 + difference 1 2) (sourceB919 + difference 2 1) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA919 + difference 1 2) (sourceB919 + difference 2 1) sourceC919) = raw8357 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw8357; decide +kernel
    rw [ha]
    exact (canonical8357 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA919 + difference 1 3) (sourceB919 + difference 3 1) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA919 + difference 1 3) (sourceB919 + difference 3 1) sourceC919) = raw8358 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw8358; decide +kernel
    rw [ha]
    exact (canonical8358 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA919 + difference 1 4) (sourceB919 + difference 4 1) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA919 + difference 1 4) (sourceB919 + difference 4 1) sourceC919) = raw8359 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw8359; decide +kernel
    rw [ha]
    exact (canonical8359 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA919 + difference 1 5) (sourceB919 + difference 5 1) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA919 + difference 1 5) (sourceB919 + difference 5 1) sourceC919) = raw8360 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw8360; decide +kernel
    rw [ha]
    exact (canonical8360 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA919 + difference 2 0) (sourceB919 + difference 0 2) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2909) := by
    have ha : (tripleCharges (sourceA919 + difference 2 0) (sourceB919 + difference 0 2) sourceC919) = raw8367 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw8367; decide +kernel
    rw [ha]
    exact (canonical8367 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA919 + difference 2 1) (sourceB919 + difference 1 2) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3714) := by
    have ha : (tripleCharges (sourceA919 + difference 2 1) (sourceB919 + difference 1 2) sourceC919) = raw15239 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15239; decide +kernel
    rw [ha]
    exact (canonical15239 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA919 + difference 2 3) (sourceB919 + difference 3 2) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3559) := by
    have ha : (tripleCharges (sourceA919 + difference 2 3) (sourceB919 + difference 3 2) sourceC919) = raw15240 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15240; decide +kernel
    rw [ha]
    exact (canonical15240 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA919 + difference 2 4) (sourceB919 + difference 4 2) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA919 + difference 2 4) (sourceB919 + difference 4 2) sourceC919) = raw15241 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15241; decide +kernel
    rw [ha]
    exact (canonical15241 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA919 + difference 2 5) (sourceB919 + difference 5 2) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA919 + difference 2 5) (sourceB919 + difference 5 2) sourceC919) = raw15242 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15242; decide +kernel
    rw [ha]
    exact (canonical15242 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA919 + difference 3 0) (sourceB919 + difference 0 3) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA919 + difference 3 0) (sourceB919 + difference 0 3) sourceC919) = raw8372 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw8372; decide +kernel
    rw [ha]
    exact (canonical8372 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA919 + difference 3 1) (sourceB919 + difference 1 3) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA919 + difference 3 1) (sourceB919 + difference 1 3) sourceC919) = raw15243 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15243; decide +kernel
    rw [ha]
    exact (canonical15243 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA919 + difference 3 2) (sourceB919 + difference 2 3) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA919 + difference 3 2) (sourceB919 + difference 2 3) sourceC919) = raw15244 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15244; decide +kernel
    rw [ha]
    exact (canonical15244 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA919 + difference 3 4) (sourceB919 + difference 4 3) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA919 + difference 3 4) (sourceB919 + difference 4 3) sourceC919) = raw15245 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15245; decide +kernel
    rw [ha]
    exact (canonical15245 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA919 + difference 3 5) (sourceB919 + difference 5 3) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA919 + difference 3 5) (sourceB919 + difference 5 3) sourceC919) = raw15246 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15246; decide +kernel
    rw [ha]
    exact (canonical15246 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA919 + difference 4 0) (sourceB919 + difference 0 4) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2910) := by
    have ha : (tripleCharges (sourceA919 + difference 4 0) (sourceB919 + difference 0 4) sourceC919) = raw8377 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw8377; decide +kernel
    rw [ha]
    exact (canonical8377 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA919 + difference 4 1) (sourceB919 + difference 1 4) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3348) := by
    have ha : (tripleCharges (sourceA919 + difference 4 1) (sourceB919 + difference 1 4) sourceC919) = raw15247 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15247; decide +kernel
    rw [ha]
    exact (canonical15247 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA919 + difference 4 2) (sourceB919 + difference 2 4) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3347) := by
    have ha : (tripleCharges (sourceA919 + difference 4 2) (sourceB919 + difference 2 4) sourceC919) = raw15248 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15248; decide +kernel
    rw [ha]
    exact (canonical15248 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA919 + difference 4 3) (sourceB919 + difference 3 4) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA919 + difference 4 3) (sourceB919 + difference 3 4) sourceC919) = raw15249 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15249; decide +kernel
    rw [ha]
    exact (canonical15249 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA919 + difference 4 5) (sourceB919 + difference 5 4) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA919 + difference 4 5) (sourceB919 + difference 5 4) sourceC919) = raw15250 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15250; decide +kernel
    rw [ha]
    exact (canonical15250 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA919 + difference 5 0) (sourceB919 + difference 0 5) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA919 + difference 5 0) (sourceB919 + difference 0 5) sourceC919) = raw8382 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw8382; decide +kernel
    rw [ha]
    exact (canonical8382 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA919 + difference 5 1) (sourceB919 + difference 1 5) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2394) := by
    have ha : (tripleCharges (sourceA919 + difference 5 1) (sourceB919 + difference 1 5) sourceC919) = raw15251 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15251; decide +kernel
    rw [ha]
    exact (canonical15251 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA919 + difference 5 2) (sourceB919 + difference 2 5) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2392) := by
    have ha : (tripleCharges (sourceA919 + difference 5 2) (sourceB919 + difference 2 5) sourceC919) = raw15252 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15252; decide +kernel
    rw [ha]
    exact (canonical15252 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA919 + difference 5 3) (sourceB919 + difference 3 5) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA919 + difference 5 3) (sourceB919 + difference 3 5) sourceC919) = raw15253 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15253; decide +kernel
    rw [ha]
    exact (canonical15253 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA919 + difference 5 4) (sourceB919 + difference 4 5) sourceC919) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA919 + difference 5 4) (sourceB919 + difference 4 5) sourceC919) = raw15254 := by
      apply Matrix.ext; unfold tripleCharges sourceA919 sourceB919 sourceC919 difference raw15254; decide +kernel
    rw [ha]
    exact (canonical15254 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA919 sourceB919 sourceC919
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm919, Integer.Sparse.eval]
  linarith only [hs]

def sourceA920 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB920 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC920 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm920 : Integer.Sparse Master := [(Sum.inr 2591, 1), (Sum.inr 3733, 1), (Sum.inr 3819, 1), (Sum.inr 3845, 1), (Sum.inr 3854, 1), (Sum.inr 3857, 1), (Sum.inr 4092, -1)]

theorem sourceEq920 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm920 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA920 + difference 0 0) (sourceB920 + difference 0 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA920 + difference 0 0) (sourceB920 + difference 0 0) sourceC920) = raw8417 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw8417; decide +kernel
    rw [ha]
    exact (canonical8417 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA920 + difference 0 1) (sourceB920 + difference 1 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA920 + difference 0 1) (sourceB920 + difference 1 0) sourceC920) = raw15255 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15255; decide +kernel
    rw [ha]
    exact (canonical15255 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA920 + difference 0 2) (sourceB920 + difference 2 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3819) := by
    have ha : (tripleCharges (sourceA920 + difference 0 2) (sourceB920 + difference 2 0) sourceC920) = raw15256 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15256; decide +kernel
    rw [ha]
    exact (canonical15256 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA920 + difference 0 3) (sourceB920 + difference 3 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA920 + difference 0 3) (sourceB920 + difference 3 0) sourceC920) = raw15257 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15257; decide +kernel
    rw [ha]
    exact (canonical15257 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA920 + difference 0 4) (sourceB920 + difference 4 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA920 + difference 0 4) (sourceB920 + difference 4 0) sourceC920) = raw15258 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15258; decide +kernel
    rw [ha]
    exact (canonical15258 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA920 + difference 0 5) (sourceB920 + difference 5 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA920 + difference 0 5) (sourceB920 + difference 5 0) sourceC920) = raw15259 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15259; decide +kernel
    rw [ha]
    exact (canonical15259 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA920 + sourceB920) sourceC920) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA920 + sourceB920) sourceC920) = raw8422 := by
      apply Matrix.ext; unfold doubleCharges sourceA920 sourceB920 sourceC920 raw8422; decide +kernel
    rw [ha]
    exact (canonical8422 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA920 sourceB920 sourceC920
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm920, Integer.Sparse.eval]
  linarith only [hs]

def sourceA921 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB921 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC921 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceForm921 : Integer.Sparse Master := [(Sum.inr 3010, 2), (Sum.inr 3729, 1), (Sum.inr 3733, 2), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

theorem sourceEq921 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm921 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA921 + difference 0 1) (sourceB921 + difference 1 0) sourceC921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA921 + difference 0 1) (sourceB921 + difference 1 0) sourceC921) = raw15255 := by
      apply Matrix.ext; unfold tripleCharges sourceA921 sourceB921 sourceC921 difference raw15255; decide +kernel
    rw [ha]
    exact (canonical15255 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA921 + difference 1 1) (sourceB921 + difference 1 1) sourceC921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA921 + difference 1 1) (sourceB921 + difference 1 1) sourceC921) = raw8417 := by
      apply Matrix.ext; unfold tripleCharges sourceA921 sourceB921 sourceC921 difference raw8417; decide +kernel
    rw [ha]
    exact (canonical8417 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA921 + difference 2 1) (sourceB921 + difference 1 2) sourceC921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3729) := by
    have ha : (tripleCharges (sourceA921 + difference 2 1) (sourceB921 + difference 1 2) sourceC921) = raw15260 := by
      apply Matrix.ext; unfold tripleCharges sourceA921 sourceB921 sourceC921 difference raw15260; decide +kernel
    rw [ha]
    exact (canonical15260 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA921 + difference 3 1) (sourceB921 + difference 1 3) sourceC921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA921 + difference 3 1) (sourceB921 + difference 1 3) sourceC921) = raw15261 := by
      apply Matrix.ext; unfold tripleCharges sourceA921 sourceB921 sourceC921 difference raw15261; decide +kernel
    rw [ha]
    exact (canonical15261 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA921 + difference 4 1) (sourceB921 + difference 1 4) sourceC921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3010) := by
    have ha : (tripleCharges (sourceA921 + difference 4 1) (sourceB921 + difference 1 4) sourceC921) = raw15262 := by
      apply Matrix.ext; unfold tripleCharges sourceA921 sourceB921 sourceC921 difference raw15262; decide +kernel
    rw [ha]
    exact (canonical15262 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA921 + difference 5 1) (sourceB921 + difference 1 5) sourceC921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3010) := by
    have ha : (tripleCharges (sourceA921 + difference 5 1) (sourceB921 + difference 1 5) sourceC921) = raw15263 := by
      apply Matrix.ext; unfold tripleCharges sourceA921 sourceB921 sourceC921 difference raw15263; decide +kernel
    rw [ha]
    exact (canonical15263 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA921 + sourceB921) sourceC921) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA921 + sourceB921) sourceC921) = raw8422 := by
      apply Matrix.ext; unfold doubleCharges sourceA921 sourceB921 sourceC921 raw8422; decide +kernel
    rw [ha]
    exact (canonical8422 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA921 sourceB921 sourceC921
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm921, Integer.Sparse.eval]
  linarith only [hs]

def sourceA922 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB922 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC922 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm922 : Integer.Sparse Master := [(Sum.inr 4813, 1), (Sum.inr 4814, 1), (Sum.inr 4821, 1), (Sum.inr 4829, 1), (Sum.inr 4867, 1), (Sum.inr 5178, 1), (Sum.inr 5180, 1), (Sum.inr 5186, 1), (Sum.inr 5188, 1), (Sum.inr 5198, 1), (Sum.inr 5200, 1), (Sum.inr 5232, 1), (Sum.inr 5260, 1), (Sum.inr 5358, 1), (Sum.inr 5360, 1), (Sum.inr 5361, 1), (Sum.inr 5370, 1), (Sum.inr 5381, 1), (Sum.inr 5384, 1), (Sum.inr 5402, 1), (Sum.inr 5411, 1), (Sum.inr 5412, 1), (Sum.inr 5421, 1), (Sum.inr 5425, 1), (Sum.inr 5429, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5446, 2), (Sum.inr 5473, 1)]

theorem sourceEq922 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm922 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA922 + difference 0 1) (sourceB922 + difference 1 0) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA922 + difference 0 1) (sourceB922 + difference 1 0) sourceC922) = raw15264 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15264; decide +kernel
    rw [ha]
    exact (canonical15264 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA922 + difference 0 2) (sourceB922 + difference 2 0) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA922 + difference 0 2) (sourceB922 + difference 2 0) sourceC922) = raw15265 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15265; decide +kernel
    rw [ha]
    exact (canonical15265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA922 + difference 0 3) (sourceB922 + difference 3 0) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA922 + difference 0 3) (sourceB922 + difference 3 0) sourceC922) = raw15266 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15266; decide +kernel
    rw [ha]
    exact (canonical15266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA922 + difference 0 4) (sourceB922 + difference 4 0) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA922 + difference 0 4) (sourceB922 + difference 4 0) sourceC922) = raw15267 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15267; decide +kernel
    rw [ha]
    exact (canonical15267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA922 + difference 0 5) (sourceB922 + difference 5 0) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA922 + difference 0 5) (sourceB922 + difference 5 0) sourceC922) = raw15268 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15268; decide +kernel
    rw [ha]
    exact (canonical15268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA922 + difference 1 0) (sourceB922 + difference 0 1) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA922 + difference 1 0) (sourceB922 + difference 0 1) sourceC922) = raw15269 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15269; decide +kernel
    rw [ha]
    exact (canonical15269 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA922 + difference 1 2) (sourceB922 + difference 2 1) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA922 + difference 1 2) (sourceB922 + difference 2 1) sourceC922) = raw15270 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15270; decide +kernel
    rw [ha]
    exact (canonical15270 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA922 + difference 1 3) (sourceB922 + difference 3 1) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA922 + difference 1 3) (sourceB922 + difference 3 1) sourceC922) = raw15271 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15271; decide +kernel
    rw [ha]
    exact (canonical15271 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA922 + difference 1 4) (sourceB922 + difference 4 1) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA922 + difference 1 4) (sourceB922 + difference 4 1) sourceC922) = raw15272 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15272; decide +kernel
    rw [ha]
    exact (canonical15272 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA922 + difference 1 5) (sourceB922 + difference 5 1) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA922 + difference 1 5) (sourceB922 + difference 5 1) sourceC922) = raw15273 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15273; decide +kernel
    rw [ha]
    exact (canonical15273 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA922 + difference 2 0) (sourceB922 + difference 0 2) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4813) := by
    have ha : (tripleCharges (sourceA922 + difference 2 0) (sourceB922 + difference 0 2) sourceC922) = raw15274 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15274; decide +kernel
    rw [ha]
    exact (canonical15274 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA922 + difference 2 1) (sourceB922 + difference 1 2) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5358) := by
    have ha : (tripleCharges (sourceA922 + difference 2 1) (sourceB922 + difference 1 2) sourceC922) = raw15275 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15275; decide +kernel
    rw [ha]
    exact (canonical15275 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA922 + difference 2 3) (sourceB922 + difference 3 2) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA922 + difference 2 3) (sourceB922 + difference 3 2) sourceC922) = raw15276 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15276; decide +kernel
    rw [ha]
    exact (canonical15276 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA922 + difference 2 4) (sourceB922 + difference 4 2) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA922 + difference 2 4) (sourceB922 + difference 4 2) sourceC922) = raw15277 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15277; decide +kernel
    rw [ha]
    exact (canonical15277 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA922 + difference 2 5) (sourceB922 + difference 5 2) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA922 + difference 2 5) (sourceB922 + difference 5 2) sourceC922) = raw15278 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15278; decide +kernel
    rw [ha]
    exact (canonical15278 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA922 + difference 3 0) (sourceB922 + difference 0 3) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4829) := by
    have ha : (tripleCharges (sourceA922 + difference 3 0) (sourceB922 + difference 0 3) sourceC922) = raw15279 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15279; decide +kernel
    rw [ha]
    exact (canonical15279 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA922 + difference 3 1) (sourceB922 + difference 1 3) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5200) := by
    have ha : (tripleCharges (sourceA922 + difference 3 1) (sourceB922 + difference 1 3) sourceC922) = raw15280 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15280; decide +kernel
    rw [ha]
    exact (canonical15280 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA922 + difference 3 2) (sourceB922 + difference 2 3) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5186) := by
    have ha : (tripleCharges (sourceA922 + difference 3 2) (sourceB922 + difference 2 3) sourceC922) = raw15281 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15281; decide +kernel
    rw [ha]
    exact (canonical15281 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA922 + difference 3 4) (sourceB922 + difference 4 3) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA922 + difference 3 4) (sourceB922 + difference 4 3) sourceC922) = raw15282 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15282; decide +kernel
    rw [ha]
    exact (canonical15282 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA922 + difference 3 5) (sourceB922 + difference 5 3) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA922 + difference 3 5) (sourceB922 + difference 5 3) sourceC922) = raw15283 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15283; decide +kernel
    rw [ha]
    exact (canonical15283 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA922 + difference 4 0) (sourceB922 + difference 0 4) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA922 + difference 4 0) (sourceB922 + difference 0 4) sourceC922) = raw15284 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15284; decide +kernel
    rw [ha]
    exact (canonical15284 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA922 + difference 4 1) (sourceB922 + difference 1 4) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA922 + difference 4 1) (sourceB922 + difference 1 4) sourceC922) = raw15285 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15285; decide +kernel
    rw [ha]
    exact (canonical15285 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA922 + difference 4 2) (sourceB922 + difference 2 4) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA922 + difference 4 2) (sourceB922 + difference 2 4) sourceC922) = raw15286 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15286; decide +kernel
    rw [ha]
    exact (canonical15286 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA922 + difference 4 3) (sourceB922 + difference 3 4) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA922 + difference 4 3) (sourceB922 + difference 3 4) sourceC922) = raw15287 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15287; decide +kernel
    rw [ha]
    exact (canonical15287 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA922 + difference 4 5) (sourceB922 + difference 5 4) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA922 + difference 4 5) (sourceB922 + difference 5 4) sourceC922) = raw15288 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15288; decide +kernel
    rw [ha]
    exact (canonical15288 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA922 + difference 5 0) (sourceB922 + difference 0 5) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4814) := by
    have ha : (tripleCharges (sourceA922 + difference 5 0) (sourceB922 + difference 0 5) sourceC922) = raw15289 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15289; decide +kernel
    rw [ha]
    exact (canonical15289 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA922 + difference 5 1) (sourceB922 + difference 1 5) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5180) := by
    have ha : (tripleCharges (sourceA922 + difference 5 1) (sourceB922 + difference 1 5) sourceC922) = raw15290 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15290; decide +kernel
    rw [ha]
    exact (canonical15290 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA922 + difference 5 2) (sourceB922 + difference 2 5) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5178) := by
    have ha : (tripleCharges (sourceA922 + difference 5 2) (sourceB922 + difference 2 5) sourceC922) = raw15291 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15291; decide +kernel
    rw [ha]
    exact (canonical15291 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA922 + difference 5 3) (sourceB922 + difference 3 5) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA922 + difference 5 3) (sourceB922 + difference 3 5) sourceC922) = raw15292 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15292; decide +kernel
    rw [ha]
    exact (canonical15292 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA922 + difference 5 4) (sourceB922 + difference 4 5) sourceC922) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA922 + difference 5 4) (sourceB922 + difference 4 5) sourceC922) = raw15293 := by
      apply Matrix.ext; unfold tripleCharges sourceA922 sourceB922 sourceC922 difference raw15293; decide +kernel
    rw [ha]
    exact (canonical15293 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA922 sourceB922 sourceC922
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm922, Integer.Sparse.eval]
  linarith only [hs]

def sourceA923 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB923 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC923 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm923 : Integer.Sparse Master := [(Sum.inr 2031, 1), (Sum.inr 2032, 1), (Sum.inr 2039, 1), (Sum.inr 2049, 1), (Sum.inr 2251, 1), (Sum.inr 2606, 1), (Sum.inr 2608, 1), (Sum.inr 2632, 1), (Sum.inr 2677, 1), (Sum.inr 3527, 1), (Sum.inr 3538, 1), (Sum.inr 3540, 1), (Sum.inr 3575, 1), (Sum.inr 3696, 1), (Sum.inr 3699, 1), (Sum.inr 3780, 1), (Sum.inr 3802, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3827, 1), (Sum.inr 3831, 1), (Sum.inr 3834, 1), (Sum.inr 3840, 1), (Sum.inr 3846, 1), (Sum.inr 3850, 1), (Sum.inr 3852, 1), (Sum.inr 3856, 1), (Sum.inr 3881, 2), (Sum.inr 3995, 1)]

theorem sourceEq923 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm923 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA923 + difference 0 1) (sourceB923 + difference 1 0) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA923 + difference 0 1) (sourceB923 + difference 1 0) sourceC923) = raw15294 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15294; decide +kernel
    rw [ha]
    exact (canonical15294 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA923 + difference 0 2) (sourceB923 + difference 2 0) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA923 + difference 0 2) (sourceB923 + difference 2 0) sourceC923) = raw15295 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15295; decide +kernel
    rw [ha]
    exact (canonical15295 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA923 + difference 0 3) (sourceB923 + difference 3 0) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA923 + difference 0 3) (sourceB923 + difference 3 0) sourceC923) = raw15296 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15296; decide +kernel
    rw [ha]
    exact (canonical15296 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA923 + difference 0 4) (sourceB923 + difference 4 0) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA923 + difference 0 4) (sourceB923 + difference 4 0) sourceC923) = raw15297 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15297; decide +kernel
    rw [ha]
    exact (canonical15297 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA923 + difference 0 5) (sourceB923 + difference 5 0) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA923 + difference 0 5) (sourceB923 + difference 5 0) sourceC923) = raw15298 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15298; decide +kernel
    rw [ha]
    exact (canonical15298 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA923 + difference 1 0) (sourceB923 + difference 0 1) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA923 + difference 1 0) (sourceB923 + difference 0 1) sourceC923) = raw15299 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15299; decide +kernel
    rw [ha]
    exact (canonical15299 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA923 + difference 1 2) (sourceB923 + difference 2 1) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA923 + difference 1 2) (sourceB923 + difference 2 1) sourceC923) = raw15300 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15300; decide +kernel
    rw [ha]
    exact (canonical15300 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA923 + difference 1 3) (sourceB923 + difference 3 1) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA923 + difference 1 3) (sourceB923 + difference 3 1) sourceC923) = raw15301 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15301; decide +kernel
    rw [ha]
    exact (canonical15301 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA923 + difference 1 4) (sourceB923 + difference 4 1) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA923 + difference 1 4) (sourceB923 + difference 4 1) sourceC923) = raw15302 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15302; decide +kernel
    rw [ha]
    exact (canonical15302 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA923 + difference 1 5) (sourceB923 + difference 5 1) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA923 + difference 1 5) (sourceB923 + difference 5 1) sourceC923) = raw15303 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15303; decide +kernel
    rw [ha]
    exact (canonical15303 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA923 + difference 2 0) (sourceB923 + difference 0 2) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA923 + difference 2 0) (sourceB923 + difference 0 2) sourceC923) = raw15304 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15304; decide +kernel
    rw [ha]
    exact (canonical15304 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA923 + difference 2 1) (sourceB923 + difference 1 2) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3696) := by
    have ha : (tripleCharges (sourceA923 + difference 2 1) (sourceB923 + difference 1 2) sourceC923) = raw15305 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15305; decide +kernel
    rw [ha]
    exact (canonical15305 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA923 + difference 2 3) (sourceB923 + difference 3 2) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3827) := by
    have ha : (tripleCharges (sourceA923 + difference 2 3) (sourceB923 + difference 3 2) sourceC923) = raw15306 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15306; decide +kernel
    rw [ha]
    exact (canonical15306 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA923 + difference 2 4) (sourceB923 + difference 4 2) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA923 + difference 2 4) (sourceB923 + difference 4 2) sourceC923) = raw15307 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15307; decide +kernel
    rw [ha]
    exact (canonical15307 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA923 + difference 2 5) (sourceB923 + difference 5 2) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA923 + difference 2 5) (sourceB923 + difference 5 2) sourceC923) = raw15308 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15308; decide +kernel
    rw [ha]
    exact (canonical15308 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA923 + difference 3 0) (sourceB923 + difference 0 3) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2049) := by
    have ha : (tripleCharges (sourceA923 + difference 3 0) (sourceB923 + difference 0 3) sourceC923) = raw15309 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15309; decide +kernel
    rw [ha]
    exact (canonical15309 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA923 + difference 3 1) (sourceB923 + difference 1 3) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3575) := by
    have ha : (tripleCharges (sourceA923 + difference 3 1) (sourceB923 + difference 1 3) sourceC923) = raw15310 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15310; decide +kernel
    rw [ha]
    exact (canonical15310 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA923 + difference 3 2) (sourceB923 + difference 2 3) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA923 + difference 3 2) (sourceB923 + difference 2 3) sourceC923) = raw15311 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15311; decide +kernel
    rw [ha]
    exact (canonical15311 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA923 + difference 3 4) (sourceB923 + difference 4 3) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA923 + difference 3 4) (sourceB923 + difference 4 3) sourceC923) = raw15312 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15312; decide +kernel
    rw [ha]
    exact (canonical15312 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA923 + difference 3 5) (sourceB923 + difference 5 3) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA923 + difference 3 5) (sourceB923 + difference 5 3) sourceC923) = raw15313 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15313; decide +kernel
    rw [ha]
    exact (canonical15313 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA923 + difference 4 0) (sourceB923 + difference 0 4) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2039) := by
    have ha : (tripleCharges (sourceA923 + difference 4 0) (sourceB923 + difference 0 4) sourceC923) = raw15314 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15314; decide +kernel
    rw [ha]
    exact (canonical15314 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA923 + difference 4 1) (sourceB923 + difference 1 4) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3699) := by
    have ha : (tripleCharges (sourceA923 + difference 4 1) (sourceB923 + difference 1 4) sourceC923) = raw15315 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15315; decide +kernel
    rw [ha]
    exact (canonical15315 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA923 + difference 4 2) (sourceB923 + difference 2 4) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA923 + difference 4 2) (sourceB923 + difference 2 4) sourceC923) = raw15316 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15316; decide +kernel
    rw [ha]
    exact (canonical15316 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA923 + difference 4 3) (sourceB923 + difference 3 4) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3831) := by
    have ha : (tripleCharges (sourceA923 + difference 4 3) (sourceB923 + difference 3 4) sourceC923) = raw15317 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15317; decide +kernel
    rw [ha]
    exact (canonical15317 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA923 + difference 4 5) (sourceB923 + difference 5 4) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA923 + difference 4 5) (sourceB923 + difference 5 4) sourceC923) = raw15318 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15318; decide +kernel
    rw [ha]
    exact (canonical15318 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA923 + difference 5 0) (sourceB923 + difference 0 5) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2032) := by
    have ha : (tripleCharges (sourceA923 + difference 5 0) (sourceB923 + difference 0 5) sourceC923) = raw15319 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15319; decide +kernel
    rw [ha]
    exact (canonical15319 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA923 + difference 5 1) (sourceB923 + difference 1 5) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2608) := by
    have ha : (tripleCharges (sourceA923 + difference 5 1) (sourceB923 + difference 1 5) sourceC923) = raw15320 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15320; decide +kernel
    rw [ha]
    exact (canonical15320 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA923 + difference 5 2) (sourceB923 + difference 2 5) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2606) := by
    have ha : (tripleCharges (sourceA923 + difference 5 2) (sourceB923 + difference 2 5) sourceC923) = raw15321 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15321; decide +kernel
    rw [ha]
    exact (canonical15321 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA923 + difference 5 3) (sourceB923 + difference 3 5) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA923 + difference 5 3) (sourceB923 + difference 3 5) sourceC923) = raw15322 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15322; decide +kernel
    rw [ha]
    exact (canonical15322 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA923 + difference 5 4) (sourceB923 + difference 4 5) sourceC923) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA923 + difference 5 4) (sourceB923 + difference 4 5) sourceC923) = raw15323 := by
      apply Matrix.ext; unfold tripleCharges sourceA923 sourceB923 sourceC923 difference raw15323; decide +kernel
    rw [ha]
    exact (canonical15323 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA923 sourceB923 sourceC923
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm923, Integer.Sparse.eval]
  linarith only [hs]

def sourceA924 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB924 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC924 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm924 : Integer.Sparse Master := [(Sum.inr 2078, 1), (Sum.inr 2080, 1), (Sum.inr 2081, 1), (Sum.inr 2108, 1), (Sum.inr 2217, 1), (Sum.inr 2860, 1), (Sum.inr 2867, 1), (Sum.inr 2876, 1), (Sum.inr 3086, 1), (Sum.inr 3374, 1), (Sum.inr 3379, 1), (Sum.inr 3386, 1), (Sum.inr 3570, 1), (Sum.inr 3722, 1), (Sum.inr 3738, 1), (Sum.inr 3752, 1), (Sum.inr 3762, 1), (Sum.inr 3771, 1), (Sum.inr 3772, 1), (Sum.inr 3788, 1), (Sum.inr 3814, 1), (Sum.inr 3872, 1), (Sum.inr 3873, 1), (Sum.inr 3883, 1), (Sum.inr 3884, 1), (Sum.inr 3954, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3982, 1), (Sum.inr 4027, 1)]

theorem sourceEq924 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm924 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA924 + difference 0 1) (sourceB924 + difference 1 0) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA924 + difference 0 1) (sourceB924 + difference 1 0) sourceC924) = raw15324 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15324; decide +kernel
    rw [ha]
    exact (canonical15324 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA924 + difference 0 2) (sourceB924 + difference 2 0) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA924 + difference 0 2) (sourceB924 + difference 2 0) sourceC924) = raw15325 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15325; decide +kernel
    rw [ha]
    exact (canonical15325 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA924 + difference 0 3) (sourceB924 + difference 3 0) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA924 + difference 0 3) (sourceB924 + difference 3 0) sourceC924) = raw15326 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15326; decide +kernel
    rw [ha]
    exact (canonical15326 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA924 + difference 0 4) (sourceB924 + difference 4 0) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA924 + difference 0 4) (sourceB924 + difference 4 0) sourceC924) = raw15327 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15327; decide +kernel
    rw [ha]
    exact (canonical15327 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA924 + difference 0 5) (sourceB924 + difference 5 0) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA924 + difference 0 5) (sourceB924 + difference 5 0) sourceC924) = raw15328 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15328; decide +kernel
    rw [ha]
    exact (canonical15328 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA924 + difference 1 0) (sourceB924 + difference 0 1) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA924 + difference 1 0) (sourceB924 + difference 0 1) sourceC924) = raw15329 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15329; decide +kernel
    rw [ha]
    exact (canonical15329 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA924 + difference 1 2) (sourceB924 + difference 2 1) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA924 + difference 1 2) (sourceB924 + difference 2 1) sourceC924) = raw15330 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15330; decide +kernel
    rw [ha]
    exact (canonical15330 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA924 + difference 1 3) (sourceB924 + difference 3 1) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA924 + difference 1 3) (sourceB924 + difference 3 1) sourceC924) = raw15331 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15331; decide +kernel
    rw [ha]
    exact (canonical15331 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA924 + difference 1 4) (sourceB924 + difference 4 1) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3738) := by
    have ha : (tripleCharges (sourceA924 + difference 1 4) (sourceB924 + difference 4 1) sourceC924) = raw15332 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15332; decide +kernel
    rw [ha]
    exact (canonical15332 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA924 + difference 1 5) (sourceB924 + difference 5 1) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA924 + difference 1 5) (sourceB924 + difference 5 1) sourceC924) = raw15333 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15333; decide +kernel
    rw [ha]
    exact (canonical15333 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA924 + difference 2 0) (sourceB924 + difference 0 2) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2078) := by
    have ha : (tripleCharges (sourceA924 + difference 2 0) (sourceB924 + difference 0 2) sourceC924) = raw15334 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15334; decide +kernel
    rw [ha]
    exact (canonical15334 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA924 + difference 2 1) (sourceB924 + difference 1 2) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3752) := by
    have ha : (tripleCharges (sourceA924 + difference 2 1) (sourceB924 + difference 1 2) sourceC924) = raw15335 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15335; decide +kernel
    rw [ha]
    exact (canonical15335 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA924 + difference 2 3) (sourceB924 + difference 3 2) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA924 + difference 2 3) (sourceB924 + difference 3 2) sourceC924) = raw15336 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15336; decide +kernel
    rw [ha]
    exact (canonical15336 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA924 + difference 2 4) (sourceB924 + difference 4 2) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA924 + difference 2 4) (sourceB924 + difference 4 2) sourceC924) = raw15337 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15337; decide +kernel
    rw [ha]
    exact (canonical15337 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA924 + difference 2 5) (sourceB924 + difference 5 2) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA924 + difference 2 5) (sourceB924 + difference 5 2) sourceC924) = raw15338 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15338; decide +kernel
    rw [ha]
    exact (canonical15338 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA924 + difference 3 0) (sourceB924 + difference 0 3) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2080) := by
    have ha : (tripleCharges (sourceA924 + difference 3 0) (sourceB924 + difference 0 3) sourceC924) = raw15339 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15339; decide +kernel
    rw [ha]
    exact (canonical15339 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA924 + difference 3 1) (sourceB924 + difference 1 3) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2876) := by
    have ha : (tripleCharges (sourceA924 + difference 3 1) (sourceB924 + difference 1 3) sourceC924) = raw15340 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15340; decide +kernel
    rw [ha]
    exact (canonical15340 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA924 + difference 3 2) (sourceB924 + difference 2 3) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2860) := by
    have ha : (tripleCharges (sourceA924 + difference 3 2) (sourceB924 + difference 2 3) sourceC924) = raw15341 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15341; decide +kernel
    rw [ha]
    exact (canonical15341 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA924 + difference 3 4) (sourceB924 + difference 4 3) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA924 + difference 3 4) (sourceB924 + difference 4 3) sourceC924) = raw15342 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15342; decide +kernel
    rw [ha]
    exact (canonical15342 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA924 + difference 3 5) (sourceB924 + difference 5 3) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA924 + difference 3 5) (sourceB924 + difference 5 3) sourceC924) = raw15343 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15343; decide +kernel
    rw [ha]
    exact (canonical15343 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA924 + difference 4 0) (sourceB924 + difference 0 4) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA924 + difference 4 0) (sourceB924 + difference 0 4) sourceC924) = raw15344 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15344; decide +kernel
    rw [ha]
    exact (canonical15344 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA924 + difference 4 1) (sourceB924 + difference 1 4) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA924 + difference 4 1) (sourceB924 + difference 1 4) sourceC924) = raw15345 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15345; decide +kernel
    rw [ha]
    exact (canonical15345 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA924 + difference 4 2) (sourceB924 + difference 2 4) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA924 + difference 4 2) (sourceB924 + difference 2 4) sourceC924) = raw15346 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15346; decide +kernel
    rw [ha]
    exact (canonical15346 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA924 + difference 4 3) (sourceB924 + difference 3 4) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA924 + difference 4 3) (sourceB924 + difference 3 4) sourceC924) = raw15347 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15347; decide +kernel
    rw [ha]
    exact (canonical15347 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA924 + difference 4 5) (sourceB924 + difference 5 4) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA924 + difference 4 5) (sourceB924 + difference 5 4) sourceC924) = raw15348 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15348; decide +kernel
    rw [ha]
    exact (canonical15348 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA924 + difference 5 0) (sourceB924 + difference 0 5) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2081) := by
    have ha : (tripleCharges (sourceA924 + difference 5 0) (sourceB924 + difference 0 5) sourceC924) = raw15349 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15349; decide +kernel
    rw [ha]
    exact (canonical15349 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA924 + difference 5 1) (sourceB924 + difference 1 5) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3386) := by
    have ha : (tripleCharges (sourceA924 + difference 5 1) (sourceB924 + difference 1 5) sourceC924) = raw15350 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15350; decide +kernel
    rw [ha]
    exact (canonical15350 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA924 + difference 5 2) (sourceB924 + difference 2 5) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3374) := by
    have ha : (tripleCharges (sourceA924 + difference 5 2) (sourceB924 + difference 2 5) sourceC924) = raw15351 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15351; decide +kernel
    rw [ha]
    exact (canonical15351 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA924 + difference 5 3) (sourceB924 + difference 3 5) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA924 + difference 5 3) (sourceB924 + difference 3 5) sourceC924) = raw15352 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15352; decide +kernel
    rw [ha]
    exact (canonical15352 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA924 + difference 5 4) (sourceB924 + difference 4 5) sourceC924) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA924 + difference 5 4) (sourceB924 + difference 4 5) sourceC924) = raw15353 := by
      apply Matrix.ext; unfold tripleCharges sourceA924 sourceB924 sourceC924 difference raw15353; decide +kernel
    rw [ha]
    exact (canonical15353 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA924 sourceB924 sourceC924
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm924, Integer.Sparse.eval]
  linarith only [hs]

def sourceA925 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB925 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC925 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm925 : Integer.Sparse Master := [(Sum.inr 2619, 1), (Sum.inr 2872, 1), (Sum.inr 3175, 1), (Sum.inr 3180, 1), (Sum.inr 3198, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem sourceEq925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm925 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA925 + difference 0 0) (sourceB925 + difference 0 0) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA925 + difference 0 0) (sourceB925 + difference 0 0) sourceC925) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA925 + difference 1 0) (sourceB925 + difference 0 1) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA925 + difference 1 0) (sourceB925 + difference 0 1) sourceC925) = raw15355 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15355; decide +kernel
    rw [ha]
    exact (canonical15355 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA925 + difference 2 0) (sourceB925 + difference 0 2) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3175) := by
    have ha : (tripleCharges (sourceA925 + difference 2 0) (sourceB925 + difference 0 2) sourceC925) = raw15356 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15356; decide +kernel
    rw [ha]
    exact (canonical15356 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA925 + difference 3 0) (sourceB925 + difference 0 3) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2619) := by
    have ha : (tripleCharges (sourceA925 + difference 3 0) (sourceB925 + difference 0 3) sourceC925) = raw15357 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15357; decide +kernel
    rw [ha]
    exact (canonical15357 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA925 + difference 4 0) (sourceB925 + difference 0 4) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA925 + difference 4 0) (sourceB925 + difference 0 4) sourceC925) = raw15358 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15358; decide +kernel
    rw [ha]
    exact (canonical15358 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA925 + difference 5 0) (sourceB925 + difference 0 5) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2872) := by
    have ha : (tripleCharges (sourceA925 + difference 5 0) (sourceB925 + difference 0 5) sourceC925) = raw15359 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15359; decide +kernel
    rw [ha]
    exact (canonical15359 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA925 + sourceB925) sourceC925) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA925 + sourceB925) sourceC925) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA925 sourceB925 sourceC925 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA925 sourceB925 sourceC925
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm925, Integer.Sparse.eval]
  linarith only [hs]

def sourceA926 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB926 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC926 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm926 : Integer.Sparse Master := [(Sum.inr 3180, 1), (Sum.inr 3732, 1), (Sum.inr 3788, 1), (Sum.inr 3809, 1), (Sum.inr 3877, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem sourceEq926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm926 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA926 + difference 1 0) (sourceB926 + difference 0 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA926 + difference 1 0) (sourceB926 + difference 0 1) sourceC926) = raw15355 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15355; decide +kernel
    rw [ha]
    exact (canonical15355 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA926 + difference 1 1) (sourceB926 + difference 1 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA926 + difference 1 1) (sourceB926 + difference 1 1) sourceC926) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA926 + difference 1 2) (sourceB926 + difference 2 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA926 + difference 1 2) (sourceB926 + difference 2 1) sourceC926) = raw15361 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15361; decide +kernel
    rw [ha]
    exact (canonical15361 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA926 + difference 1 3) (sourceB926 + difference 3 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA926 + difference 1 3) (sourceB926 + difference 3 1) sourceC926) = raw15362 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15362; decide +kernel
    rw [ha]
    exact (canonical15362 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA926 + difference 1 4) (sourceB926 + difference 4 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA926 + difference 1 4) (sourceB926 + difference 4 1) sourceC926) = raw15363 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15363; decide +kernel
    rw [ha]
    exact (canonical15363 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA926 + difference 1 5) (sourceB926 + difference 5 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA926 + difference 1 5) (sourceB926 + difference 5 1) sourceC926) = raw15364 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15364; decide +kernel
    rw [ha]
    exact (canonical15364 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA926 + sourceB926) sourceC926) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA926 + sourceB926) sourceC926) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA926 sourceB926 sourceC926 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA926 sourceB926 sourceC926
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm926, Integer.Sparse.eval]
  linarith only [hs]

def sourceA927 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB927 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC927 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm927 : Integer.Sparse Master := [(Sum.inr 2634, 1), (Sum.inr 2873, 1), (Sum.inr 3699, 1), (Sum.inr 3828, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

theorem sourceEq927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm927 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA927 + difference 0 1) (sourceB927 + difference 1 0) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA927 + difference 0 1) (sourceB927 + difference 1 0) sourceC927) = raw15365 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15365; decide +kernel
    rw [ha]
    exact (canonical15365 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA927 + difference 1 1) (sourceB927 + difference 1 1) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA927 + difference 1 1) (sourceB927 + difference 1 1) sourceC927) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA927 + difference 2 1) (sourceB927 + difference 1 2) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3828) := by
    have ha : (tripleCharges (sourceA927 + difference 2 1) (sourceB927 + difference 1 2) sourceC927) = raw15366 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15366; decide +kernel
    rw [ha]
    exact (canonical15366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA927 + difference 3 1) (sourceB927 + difference 1 3) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2634) := by
    have ha : (tripleCharges (sourceA927 + difference 3 1) (sourceB927 + difference 1 3) sourceC927) = raw15367 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15367; decide +kernel
    rw [ha]
    exact (canonical15367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA927 + difference 4 1) (sourceB927 + difference 1 4) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3699) := by
    have ha : (tripleCharges (sourceA927 + difference 4 1) (sourceB927 + difference 1 4) sourceC927) = raw15368 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15368; decide +kernel
    rw [ha]
    exact (canonical15368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA927 + difference 5 1) (sourceB927 + difference 1 5) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2873) := by
    have ha : (tripleCharges (sourceA927 + difference 5 1) (sourceB927 + difference 1 5) sourceC927) = raw15369 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15369; decide +kernel
    rw [ha]
    exact (canonical15369 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA927 + sourceB927) sourceC927) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA927 + sourceB927) sourceC927) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA927 sourceB927 sourceC927 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA927 sourceB927 sourceC927
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm927, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
