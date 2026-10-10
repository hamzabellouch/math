import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical156
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical158

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1216 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1216 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1216 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1216 : Integer.Sparse Master := [(Sum.inr 1723, 2), (Sum.inr 1725, 1), (Sum.inr 1729, 1), (Sum.inr 1750, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

theorem sourceEq1216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1216 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1216 + difference 0 3) (sourceB1216 + difference 3 0) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1216 + difference 0 3) (sourceB1216 + difference 3 0) sourceC1216) = raw20151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20151; decide +kernel
    rw [ha]
    exact (canonical20151 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1216 + difference 1 3) (sourceB1216 + difference 3 1) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1216 + difference 1 3) (sourceB1216 + difference 3 1) sourceC1216) = raw20159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20159; decide +kernel
    rw [ha]
    exact (canonical20159 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1216 + difference 2 3) (sourceB1216 + difference 3 2) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1216 + difference 2 3) (sourceB1216 + difference 3 2) sourceC1216) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1216 + difference 3 3) (sourceB1216 + difference 3 3) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1216 + difference 3 3) (sourceB1216 + difference 3 3) sourceC1216) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1216 + difference 4 3) (sourceB1216 + difference 3 4) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1216 + difference 4 3) (sourceB1216 + difference 3 4) sourceC1216) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1216 + difference 5 3) (sourceB1216 + difference 3 5) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1216 + difference 5 3) (sourceB1216 + difference 3 5) sourceC1216) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1216 + sourceB1216) sourceC1216) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1216 + sourceB1216) sourceC1216) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1216 sourceB1216 sourceC1216 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1216 sourceB1216 sourceC1216
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1216, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1217 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1217 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1217 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1217 : Integer.Sparse Master := [(Sum.inr 857, 1), (Sum.inr 1624, 2), (Sum.inr 1729, 1), (Sum.inr 1746, 1), (Sum.inr 1750, 1), (Sum.inr 4070, -1)]

theorem sourceEq1217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1217 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 0) (sourceB1217 + difference 0 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 857) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 0) (sourceB1217 + difference 0 4) sourceC1217) = raw20157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20157; decide +kernel
    rw [ha]
    exact (canonical20157 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 1) (sourceB1217 + difference 1 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 1) (sourceB1217 + difference 1 4) sourceC1217) = raw20162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20162; decide +kernel
    rw [ha]
    exact (canonical20162 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 2) (sourceB1217 + difference 2 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 2) (sourceB1217 + difference 2 4) sourceC1217) = raw20163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20163; decide +kernel
    rw [ha]
    exact (canonical20163 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 3) (sourceB1217 + difference 3 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 3) (sourceB1217 + difference 3 4) sourceC1217) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 4) (sourceB1217 + difference 4 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 4) (sourceB1217 + difference 4 4) sourceC1217) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 5) (sourceB1217 + difference 5 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 5) (sourceB1217 + difference 5 4) sourceC1217) = raw20132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20132; decide +kernel
    rw [ha]
    exact (canonical20132 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1217 + sourceB1217) sourceC1217) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1217 + sourceB1217) sourceC1217) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1217 sourceB1217 sourceC1217 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1217 sourceB1217 sourceC1217
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1217, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1218 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1218 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1218 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1218 : Integer.Sparse Master := [(Sum.inr 815, 1), (Sum.inr 1604, 2), (Sum.inr 1652, 1), (Sum.inr 1725, 1), (Sum.inr 1729, 1), (Sum.inr 4070, -1)]

theorem sourceEq1218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1218 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 0) (sourceB1218 + difference 0 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 0) (sourceB1218 + difference 0 5) sourceC1218) = raw20158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20158; decide +kernel
    rw [ha]
    exact (canonical20158 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 1) (sourceB1218 + difference 1 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1604) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 1) (sourceB1218 + difference 1 5) sourceC1218) = raw20164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20164; decide +kernel
    rw [ha]
    exact (canonical20164 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 2) (sourceB1218 + difference 2 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1604) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 2) (sourceB1218 + difference 2 5) sourceC1218) = raw20165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20165; decide +kernel
    rw [ha]
    exact (canonical20165 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 3) (sourceB1218 + difference 3 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 3) (sourceB1218 + difference 3 5) sourceC1218) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 4) (sourceB1218 + difference 4 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1652) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 4) (sourceB1218 + difference 4 5) sourceC1218) = raw20166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20166; decide +kernel
    rw [ha]
    exact (canonical20166 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 5) (sourceB1218 + difference 5 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 5) (sourceB1218 + difference 5 5) sourceC1218) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1218 + sourceB1218) sourceC1218) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1218 + sourceB1218) sourceC1218) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1218 sourceB1218 sourceC1218 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1218 sourceB1218 sourceC1218
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1218, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1219 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1219 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1219 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1219 : Integer.Sparse Master := [(Sum.inr 1718, 2), (Sum.inr 1719, 1), (Sum.inr 1729, 1), (Sum.inr 1746, 1), (Sum.inr 1952, 1), (Sum.inr 4070, -1)]

theorem sourceEq1219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1219 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1219 + difference 0 5) (sourceB1219 + difference 5 0) sourceC1219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1952) := by
    have ha : (tripleCharges (sourceA1219 + difference 0 5) (sourceB1219 + difference 5 0) sourceC1219) = raw20153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1219 sourceB1219 sourceC1219 difference raw20153; decide +kernel
    rw [ha]
    exact (canonical20153 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1219 + difference 1 5) (sourceB1219 + difference 5 1) sourceC1219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1718) := by
    have ha : (tripleCharges (sourceA1219 + difference 1 5) (sourceB1219 + difference 5 1) sourceC1219) = raw20167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1219 sourceB1219 sourceC1219 difference raw20167; decide +kernel
    rw [ha]
    exact (canonical20167 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1219 + difference 2 5) (sourceB1219 + difference 5 2) sourceC1219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1718) := by
    have ha : (tripleCharges (sourceA1219 + difference 2 5) (sourceB1219 + difference 5 2) sourceC1219) = raw20168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1219 sourceB1219 sourceC1219 difference raw20168; decide +kernel
    rw [ha]
    exact (canonical20168 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1219 + difference 3 5) (sourceB1219 + difference 5 3) sourceC1219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1719) := by
    have ha : (tripleCharges (sourceA1219 + difference 3 5) (sourceB1219 + difference 5 3) sourceC1219) = raw20169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1219 sourceB1219 sourceC1219 difference raw20169; decide +kernel
    rw [ha]
    exact (canonical20169 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1219 + difference 4 5) (sourceB1219 + difference 5 4) sourceC1219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1219 + difference 4 5) (sourceB1219 + difference 5 4) sourceC1219) = raw20132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1219 sourceB1219 sourceC1219 difference raw20132; decide +kernel
    rw [ha]
    exact (canonical20132 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1219 + difference 5 5) (sourceB1219 + difference 5 5) sourceC1219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1219 + difference 5 5) (sourceB1219 + difference 5 5) sourceC1219) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1219 sourceB1219 sourceC1219 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1219 + sourceB1219) sourceC1219) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1219 + sourceB1219) sourceC1219) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1219 sourceB1219 sourceC1219 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1219 sourceB1219 sourceC1219
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1219, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1220 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1220 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1220 : Charge := ![1, 0, 0, 2, 0, -3]
def sourceForm1220 : Integer.Sparse Master := [(Sum.inr 936, 1), (Sum.inr 1315, 2), (Sum.inr 1323, 1), (Sum.inr 1369, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

theorem sourceEq1220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1220 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1220 + difference 0 3) (sourceB1220 + difference 3 0) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1220 + difference 0 3) (sourceB1220 + difference 3 0) sourceC1220) = raw20170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20170; decide +kernel
    rw [ha]
    exact (canonical20170 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1220 + difference 1 3) (sourceB1220 + difference 3 1) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1315) := by
    have ha : (tripleCharges (sourceA1220 + difference 1 3) (sourceB1220 + difference 3 1) sourceC1220) = raw20171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20171; decide +kernel
    rw [ha]
    exact (canonical20171 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1220 + difference 2 3) (sourceB1220 + difference 3 2) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1315) := by
    have ha : (tripleCharges (sourceA1220 + difference 2 3) (sourceB1220 + difference 3 2) sourceC1220) = raw20172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20172; decide +kernel
    rw [ha]
    exact (canonical20172 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1220 + difference 3 3) (sourceB1220 + difference 3 3) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA1220 + difference 3 3) (sourceB1220 + difference 3 3) sourceC1220) = raw20173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20173; decide +kernel
    rw [ha]
    exact (canonical20173 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1220 + difference 4 3) (sourceB1220 + difference 3 4) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1323) := by
    have ha : (tripleCharges (sourceA1220 + difference 4 3) (sourceB1220 + difference 3 4) sourceC1220) = raw20174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20174; decide +kernel
    rw [ha]
    exact (canonical20174 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1220 + difference 5 3) (sourceB1220 + difference 3 5) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1220 + difference 5 3) (sourceB1220 + difference 3 5) sourceC1220) = raw20175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20175; decide +kernel
    rw [ha]
    exact (canonical20175 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1220 + sourceB1220) sourceC1220) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1220 + sourceB1220) sourceC1220) = raw20176 := by
      apply Matrix.ext; unfold doubleCharges sourceA1220 sourceB1220 sourceC1220 raw20176; decide +kernel
    rw [ha]
    exact (canonical20176 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1220 sourceB1220 sourceC1220
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1220, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1221 : Charge := ![1, 0, 0, 2, 0, -3]
def sourceB1221 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1221 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1221 : Integer.Sparse Master := [(Sum.inr 1011, 1), (Sum.inr 1746, 1), (Sum.inr 1952, 1), (Sum.inr 2005, 2), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

theorem sourceEq1221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1221 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 0) (sourceB1221 + difference 0 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 0) (sourceB1221 + difference 0 0) sourceC1221) = raw20132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20132; decide +kernel
    rw [ha]
    exact (canonical20132 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 1) (sourceB1221 + difference 1 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2005) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 1) (sourceB1221 + difference 1 0) sourceC1221) = raw20177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20177; decide +kernel
    rw [ha]
    exact (canonical20177 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 2) (sourceB1221 + difference 2 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2005) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 2) (sourceB1221 + difference 2 0) sourceC1221) = raw20178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20178; decide +kernel
    rw [ha]
    exact (canonical20178 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 3) (sourceB1221 + difference 3 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 3) (sourceB1221 + difference 3 0) sourceC1221) = raw20123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20123; decide +kernel
    rw [ha]
    exact (canonical20123 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 4) (sourceB1221 + difference 4 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1952) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 4) (sourceB1221 + difference 4 0) sourceC1221) = raw20153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20153; decide +kernel
    rw [ha]
    exact (canonical20153 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 5) (sourceB1221 + difference 5 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1011) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 5) (sourceB1221 + difference 5 0) sourceC1221) = raw20179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20179; decide +kernel
    rw [ha]
    exact (canonical20179 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1221 + sourceB1221) sourceC1221) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1221 + sourceB1221) sourceC1221) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1221 sourceB1221 sourceC1221 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1221 sourceB1221 sourceC1221
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1221, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1222 : Charge := ![1, 0, 0, 2, 0, -3]
def sourceB1222 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1222 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1222 : Integer.Sparse Master := [(Sum.inr 835, 2), (Sum.inr 837, 1), (Sum.inr 838, 1), (Sum.inr 857, 1), (Sum.inr 1746, 1), (Sum.inr 4070, -1)]

theorem sourceEq1222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1222 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1222 + difference 0 0) (sourceB1222 + difference 0 0) sourceC1222) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1222 + difference 0 0) (sourceB1222 + difference 0 0) sourceC1222) = raw20132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1222 sourceB1222 sourceC1222 difference raw20132; decide +kernel
    rw [ha]
    exact (canonical20132 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1222 + difference 1 0) (sourceB1222 + difference 0 1) sourceC1222) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 835) := by
    have ha : (tripleCharges (sourceA1222 + difference 1 0) (sourceB1222 + difference 0 1) sourceC1222) = raw20180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1222 sourceB1222 sourceC1222 difference raw20180; decide +kernel
    rw [ha]
    exact (canonical20180 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1222 + difference 2 0) (sourceB1222 + difference 0 2) sourceC1222) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 835) := by
    have ha : (tripleCharges (sourceA1222 + difference 2 0) (sourceB1222 + difference 0 2) sourceC1222) = raw20181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1222 sourceB1222 sourceC1222 difference raw20181; decide +kernel
    rw [ha]
    exact (canonical20181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1222 + difference 3 0) (sourceB1222 + difference 0 3) sourceC1222) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 837) := by
    have ha : (tripleCharges (sourceA1222 + difference 3 0) (sourceB1222 + difference 0 3) sourceC1222) = raw20182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1222 sourceB1222 sourceC1222 difference raw20182; decide +kernel
    rw [ha]
    exact (canonical20182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1222 + difference 4 0) (sourceB1222 + difference 0 4) sourceC1222) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 838) := by
    have ha : (tripleCharges (sourceA1222 + difference 4 0) (sourceB1222 + difference 0 4) sourceC1222) = raw20127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1222 sourceB1222 sourceC1222 difference raw20127; decide +kernel
    rw [ha]
    exact (canonical20127 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1222 + difference 5 0) (sourceB1222 + difference 0 5) sourceC1222) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 857) := by
    have ha : (tripleCharges (sourceA1222 + difference 5 0) (sourceB1222 + difference 0 5) sourceC1222) = raw20157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1222 sourceB1222 sourceC1222 difference raw20157; decide +kernel
    rw [ha]
    exact (canonical20157 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1222 + sourceB1222) sourceC1222) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1222 + sourceB1222) sourceC1222) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1222 sourceB1222 sourceC1222 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1222 sourceB1222 sourceC1222
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1222, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1223 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1223 : Charge := ![3, 0, 0, -3, 0, 0]
def sourceC1223 : Charge := ![1, 0, 0, 3, -1, -3]
def sourceForm1223 : Integer.Sparse Master := [(Sum.inr 1352, 1), (Sum.inr 1932, 2), (Sum.inr 1951, 1), (Sum.inr 2222, 1), (Sum.inr 2267, 1), (Sum.inr 4081, -1)]

theorem sourceEq1223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1223 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1223 + difference 0 0) (sourceB1223 + difference 0 0) sourceC1223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1352) := by
    have ha : (tripleCharges (sourceA1223 + difference 0 0) (sourceB1223 + difference 0 0) sourceC1223) = raw20183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1223 sourceB1223 sourceC1223 difference raw20183; decide +kernel
    rw [ha]
    exact (canonical20183 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1223 + difference 0 1) (sourceB1223 + difference 1 0) sourceC1223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1932) := by
    have ha : (tripleCharges (sourceA1223 + difference 0 1) (sourceB1223 + difference 1 0) sourceC1223) = raw20184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1223 sourceB1223 sourceC1223 difference raw20184; decide +kernel
    rw [ha]
    exact (canonical20184 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1223 + difference 0 2) (sourceB1223 + difference 2 0) sourceC1223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1932) := by
    have ha : (tripleCharges (sourceA1223 + difference 0 2) (sourceB1223 + difference 2 0) sourceC1223) = raw20185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1223 sourceB1223 sourceC1223 difference raw20185; decide +kernel
    rw [ha]
    exact (canonical20185 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1223 + difference 0 3) (sourceB1223 + difference 3 0) sourceC1223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA1223 + difference 0 3) (sourceB1223 + difference 3 0) sourceC1223) = raw20186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1223 sourceB1223 sourceC1223 difference raw20186; decide +kernel
    rw [ha]
    exact (canonical20186 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1223 + difference 0 4) (sourceB1223 + difference 4 0) sourceC1223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA1223 + difference 0 4) (sourceB1223 + difference 4 0) sourceC1223) = raw20187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1223 sourceB1223 sourceC1223 difference raw20187; decide +kernel
    rw [ha]
    exact (canonical20187 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1223 + difference 0 5) (sourceB1223 + difference 5 0) sourceC1223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA1223 + difference 0 5) (sourceB1223 + difference 5 0) sourceC1223) = raw20188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1223 sourceB1223 sourceC1223 difference raw20188; decide +kernel
    rw [ha]
    exact (canonical20188 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1223 + sourceB1223) sourceC1223) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1223 + sourceB1223) sourceC1223) = raw20189 := by
      apply Matrix.ext; unfold doubleCharges sourceA1223 sourceB1223 sourceC1223 raw20189; decide +kernel
    rw [ha]
    exact (canonical20189 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1223 sourceB1223 sourceC1223
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1223, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1224 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1224 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1224 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceForm1224 : Integer.Sparse Master := [(Sum.inr 581, 1), (Sum.inr 905, 1), (Sum.inr 945, 1), (Sum.inr 1022, 1), (Sum.inr 1041, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

theorem sourceEq1224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1224 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 0) (sourceB1224 + difference 0 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 0) (sourceB1224 + difference 0 2) sourceC1224) = raw20190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20190; decide +kernel
    rw [ha]
    exact (canonical20190 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 1) (sourceB1224 + difference 1 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 905) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 1) (sourceB1224 + difference 1 2) sourceC1224) = raw20191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20191; decide +kernel
    rw [ha]
    exact (canonical20191 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 2) (sourceB1224 + difference 2 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 2) (sourceB1224 + difference 2 2) sourceC1224) = raw20192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20192; decide +kernel
    rw [ha]
    exact (canonical20192 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 3) (sourceB1224 + difference 3 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 3) (sourceB1224 + difference 3 2) sourceC1224) = raw20193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20193; decide +kernel
    rw [ha]
    exact (canonical20193 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 4) (sourceB1224 + difference 4 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 4) (sourceB1224 + difference 4 2) sourceC1224) = raw20194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20194; decide +kernel
    rw [ha]
    exact (canonical20194 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 5) (sourceB1224 + difference 5 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 5) (sourceB1224 + difference 5 2) sourceC1224) = raw20195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20195; decide +kernel
    rw [ha]
    exact (canonical20195 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1224 + sourceB1224) sourceC1224) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1224 + sourceB1224) sourceC1224) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA1224 sourceB1224 sourceC1224 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1224 sourceB1224 sourceC1224
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1224, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1225 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1225 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1225 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceForm1225 : Integer.Sparse Master := [(Sum.inr 1118, 1), (Sum.inr 1327, 1), (Sum.inr 1333, 1), (Sum.inr 1337, 1), (Sum.inr 1388, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

theorem sourceEq1225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1225 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1225 + difference 0 2) (sourceB1225 + difference 2 0) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1225 + difference 0 2) (sourceB1225 + difference 2 0) sourceC1225) = raw20197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20197; decide +kernel
    rw [ha]
    exact (canonical20197 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1225 + difference 1 2) (sourceB1225 + difference 2 1) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1225 + difference 1 2) (sourceB1225 + difference 2 1) sourceC1225) = raw20198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20198; decide +kernel
    rw [ha]
    exact (canonical20198 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1225 + difference 2 2) (sourceB1225 + difference 2 2) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1225 + difference 2 2) (sourceB1225 + difference 2 2) sourceC1225) = raw9229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw9229; decide +kernel
    rw [ha]
    exact (canonical9229 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1225 + difference 3 2) (sourceB1225 + difference 2 3) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1337) := by
    have ha : (tripleCharges (sourceA1225 + difference 3 2) (sourceB1225 + difference 2 3) sourceC1225) = raw20199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20199; decide +kernel
    rw [ha]
    exact (canonical20199 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1225 + difference 4 2) (sourceB1225 + difference 2 4) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1225 + difference 4 2) (sourceB1225 + difference 2 4) sourceC1225) = raw20200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20200; decide +kernel
    rw [ha]
    exact (canonical20200 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1225 + difference 5 2) (sourceB1225 + difference 2 5) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1225 + difference 5 2) (sourceB1225 + difference 2 5) sourceC1225) = raw20201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20201; decide +kernel
    rw [ha]
    exact (canonical20201 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1225 + sourceB1225) sourceC1225) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1225 + sourceB1225) sourceC1225) = raw9224 := by
      apply Matrix.ext; unfold doubleCharges sourceA1225 sourceB1225 sourceC1225 raw9224; decide +kernel
    rw [ha]
    exact (canonical9224 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1225 sourceB1225 sourceC1225
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1225, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1226 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1226 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1226 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1226 : Integer.Sparse Master := [(Sum.inr 1723, 1), (Sum.inr 1942, 1), (Sum.inr 3279, 1), (Sum.inr 3283, 1), (Sum.inr 3300, 2), (Sum.inr 4070, -1)]

theorem sourceEq1226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1226 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 0) (sourceB1226 + difference 0 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 0) (sourceB1226 + difference 0 0) sourceC1226) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 1) (sourceB1226 + difference 1 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3279) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 1) (sourceB1226 + difference 1 0) sourceC1226) = raw20202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20202; decide +kernel
    rw [ha]
    exact (canonical20202 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 2) (sourceB1226 + difference 2 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 2) (sourceB1226 + difference 2 0) sourceC1226) = raw20151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20151; decide +kernel
    rw [ha]
    exact (canonical20151 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 3) (sourceB1226 + difference 3 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 3) (sourceB1226 + difference 3 0) sourceC1226) = raw20203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20203; decide +kernel
    rw [ha]
    exact (canonical20203 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 4) (sourceB1226 + difference 4 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3283) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 4) (sourceB1226 + difference 4 0) sourceC1226) = raw20204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20204; decide +kernel
    rw [ha]
    exact (canonical20204 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 5) (sourceB1226 + difference 5 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1942) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 5) (sourceB1226 + difference 5 0) sourceC1226) = raw20205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20205; decide +kernel
    rw [ha]
    exact (canonical20205 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1226 + sourceB1226) sourceC1226) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1226 + sourceB1226) sourceC1226) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1226 sourceB1226 sourceC1226 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1226 sourceB1226 sourceC1226
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1226, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1227 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1227 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1227 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1227 : Integer.Sparse Master := [(Sum.inr 802, 1), (Sum.inr 804, 1), (Sum.inr 808, 2), (Sum.inr 847, 1), (Sum.inr 1723, 1), (Sum.inr 4070, -1)]

theorem sourceEq1227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1227 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1227 + difference 0 0) (sourceB1227 + difference 0 0) sourceC1227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1227 + difference 0 0) (sourceB1227 + difference 0 0) sourceC1227) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1227 sourceB1227 sourceC1227 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1227 + difference 1 0) (sourceB1227 + difference 0 1) sourceC1227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 802) := by
    have ha : (tripleCharges (sourceA1227 + difference 1 0) (sourceB1227 + difference 0 1) sourceC1227) = raw20206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1227 sourceB1227 sourceC1227 difference raw20206; decide +kernel
    rw [ha]
    exact (canonical20206 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1227 + difference 2 0) (sourceB1227 + difference 0 2) sourceC1227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 808) := by
    have ha : (tripleCharges (sourceA1227 + difference 2 0) (sourceB1227 + difference 0 2) sourceC1227) = raw20207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1227 sourceB1227 sourceC1227 difference raw20207; decide +kernel
    rw [ha]
    exact (canonical20207 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1227 + difference 3 0) (sourceB1227 + difference 0 3) sourceC1227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 808) := by
    have ha : (tripleCharges (sourceA1227 + difference 3 0) (sourceB1227 + difference 0 3) sourceC1227) = raw20155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1227 sourceB1227 sourceC1227 difference raw20155; decide +kernel
    rw [ha]
    exact (canonical20155 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1227 + difference 4 0) (sourceB1227 + difference 0 4) sourceC1227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1227 + difference 4 0) (sourceB1227 + difference 0 4) sourceC1227) = raw20208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1227 sourceB1227 sourceC1227 difference raw20208; decide +kernel
    rw [ha]
    exact (canonical20208 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1227 + difference 5 0) (sourceB1227 + difference 0 5) sourceC1227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1227 + difference 5 0) (sourceB1227 + difference 0 5) sourceC1227) = raw20209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1227 sourceB1227 sourceC1227 difference raw20209; decide +kernel
    rw [ha]
    exact (canonical20209 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1227 + sourceB1227) sourceC1227) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1227 + sourceB1227) sourceC1227) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1227 sourceB1227 sourceC1227 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1227 sourceB1227 sourceC1227
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1227, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1228 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1228 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1228 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1228 : Integer.Sparse Master := [(Sum.inr 847, 1), (Sum.inr 1613, 1), (Sum.inr 1723, 1), (Sum.inr 1744, 1), (Sum.inr 1750, 2), (Sum.inr 4070, -1)]

theorem sourceEq1228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1228 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 0) (sourceB1228 + difference 0 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 0) (sourceB1228 + difference 0 4) sourceC1228) = raw20208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20208; decide +kernel
    rw [ha]
    exact (canonical20208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 1) (sourceB1228 + difference 1 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1613) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 1) (sourceB1228 + difference 1 4) sourceC1228) = raw20210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20210; decide +kernel
    rw [ha]
    exact (canonical20210 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 2) (sourceB1228 + difference 2 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 2) (sourceB1228 + difference 2 4) sourceC1228) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 3) (sourceB1228 + difference 3 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 3) (sourceB1228 + difference 3 4) sourceC1228) = raw20211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20211; decide +kernel
    rw [ha]
    exact (canonical20211 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 4) (sourceB1228 + difference 4 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 4) (sourceB1228 + difference 4 4) sourceC1228) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 5) (sourceB1228 + difference 5 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 5) (sourceB1228 + difference 5 4) sourceC1228) = raw20131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20131; decide +kernel
    rw [ha]
    exact (canonical20131 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1228 + sourceB1228) sourceC1228) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1228 + sourceB1228) sourceC1228) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1228 sourceB1228 sourceC1228 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1228 sourceB1228 sourceC1228
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1228, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1229 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1229 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1229 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1229 : Integer.Sparse Master := [(Sum.inr 804, 1), (Sum.inr 1596, 1), (Sum.inr 1643, 1), (Sum.inr 1723, 1), (Sum.inr 1725, 2), (Sum.inr 4070, -1)]

theorem sourceEq1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1229 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 0) (sourceB1229 + difference 0 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 0) (sourceB1229 + difference 0 5) sourceC1229) = raw20209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20209; decide +kernel
    rw [ha]
    exact (canonical20209 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 1) (sourceB1229 + difference 1 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1596) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 1) (sourceB1229 + difference 1 5) sourceC1229) = raw20212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20212; decide +kernel
    rw [ha]
    exact (canonical20212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 2) (sourceB1229 + difference 2 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 2) (sourceB1229 + difference 2 5) sourceC1229) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 3) (sourceB1229 + difference 3 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 3) (sourceB1229 + difference 3 5) sourceC1229) = raw20213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20213; decide +kernel
    rw [ha]
    exact (canonical20213 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 4) (sourceB1229 + difference 4 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1643) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 4) (sourceB1229 + difference 4 5) sourceC1229) = raw20214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20214; decide +kernel
    rw [ha]
    exact (canonical20214 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 5) (sourceB1229 + difference 5 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 5) (sourceB1229 + difference 5 5) sourceC1229) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1229 + sourceB1229) sourceC1229) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1229 + sourceB1229) sourceC1229) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1229 sourceB1229 sourceC1229 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1229 sourceB1229 sourceC1229
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1229, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1230 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1230 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1230 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1230 : Integer.Sparse Master := [(Sum.inr 1717, 1), (Sum.inr 1718, 2), (Sum.inr 1723, 1), (Sum.inr 1744, 1), (Sum.inr 1942, 1), (Sum.inr 4070, -1)]

theorem sourceEq1230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1230 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1230 + difference 0 5) (sourceB1230 + difference 5 0) sourceC1230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1942) := by
    have ha : (tripleCharges (sourceA1230 + difference 0 5) (sourceB1230 + difference 5 0) sourceC1230) = raw20205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1230 sourceB1230 sourceC1230 difference raw20205; decide +kernel
    rw [ha]
    exact (canonical20205 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1230 + difference 1 5) (sourceB1230 + difference 5 1) sourceC1230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1717) := by
    have ha : (tripleCharges (sourceA1230 + difference 1 5) (sourceB1230 + difference 5 1) sourceC1230) = raw20215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1230 sourceB1230 sourceC1230 difference raw20215; decide +kernel
    rw [ha]
    exact (canonical20215 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1230 + difference 2 5) (sourceB1230 + difference 5 2) sourceC1230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1718) := by
    have ha : (tripleCharges (sourceA1230 + difference 2 5) (sourceB1230 + difference 5 2) sourceC1230) = raw20216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1230 sourceB1230 sourceC1230 difference raw20216; decide +kernel
    rw [ha]
    exact (canonical20216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1230 + difference 3 5) (sourceB1230 + difference 5 3) sourceC1230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1718) := by
    have ha : (tripleCharges (sourceA1230 + difference 3 5) (sourceB1230 + difference 5 3) sourceC1230) = raw20168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1230 sourceB1230 sourceC1230 difference raw20168; decide +kernel
    rw [ha]
    exact (canonical20168 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1230 + difference 4 5) (sourceB1230 + difference 5 4) sourceC1230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1230 + difference 4 5) (sourceB1230 + difference 5 4) sourceC1230) = raw20131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1230 sourceB1230 sourceC1230 difference raw20131; decide +kernel
    rw [ha]
    exact (canonical20131 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1230 + difference 5 5) (sourceB1230 + difference 5 5) sourceC1230) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1230 + difference 5 5) (sourceB1230 + difference 5 5) sourceC1230) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1230 sourceB1230 sourceC1230 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1230 + sourceB1230) sourceC1230) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1230 + sourceB1230) sourceC1230) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1230 sourceB1230 sourceC1230 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1230 sourceB1230 sourceC1230
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1230, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1231 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1231 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC1231 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm1231 : Integer.Sparse Master := [(Sum.inr 585, 1), (Sum.inr 909, 1), (Sum.inr 949, 1), (Sum.inr 1024, 2), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

theorem sourceEq1231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1231 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 0) (sourceB1231 + difference 0 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 585) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 0) (sourceB1231 + difference 0 2) sourceC1231) = raw20217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw20217; decide +kernel
    rw [ha]
    exact (canonical20217 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 1) (sourceB1231 + difference 1 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 909) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 1) (sourceB1231 + difference 1 2) sourceC1231) = raw20218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw20218; decide +kernel
    rw [ha]
    exact (canonical20218 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 2) (sourceB1231 + difference 2 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 2) (sourceB1231 + difference 2 2) sourceC1231) = raw3838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw3838; decide +kernel
    rw [ha]
    exact (canonical3838 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 3) (sourceB1231 + difference 3 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 949) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 3) (sourceB1231 + difference 3 2) sourceC1231) = raw20219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw20219; decide +kernel
    rw [ha]
    exact (canonical20219 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 4) (sourceB1231 + difference 4 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 4) (sourceB1231 + difference 4 2) sourceC1231) = raw3836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw3836; decide +kernel
    rw [ha]
    exact (canonical3836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 5) (sourceB1231 + difference 5 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 5) (sourceB1231 + difference 5 2) sourceC1231) = raw20220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw20220; decide +kernel
    rw [ha]
    exact (canonical20220 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1231 + sourceB1231) sourceC1231) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1231 + sourceB1231) sourceC1231) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA1231 sourceB1231 sourceC1231 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1231 sourceB1231 sourceC1231
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1231, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1232 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1232 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC1232 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceForm1232 : Integer.Sparse Master := [(Sum.inr 911, 1), (Sum.inr 1326, 1), (Sum.inr 1332, 1), (Sum.inr 1336, 1), (Sum.inr 1385, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

theorem sourceEq1232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1232 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1232 + difference 0 2) (sourceB1232 + difference 2 0) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1232 + difference 0 2) (sourceB1232 + difference 2 0) sourceC1232) = raw9473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw9473; decide +kernel
    rw [ha]
    exact (canonical9473 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1232 + difference 1 2) (sourceB1232 + difference 2 1) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1326) := by
    have ha : (tripleCharges (sourceA1232 + difference 1 2) (sourceB1232 + difference 2 1) sourceC1232) = raw20221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw20221; decide +kernel
    rw [ha]
    exact (canonical20221 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1232 + difference 2 2) (sourceB1232 + difference 2 2) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA1232 + difference 2 2) (sourceB1232 + difference 2 2) sourceC1232) = raw9462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw9462; decide +kernel
    rw [ha]
    exact (canonical9462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1232 + difference 3 2) (sourceB1232 + difference 2 3) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1336) := by
    have ha : (tripleCharges (sourceA1232 + difference 3 2) (sourceB1232 + difference 2 3) sourceC1232) = raw20222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw20222; decide +kernel
    rw [ha]
    exact (canonical20222 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1232 + difference 4 2) (sourceB1232 + difference 2 4) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1332) := by
    have ha : (tripleCharges (sourceA1232 + difference 4 2) (sourceB1232 + difference 2 4) sourceC1232) = raw20223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw20223; decide +kernel
    rw [ha]
    exact (canonical20223 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1232 + difference 5 2) (sourceB1232 + difference 2 5) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1232 + difference 5 2) (sourceB1232 + difference 2 5) sourceC1232) = raw20224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw20224; decide +kernel
    rw [ha]
    exact (canonical20224 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1232 + sourceB1232) sourceC1232) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1232 + sourceB1232) sourceC1232) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA1232 sourceB1232 sourceC1232 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1232 sourceB1232 sourceC1232
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1232, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1233 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB1233 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC1233 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1233 : Integer.Sparse Master := [(Sum.inr 997, 1), (Sum.inr 1744, 1), (Sum.inr 1942, 1), (Sum.inr 1995, 1), (Sum.inr 2226, 2), (Sum.inr 4070, -1)]

theorem sourceEq1233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1233 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 0) (sourceB1233 + difference 0 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 0) (sourceB1233 + difference 0 0) sourceC1233) = raw20131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20131; decide +kernel
    rw [ha]
    exact (canonical20131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 1) (sourceB1233 + difference 1 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1995) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 1) (sourceB1233 + difference 1 0) sourceC1233) = raw20225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20225; decide +kernel
    rw [ha]
    exact (canonical20225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 2) (sourceB1233 + difference 2 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 2) (sourceB1233 + difference 2 0) sourceC1233) = raw20123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20123; decide +kernel
    rw [ha]
    exact (canonical20123 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 3) (sourceB1233 + difference 3 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 3) (sourceB1233 + difference 3 0) sourceC1233) = raw20226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20226; decide +kernel
    rw [ha]
    exact (canonical20226 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 4) (sourceB1233 + difference 4 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1942) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 4) (sourceB1233 + difference 4 0) sourceC1233) = raw20205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20205; decide +kernel
    rw [ha]
    exact (canonical20205 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 5) (sourceB1233 + difference 5 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 997) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 5) (sourceB1233 + difference 5 0) sourceC1233) = raw20227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20227; decide +kernel
    rw [ha]
    exact (canonical20227 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1233 + sourceB1233) sourceC1233) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1233 + sourceB1233) sourceC1233) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1233 sourceB1233 sourceC1233 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1233 sourceB1233 sourceC1233
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1233, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1234 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB1234 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC1234 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1234 : Integer.Sparse Master := [(Sum.inr 833, 1), (Sum.inr 834, 1), (Sum.inr 835, 2), (Sum.inr 847, 1), (Sum.inr 1744, 1), (Sum.inr 4070, -1)]

theorem sourceEq1234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1234 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1234 + difference 0 0) (sourceB1234 + difference 0 0) sourceC1234) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1234 + difference 0 0) (sourceB1234 + difference 0 0) sourceC1234) = raw20131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1234 sourceB1234 sourceC1234 difference raw20131; decide +kernel
    rw [ha]
    exact (canonical20131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1234 + difference 1 0) (sourceB1234 + difference 0 1) sourceC1234) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 833) := by
    have ha : (tripleCharges (sourceA1234 + difference 1 0) (sourceB1234 + difference 0 1) sourceC1234) = raw20228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1234 sourceB1234 sourceC1234 difference raw20228; decide +kernel
    rw [ha]
    exact (canonical20228 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1234 + difference 2 0) (sourceB1234 + difference 0 2) sourceC1234) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 835) := by
    have ha : (tripleCharges (sourceA1234 + difference 2 0) (sourceB1234 + difference 0 2) sourceC1234) = raw20229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1234 sourceB1234 sourceC1234 difference raw20229; decide +kernel
    rw [ha]
    exact (canonical20229 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1234 + difference 3 0) (sourceB1234 + difference 0 3) sourceC1234) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 835) := by
    have ha : (tripleCharges (sourceA1234 + difference 3 0) (sourceB1234 + difference 0 3) sourceC1234) = raw20181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1234 sourceB1234 sourceC1234 difference raw20181; decide +kernel
    rw [ha]
    exact (canonical20181 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1234 + difference 4 0) (sourceB1234 + difference 0 4) sourceC1234) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 834) := by
    have ha : (tripleCharges (sourceA1234 + difference 4 0) (sourceB1234 + difference 0 4) sourceC1234) = raw20126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1234 sourceB1234 sourceC1234 difference raw20126; decide +kernel
    rw [ha]
    exact (canonical20126 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1234 + difference 5 0) (sourceB1234 + difference 0 5) sourceC1234) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1234 + difference 5 0) (sourceB1234 + difference 0 5) sourceC1234) = raw20208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1234 sourceB1234 sourceC1234 difference raw20208; decide +kernel
    rw [ha]
    exact (canonical20208 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1234 + sourceB1234) sourceC1234) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1234 + sourceB1234) sourceC1234) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1234 sourceB1234 sourceC1234 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1234 sourceB1234 sourceC1234
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1234, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1235 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1235 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC1235 : Charge := ![1, 0, 1, 2, -1, -3]
def sourceForm1235 : Integer.Sparse Master := [(Sum.inr 1355, 1), (Sum.inr 1902, 1), (Sum.inr 1915, 1), (Sum.inr 1926, 1), (Sum.inr 2197, 1), (Sum.inr 3024, 1), (Sum.inr 4080, -1)]

theorem sourceEq1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1235 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 0) (sourceB1235 + difference 0 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1355) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 0) (sourceB1235 + difference 0 0) sourceC1235) = raw20230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20230; decide +kernel
    rw [ha]
    exact (canonical20230 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 1) (sourceB1235 + difference 1 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1902) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 1) (sourceB1235 + difference 1 0) sourceC1235) = raw20231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20231; decide +kernel
    rw [ha]
    exact (canonical20231 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 2) (sourceB1235 + difference 2 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 2) (sourceB1235 + difference 2 0) sourceC1235) = raw20232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20232; decide +kernel
    rw [ha]
    exact (canonical20232 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 3) (sourceB1235 + difference 3 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 3) (sourceB1235 + difference 3 0) sourceC1235) = raw20233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20233; decide +kernel
    rw [ha]
    exact (canonical20233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 4) (sourceB1235 + difference 4 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 4) (sourceB1235 + difference 4 0) sourceC1235) = raw20234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20234; decide +kernel
    rw [ha]
    exact (canonical20234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 5) (sourceB1235 + difference 5 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 5) (sourceB1235 + difference 5 0) sourceC1235) = raw20235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20235; decide +kernel
    rw [ha]
    exact (canonical20235 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1235 + sourceB1235) sourceC1235) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1235 + sourceB1235) sourceC1235) = raw20236 := by
      apply Matrix.ext; unfold doubleCharges sourceA1235 sourceB1235 sourceC1235 raw20236; decide +kernel
    rw [ha]
    exact (canonical20236 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1235 sourceB1235 sourceC1235
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1235, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1236 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1236 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1236 : Charge := ![1, 1, 1, 1, -1, -3]
def sourceForm1236 : Integer.Sparse Master := [(Sum.inr 1376, 1), (Sum.inr 1898, 3), (Sum.inr 2187, 1), (Sum.inr 3058, 1), (Sum.inr 4079, -1)]

theorem sourceEq1236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1236 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1236 + difference 0 0) (sourceB1236 + difference 0 0) sourceC1236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1376) := by
    have ha : (tripleCharges (sourceA1236 + difference 0 0) (sourceB1236 + difference 0 0) sourceC1236) = raw20237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1236 sourceB1236 sourceC1236 difference raw20237; decide +kernel
    rw [ha]
    exact (canonical20237 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1236 + difference 0 1) (sourceB1236 + difference 1 0) sourceC1236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1236 + difference 0 1) (sourceB1236 + difference 1 0) sourceC1236) = raw20238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1236 sourceB1236 sourceC1236 difference raw20238; decide +kernel
    rw [ha]
    exact (canonical20238 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1236 + difference 0 2) (sourceB1236 + difference 2 0) sourceC1236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1236 + difference 0 2) (sourceB1236 + difference 2 0) sourceC1236) = raw20239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1236 sourceB1236 sourceC1236 difference raw20239; decide +kernel
    rw [ha]
    exact (canonical20239 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1236 + difference 0 3) (sourceB1236 + difference 3 0) sourceC1236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1236 + difference 0 3) (sourceB1236 + difference 3 0) sourceC1236) = raw20240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1236 sourceB1236 sourceC1236 difference raw20240; decide +kernel
    rw [ha]
    exact (canonical20240 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1236 + difference 0 4) (sourceB1236 + difference 4 0) sourceC1236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA1236 + difference 0 4) (sourceB1236 + difference 4 0) sourceC1236) = raw20241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1236 sourceB1236 sourceC1236 difference raw20241; decide +kernel
    rw [ha]
    exact (canonical20241 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1236 + difference 0 5) (sourceB1236 + difference 5 0) sourceC1236) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA1236 + difference 0 5) (sourceB1236 + difference 5 0) sourceC1236) = raw20242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1236 sourceB1236 sourceC1236 difference raw20242; decide +kernel
    rw [ha]
    exact (canonical20242 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1236 + sourceB1236) sourceC1236) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1236 + sourceB1236) sourceC1236) = raw20243 := by
      apply Matrix.ext; unfold doubleCharges sourceA1236 sourceB1236 sourceC1236 raw20243; decide +kernel
    rw [ha]
    exact (canonical20243 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1236 sourceB1236 sourceC1236
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1236, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1237 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1237 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1237 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm1237 : Integer.Sparse Master := [(Sum.inr 1132, 2), (Sum.inr 1142, 1), (Sum.inr 1145, 1), (Sum.inr 1243, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

theorem sourceEq1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1237 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1237 + difference 0 1) (sourceB1237 + difference 1 0) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1237 + difference 0 1) (sourceB1237 + difference 1 0) sourceC1237) = raw4020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw4020; decide +kernel
    rw [ha]
    exact (canonical4020 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1237 + difference 1 1) (sourceB1237 + difference 1 1) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1237 + difference 1 1) (sourceB1237 + difference 1 1) sourceC1237) = raw4012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw4012; decide +kernel
    rw [ha]
    exact (canonical4012 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1237 + difference 2 1) (sourceB1237 + difference 1 2) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1237 + difference 2 1) (sourceB1237 + difference 1 2) sourceC1237) = raw20244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw20244; decide +kernel
    rw [ha]
    exact (canonical20244 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1237 + difference 3 1) (sourceB1237 + difference 1 3) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1237 + difference 3 1) (sourceB1237 + difference 1 3) sourceC1237) = raw20245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw20245; decide +kernel
    rw [ha]
    exact (canonical20245 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1237 + difference 4 1) (sourceB1237 + difference 1 4) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1237 + difference 4 1) (sourceB1237 + difference 1 4) sourceC1237) = raw20246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw20246; decide +kernel
    rw [ha]
    exact (canonical20246 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1237 + difference 5 1) (sourceB1237 + difference 1 5) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1237 + difference 5 1) (sourceB1237 + difference 1 5) sourceC1237) = raw20247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw20247; decide +kernel
    rw [ha]
    exact (canonical20247 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1237 + sourceB1237) sourceC1237) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1237 + sourceB1237) sourceC1237) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1237 sourceB1237 sourceC1237 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1237 sourceB1237 sourceC1237
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1237, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1238 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1238 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1238 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm1238 : Integer.Sparse Master := [(Sum.inr 636, 1), (Sum.inr 1145, 1), (Sum.inr 1155, 2), (Sum.inr 1243, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

theorem sourceEq1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1238 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 0) (sourceB1238 + difference 0 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 636) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 0) (sourceB1238 + difference 0 4) sourceC1238) = raw20248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20248; decide +kernel
    rw [ha]
    exact (canonical20248 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 1) (sourceB1238 + difference 1 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 1) (sourceB1238 + difference 1 4) sourceC1238) = raw20246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20246; decide +kernel
    rw [ha]
    exact (canonical20246 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 2) (sourceB1238 + difference 2 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1155) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 2) (sourceB1238 + difference 2 4) sourceC1238) = raw20249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20249; decide +kernel
    rw [ha]
    exact (canonical20249 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 3) (sourceB1238 + difference 3 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1155) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 3) (sourceB1238 + difference 3 4) sourceC1238) = raw20250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20250; decide +kernel
    rw [ha]
    exact (canonical20250 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 4) (sourceB1238 + difference 4 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 4) (sourceB1238 + difference 4 4) sourceC1238) = raw4012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw4012; decide +kernel
    rw [ha]
    exact (canonical4012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 5) (sourceB1238 + difference 5 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 5) (sourceB1238 + difference 5 4) sourceC1238) = raw20251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20251; decide +kernel
    rw [ha]
    exact (canonical20251 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1238 + sourceB1238) sourceC1238) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1238 + sourceB1238) sourceC1238) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1238 sourceB1238 sourceC1238 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1238 sourceB1238 sourceC1238
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1238, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1239 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1239 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1239 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm1239 : Integer.Sparse Master := [(Sum.inr 641, 1), (Sum.inr 1159, 2), (Sum.inr 1242, 1), (Sum.inr 1264, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

theorem sourceEq1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1239 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 0) (sourceB1239 + difference 0 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 641) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 0) (sourceB1239 + difference 0 1) sourceC1239) = raw20252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw20252; decide +kernel
    rw [ha]
    exact (canonical20252 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 1) (sourceB1239 + difference 1 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 1) (sourceB1239 + difference 1 1) sourceC1239) = raw4909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw4909; decide +kernel
    rw [ha]
    exact (canonical4909 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 2) (sourceB1239 + difference 2 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1159) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 2) (sourceB1239 + difference 2 1) sourceC1239) = raw20253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw20253; decide +kernel
    rw [ha]
    exact (canonical20253 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 3) (sourceB1239 + difference 3 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1159) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 3) (sourceB1239 + difference 3 1) sourceC1239) = raw20254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw20254; decide +kernel
    rw [ha]
    exact (canonical20254 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 4) (sourceB1239 + difference 4 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 4) (sourceB1239 + difference 4 1) sourceC1239) = raw4906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw4906; decide +kernel
    rw [ha]
    exact (canonical4906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 5) (sourceB1239 + difference 5 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 5) (sourceB1239 + difference 5 1) sourceC1239) = raw9580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw9580; decide +kernel
    rw [ha]
    exact (canonical9580 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1239 + sourceB1239) sourceC1239) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1239 + sourceB1239) sourceC1239) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA1239 sourceB1239 sourceC1239 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1239 sourceB1239 sourceC1239
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1239, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1240 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1240 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1240 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1240 : Integer.Sparse Master := [(Sum.inr 1643, 2), (Sum.inr 1647, 1), (Sum.inr 1652, 1), (Sum.inr 1725, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

theorem sourceEq1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1240 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 0) (sourceB1240 + difference 0 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 0) (sourceB1240 + difference 0 0) sourceC1240) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 1) (sourceB1240 + difference 1 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1652) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 1) (sourceB1240 + difference 1 0) sourceC1240) = raw20256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20256; decide +kernel
    rw [ha]
    exact (canonical20256 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 2) (sourceB1240 + difference 2 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1643) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 2) (sourceB1240 + difference 2 0) sourceC1240) = raw20257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20257; decide +kernel
    rw [ha]
    exact (canonical20257 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 3) (sourceB1240 + difference 3 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1643) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 3) (sourceB1240 + difference 3 0) sourceC1240) = raw20258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20258; decide +kernel
    rw [ha]
    exact (canonical20258 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 4) (sourceB1240 + difference 4 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 4) (sourceB1240 + difference 4 0) sourceC1240) = raw20259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20259; decide +kernel
    rw [ha]
    exact (canonical20259 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 5) (sourceB1240 + difference 5 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 5) (sourceB1240 + difference 5 0) sourceC1240) = raw20260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20260; decide +kernel
    rw [ha]
    exact (canonical20260 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1240 + sourceB1240) sourceC1240) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1240 + sourceB1240) sourceC1240) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1240 sourceB1240 sourceC1240 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1240 sourceB1240 sourceC1240
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1240, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1241 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1241 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1241 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1241 : Integer.Sparse Master := [(Sum.inr 1619, 2), (Sum.inr 1628, 1), (Sum.inr 1630, 1), (Sum.inr 1756, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

theorem sourceEq1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1241 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1241 + difference 0 0) (sourceB1241 + difference 0 0) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1241 + difference 0 0) (sourceB1241 + difference 0 0) sourceC1241) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1241 + difference 1 0) (sourceB1241 + difference 0 1) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1241 + difference 1 0) (sourceB1241 + difference 0 1) sourceC1241) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1241 + difference 2 0) (sourceB1241 + difference 0 2) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1241 + difference 2 0) (sourceB1241 + difference 0 2) sourceC1241) = raw20261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20261; decide +kernel
    rw [ha]
    exact (canonical20261 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1241 + difference 3 0) (sourceB1241 + difference 0 3) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1241 + difference 3 0) (sourceB1241 + difference 0 3) sourceC1241) = raw20134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20134; decide +kernel
    rw [ha]
    exact (canonical20134 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1241 + difference 4 0) (sourceB1241 + difference 0 4) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA1241 + difference 4 0) (sourceB1241 + difference 0 4) sourceC1241) = raw20105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20105; decide +kernel
    rw [ha]
    exact (canonical20105 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1241 + difference 5 0) (sourceB1241 + difference 0 5) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1241 + difference 5 0) (sourceB1241 + difference 0 5) sourceC1241) = raw20262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20262; decide +kernel
    rw [ha]
    exact (canonical20262 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1241 + sourceB1241) sourceC1241) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1241 + sourceB1241) sourceC1241) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1241 sourceB1241 sourceC1241 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1241 sourceB1241 sourceC1241
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1241, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1242 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1242 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1242 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1242 : Integer.Sparse Master := [(Sum.inr 1756, 1), (Sum.inr 2289, 1), (Sum.inr 3302, 3), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem sourceEq1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1242 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 0) (sourceB1242 + difference 0 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 0) (sourceB1242 + difference 0 1) sourceC1242) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 1) (sourceB1242 + difference 1 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 1) (sourceB1242 + difference 1 1) sourceC1242) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 2) (sourceB1242 + difference 2 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 2) (sourceB1242 + difference 2 1) sourceC1242) = raw20263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20263; decide +kernel
    rw [ha]
    exact (canonical20263 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 3) (sourceB1242 + difference 3 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 3) (sourceB1242 + difference 3 1) sourceC1242) = raw20264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20264; decide +kernel
    rw [ha]
    exact (canonical20264 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 4) (sourceB1242 + difference 4 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 4) (sourceB1242 + difference 4 1) sourceC1242) = raw20265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20265; decide +kernel
    rw [ha]
    exact (canonical20265 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 5) (sourceB1242 + difference 5 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 5) (sourceB1242 + difference 5 1) sourceC1242) = raw20097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20097; decide +kernel
    rw [ha]
    exact (canonical20097 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1242 + sourceB1242) sourceC1242) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1242 + sourceB1242) sourceC1242) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1242 sourceB1242 sourceC1242 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1242 sourceB1242 sourceC1242
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1242, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1243 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1243 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1243 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1243 : Integer.Sparse Master := [(Sum.inr 1725, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem sourceEq1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1243 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1243 + difference 0 4) (sourceB1243 + difference 4 0) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1243 + difference 0 4) (sourceB1243 + difference 4 0) sourceC1243) = raw20259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20259; decide +kernel
    rw [ha]
    exact (canonical20259 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1243 + difference 1 4) (sourceB1243 + difference 4 1) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1243 + difference 1 4) (sourceB1243 + difference 4 1) sourceC1243) = raw20265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20265; decide +kernel
    rw [ha]
    exact (canonical20265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1243 + difference 2 4) (sourceB1243 + difference 4 2) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1243 + difference 2 4) (sourceB1243 + difference 4 2) sourceC1243) = raw20266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20266; decide +kernel
    rw [ha]
    exact (canonical20266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1243 + difference 3 4) (sourceB1243 + difference 4 3) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1243 + difference 3 4) (sourceB1243 + difference 4 3) sourceC1243) = raw20267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20267; decide +kernel
    rw [ha]
    exact (canonical20267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1243 + difference 4 4) (sourceB1243 + difference 4 4) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1243 + difference 4 4) (sourceB1243 + difference 4 4) sourceC1243) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1243 + difference 5 4) (sourceB1243 + difference 4 5) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1243 + difference 5 4) (sourceB1243 + difference 4 5) sourceC1243) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1243 + sourceB1243) sourceC1243) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1243 + sourceB1243) sourceC1243) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1243 sourceB1243 sourceC1243 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1243 sourceB1243 sourceC1243
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1243, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1244 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1244 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1244 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1244 : Integer.Sparse Master := [(Sum.inr 1630, 1), (Sum.inr 3247, 1), (Sum.inr 3283, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

theorem sourceEq1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1244 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 0) (sourceB1244 + difference 0 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 0) (sourceB1244 + difference 0 5) sourceC1244) = raw20262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20262; decide +kernel
    rw [ha]
    exact (canonical20262 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 1) (sourceB1244 + difference 1 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3247) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 1) (sourceB1244 + difference 1 5) sourceC1244) = raw20269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20269; decide +kernel
    rw [ha]
    exact (canonical20269 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 2) (sourceB1244 + difference 2 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3283) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 2) (sourceB1244 + difference 2 5) sourceC1244) = raw20270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20270; decide +kernel
    rw [ha]
    exact (canonical20270 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 3) (sourceB1244 + difference 3 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3283) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 3) (sourceB1244 + difference 3 5) sourceC1244) = raw20271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20271; decide +kernel
    rw [ha]
    exact (canonical20271 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 4) (sourceB1244 + difference 4 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 4) (sourceB1244 + difference 4 5) sourceC1244) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 5) (sourceB1244 + difference 5 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 5) (sourceB1244 + difference 5 5) sourceC1244) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1244 + sourceB1244) sourceC1244) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1244 + sourceB1244) sourceC1244) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1244 sourceB1244 sourceC1244 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1244 sourceB1244 sourceC1244
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1244, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1245 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1245 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1245 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1245 : Integer.Sparse Master := [(Sum.inr 1647, 1), (Sum.inr 2045, 2), (Sum.inr 2064, 1), (Sum.inr 2289, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

theorem sourceEq1245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1245 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1245 + difference 0 5) (sourceB1245 + difference 5 0) sourceC1245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1245 + difference 0 5) (sourceB1245 + difference 5 0) sourceC1245) = raw20260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1245 sourceB1245 sourceC1245 difference raw20260; decide +kernel
    rw [ha]
    exact (canonical20260 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1245 + difference 1 5) (sourceB1245 + difference 5 1) sourceC1245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1245 + difference 1 5) (sourceB1245 + difference 5 1) sourceC1245) = raw20097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1245 sourceB1245 sourceC1245 difference raw20097; decide +kernel
    rw [ha]
    exact (canonical20097 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1245 + difference 2 5) (sourceB1245 + difference 5 2) sourceC1245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA1245 + difference 2 5) (sourceB1245 + difference 5 2) sourceC1245) = raw20272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1245 sourceB1245 sourceC1245 difference raw20272; decide +kernel
    rw [ha]
    exact (canonical20272 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1245 + difference 3 5) (sourceB1245 + difference 5 3) sourceC1245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA1245 + difference 3 5) (sourceB1245 + difference 5 3) sourceC1245) = raw20121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1245 sourceB1245 sourceC1245 difference raw20121; decide +kernel
    rw [ha]
    exact (canonical20121 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1245 + difference 4 5) (sourceB1245 + difference 5 4) sourceC1245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2064) := by
    have ha : (tripleCharges (sourceA1245 + difference 4 5) (sourceB1245 + difference 5 4) sourceC1245) = raw20094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1245 sourceB1245 sourceC1245 difference raw20094; decide +kernel
    rw [ha]
    exact (canonical20094 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1245 + difference 5 5) (sourceB1245 + difference 5 5) sourceC1245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1245 + difference 5 5) (sourceB1245 + difference 5 5) sourceC1245) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1245 sourceB1245 sourceC1245 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1245 + sourceB1245) sourceC1245) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1245 + sourceB1245) sourceC1245) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1245 sourceB1245 sourceC1245 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1245 sourceB1245 sourceC1245
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1245, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1246 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1246 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC1246 : Charge := ![2, -1, 0, 0, 2, -3]
def sourceForm1246 : Integer.Sparse Master := [(Sum.inr 1258, 1), (Sum.inr 2119, 2), (Sum.inr 2130, 1), (Sum.inr 2218, 1), (Sum.inr 2761, 1), (Sum.inr 4082, -1)]

theorem sourceEq1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1246 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 0) (sourceB1246 + difference 0 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1258) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 0) (sourceB1246 + difference 0 0) sourceC1246) = raw19492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw19492; decide +kernel
    rw [ha]
    exact (canonical19492 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 1) (sourceB1246 + difference 1 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2130) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 1) (sourceB1246 + difference 1 0) sourceC1246) = raw20273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw20273; decide +kernel
    rw [ha]
    exact (canonical20273 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 2) (sourceB1246 + difference 2 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2119) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 2) (sourceB1246 + difference 2 0) sourceC1246) = raw20274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw20274; decide +kernel
    rw [ha]
    exact (canonical20274 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 3) (sourceB1246 + difference 3 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2119) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 3) (sourceB1246 + difference 3 0) sourceC1246) = raw20275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw20275; decide +kernel
    rw [ha]
    exact (canonical20275 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 4) (sourceB1246 + difference 4 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 4) (sourceB1246 + difference 4 0) sourceC1246) = raw19487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw19487; decide +kernel
    rw [ha]
    exact (canonical19487 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 5) (sourceB1246 + difference 5 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 5) (sourceB1246 + difference 5 0) sourceC1246) = raw20276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw20276; decide +kernel
    rw [ha]
    exact (canonical20276 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1246 + sourceB1246) sourceC1246) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1246 + sourceB1246) sourceC1246) = raw19488 := by
      apply Matrix.ext; unfold doubleCharges sourceA1246 sourceB1246 sourceC1246 raw19488; decide +kernel
    rw [ha]
    exact (canonical19488 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1246 sourceB1246 sourceC1246
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1246, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1247 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1247 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1247 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceForm1247 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 1115, 1), (Sum.inr 1119, 1), (Sum.inr 1131, 1), (Sum.inr 1215, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

theorem sourceEq1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1247 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1247 + difference 0 1) (sourceB1247 + difference 1 0) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1247 + difference 0 1) (sourceB1247 + difference 1 0) sourceC1247) = raw20277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20277; decide +kernel
    rw [ha]
    exact (canonical20277 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1247 + difference 1 1) (sourceB1247 + difference 1 1) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1247 + difference 1 1) (sourceB1247 + difference 1 1) sourceC1247) = raw20278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20278; decide +kernel
    rw [ha]
    exact (canonical20278 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1247 + difference 2 1) (sourceB1247 + difference 1 2) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1111) := by
    have ha : (tripleCharges (sourceA1247 + difference 2 1) (sourceB1247 + difference 1 2) sourceC1247) = raw20279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20279; decide +kernel
    rw [ha]
    exact (canonical20279 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1247 + difference 3 1) (sourceB1247 + difference 1 3) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1247 + difference 3 1) (sourceB1247 + difference 1 3) sourceC1247) = raw20280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20280; decide +kernel
    rw [ha]
    exact (canonical20280 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1247 + difference 4 1) (sourceB1247 + difference 1 4) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1119) := by
    have ha : (tripleCharges (sourceA1247 + difference 4 1) (sourceB1247 + difference 1 4) sourceC1247) = raw20281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20281; decide +kernel
    rw [ha]
    exact (canonical20281 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1247 + difference 5 1) (sourceB1247 + difference 1 5) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1247 + difference 5 1) (sourceB1247 + difference 1 5) sourceC1247) = raw20282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20282; decide +kernel
    rw [ha]
    exact (canonical20282 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1247 + sourceB1247) sourceC1247) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1247 + sourceB1247) sourceC1247) = raw20283 := by
      apply Matrix.ext; unfold doubleCharges sourceA1247 sourceB1247 sourceC1247 raw20283; decide +kernel
    rw [ha]
    exact (canonical20283 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1247 sourceB1247 sourceC1247
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1247, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
