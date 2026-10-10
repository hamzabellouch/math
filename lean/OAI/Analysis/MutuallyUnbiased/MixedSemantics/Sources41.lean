import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical165
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical166

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1312 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1312 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1312 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceForm1312 : Integer.Sparse Master := [(Sum.inr 893, 1), (Sum.inr 1098, 2), (Sum.inr 1103, 1), (Sum.inr 1190, 1), (Sum.inr 1950, 1), (Sum.inr 4082, -1)]

theorem sourceEq1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1312 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1312 + difference 0 3) (sourceB1312 + difference 3 0) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1950) := by
    have ha : (tripleCharges (sourceA1312 + difference 0 3) (sourceB1312 + difference 3 0) sourceC1312) = raw21016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21016; decide +kernel
    rw [ha]
    exact (canonical21016 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1312 + difference 1 3) (sourceB1312 + difference 3 1) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA1312 + difference 1 3) (sourceB1312 + difference 3 1) sourceC1312) = raw21020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21020; decide +kernel
    rw [ha]
    exact (canonical21020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1312 + difference 2 3) (sourceB1312 + difference 3 2) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA1312 + difference 2 3) (sourceB1312 + difference 3 2) sourceC1312) = raw21021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21021; decide +kernel
    rw [ha]
    exact (canonical21021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1312 + difference 3 3) (sourceB1312 + difference 3 3) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1312 + difference 3 3) (sourceB1312 + difference 3 3) sourceC1312) = raw21013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21013; decide +kernel
    rw [ha]
    exact (canonical21013 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1312 + difference 4 3) (sourceB1312 + difference 3 4) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1103) := by
    have ha : (tripleCharges (sourceA1312 + difference 4 3) (sourceB1312 + difference 3 4) sourceC1312) = raw21022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21022; decide +kernel
    rw [ha]
    exact (canonical21022 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1312 + difference 5 3) (sourceB1312 + difference 3 5) sourceC1312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1312 + difference 5 3) (sourceB1312 + difference 3 5) sourceC1312) = raw21023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1312 sourceB1312 sourceC1312 difference raw21023; decide +kernel
    rw [ha]
    exact (canonical21023 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1312 + sourceB1312) sourceC1312) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1312 + sourceB1312) sourceC1312) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA1312 sourceB1312 sourceC1312 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1312 sourceB1312 sourceC1312
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1312, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1313 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1313 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1313 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceForm1313 : Integer.Sparse Master := [(Sum.inr 1184, 2), (Sum.inr 1190, 1), (Sum.inr 1192, 1), (Sum.inr 1287, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

theorem sourceEq1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1313 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1313 + difference 0 5) (sourceB1313 + difference 5 0) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1313 + difference 0 5) (sourceB1313 + difference 5 0) sourceC1313) = raw21018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21018; decide +kernel
    rw [ha]
    exact (canonical21018 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1313 + difference 1 5) (sourceB1313 + difference 5 1) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1184) := by
    have ha : (tripleCharges (sourceA1313 + difference 1 5) (sourceB1313 + difference 5 1) sourceC1313) = raw21024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21024; decide +kernel
    rw [ha]
    exact (canonical21024 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1313 + difference 2 5) (sourceB1313 + difference 5 2) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1184) := by
    have ha : (tripleCharges (sourceA1313 + difference 2 5) (sourceB1313 + difference 5 2) sourceC1313) = raw21025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21025; decide +kernel
    rw [ha]
    exact (canonical21025 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1313 + difference 3 5) (sourceB1313 + difference 5 3) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1287) := by
    have ha : (tripleCharges (sourceA1313 + difference 3 5) (sourceB1313 + difference 5 3) sourceC1313) = raw21026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21026; decide +kernel
    rw [ha]
    exact (canonical21026 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1313 + difference 4 5) (sourceB1313 + difference 5 4) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1192) := by
    have ha : (tripleCharges (sourceA1313 + difference 4 5) (sourceB1313 + difference 5 4) sourceC1313) = raw21027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21027; decide +kernel
    rw [ha]
    exact (canonical21027 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1313 + difference 5 5) (sourceB1313 + difference 5 5) sourceC1313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1313 + difference 5 5) (sourceB1313 + difference 5 5) sourceC1313) = raw21013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1313 sourceB1313 sourceC1313 difference raw21013; decide +kernel
    rw [ha]
    exact (canonical21013 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1313 + sourceB1313) sourceC1313) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1313 + sourceB1313) sourceC1313) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA1313 sourceB1313 sourceC1313 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1313 sourceB1313 sourceC1313
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1313, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1314 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceB1314 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceC1314 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1314 : Integer.Sparse Master := [(Sum.inr 894, 1), (Sum.inr 1543, 2), (Sum.inr 1548, 1), (Sum.inr 1625, 1), (Sum.inr 1952, 1), (Sum.inr 4070, -1)]

theorem sourceEq1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1314 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1314 + difference 0 0) (sourceB1314 + difference 0 0) sourceC1314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1952) := by
    have ha : (tripleCharges (sourceA1314 + difference 0 0) (sourceB1314 + difference 0 0) sourceC1314) = raw21028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1314 sourceB1314 sourceC1314 difference raw21028; decide +kernel
    rw [ha]
    exact (canonical21028 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1314 + difference 1 0) (sourceB1314 + difference 0 1) sourceC1314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1543) := by
    have ha : (tripleCharges (sourceA1314 + difference 1 0) (sourceB1314 + difference 0 1) sourceC1314) = raw21029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1314 sourceB1314 sourceC1314 difference raw21029; decide +kernel
    rw [ha]
    exact (canonical21029 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1314 + difference 2 0) (sourceB1314 + difference 0 2) sourceC1314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1543) := by
    have ha : (tripleCharges (sourceA1314 + difference 2 0) (sourceB1314 + difference 0 2) sourceC1314) = raw21030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1314 sourceB1314 sourceC1314 difference raw21030; decide +kernel
    rw [ha]
    exact (canonical21030 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1314 + difference 3 0) (sourceB1314 + difference 0 3) sourceC1314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1625) := by
    have ha : (tripleCharges (sourceA1314 + difference 3 0) (sourceB1314 + difference 0 3) sourceC1314) = raw20843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1314 sourceB1314 sourceC1314 difference raw20843; decide +kernel
    rw [ha]
    exact (canonical20843 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1314 + difference 4 0) (sourceB1314 + difference 0 4) sourceC1314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1548) := by
    have ha : (tripleCharges (sourceA1314 + difference 4 0) (sourceB1314 + difference 0 4) sourceC1314) = raw21031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1314 sourceB1314 sourceC1314 difference raw21031; decide +kernel
    rw [ha]
    exact (canonical21031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1314 + difference 5 0) (sourceB1314 + difference 0 5) sourceC1314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 894) := by
    have ha : (tripleCharges (sourceA1314 + difference 5 0) (sourceB1314 + difference 0 5) sourceC1314) = raw21032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1314 sourceB1314 sourceC1314 difference raw21032; decide +kernel
    rw [ha]
    exact (canonical21032 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1314 + sourceB1314) sourceC1314) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1314 + sourceB1314) sourceC1314) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1314 sourceB1314 sourceC1314 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1314 sourceB1314 sourceC1314
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1314, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1315 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1315 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC1315 : Charge := ![2, 0, 0, 2, 0, -4]
def sourceForm1315 : Integer.Sparse Master := [(Sum.inr 1186, 1), (Sum.inr 1608, 2), (Sum.inr 1627, 1), (Sum.inr 1741, 1), (Sum.inr 2683, 1), (Sum.inr 4071, -1)]

theorem sourceEq1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1315 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 0) (sourceB1315 + difference 0 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1186) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 0) (sourceB1315 + difference 0 0) sourceC1315) = raw21033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21033; decide +kernel
    rw [ha]
    exact (canonical21033 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 1) (sourceB1315 + difference 1 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 1) (sourceB1315 + difference 1 0) sourceC1315) = raw21034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21034; decide +kernel
    rw [ha]
    exact (canonical21034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 2) (sourceB1315 + difference 2 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 2) (sourceB1315 + difference 2 0) sourceC1315) = raw21035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21035; decide +kernel
    rw [ha]
    exact (canonical21035 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 3) (sourceB1315 + difference 3 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1627) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 3) (sourceB1315 + difference 3 0) sourceC1315) = raw21036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21036; decide +kernel
    rw [ha]
    exact (canonical21036 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 4) (sourceB1315 + difference 4 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 4) (sourceB1315 + difference 4 0) sourceC1315) = raw21037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21037; decide +kernel
    rw [ha]
    exact (canonical21037 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1315 + difference 0 5) (sourceB1315 + difference 5 0) sourceC1315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1315 + difference 0 5) (sourceB1315 + difference 5 0) sourceC1315) = raw21038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1315 sourceB1315 sourceC1315 difference raw21038; decide +kernel
    rw [ha]
    exact (canonical21038 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1315 + sourceB1315) sourceC1315) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1315 + sourceB1315) sourceC1315) = raw21039 := by
      apply Matrix.ext; unfold doubleCharges sourceA1315 sourceB1315 sourceC1315 raw21039; decide +kernel
    rw [ha]
    exact (canonical21039 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1315 sourceB1315 sourceC1315
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1315, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1316 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1316 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1316 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceForm1316 : Integer.Sparse Master := [(Sum.inr 1203, 1), (Sum.inr 2377, 1), (Sum.inr 2385, 2), (Sum.inr 2664, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

theorem sourceEq1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1316 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 0) (sourceB1316 + difference 0 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1203) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 0) (sourceB1316 + difference 0 0) sourceC1316) = raw21040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21040; decide +kernel
    rw [ha]
    exact (canonical21040 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 1) (sourceB1316 + difference 1 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2377) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 1) (sourceB1316 + difference 1 0) sourceC1316) = raw21041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21041; decide +kernel
    rw [ha]
    exact (canonical21041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 2) (sourceB1316 + difference 2 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 2) (sourceB1316 + difference 2 0) sourceC1316) = raw21042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21042; decide +kernel
    rw [ha]
    exact (canonical21042 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 3) (sourceB1316 + difference 3 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 3) (sourceB1316 + difference 3 0) sourceC1316) = raw21043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21043; decide +kernel
    rw [ha]
    exact (canonical21043 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 4) (sourceB1316 + difference 4 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 4) (sourceB1316 + difference 4 0) sourceC1316) = raw21044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21044; decide +kernel
    rw [ha]
    exact (canonical21044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1316 + difference 0 5) (sourceB1316 + difference 5 0) sourceC1316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1316 + difference 0 5) (sourceB1316 + difference 5 0) sourceC1316) = raw21045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1316 sourceB1316 sourceC1316 difference raw21045; decide +kernel
    rw [ha]
    exact (canonical21045 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1316 + sourceB1316) sourceC1316) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1316 + sourceB1316) sourceC1316) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1316 sourceB1316 sourceC1316 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1316 sourceB1316 sourceC1316
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1316, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1317 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1317 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1317 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceForm1317 : Integer.Sparse Master := [(Sum.inr 1198, 1), (Sum.inr 1203, 1), (Sum.inr 1205, 1), (Sum.inr 1230, 2), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

theorem sourceEq1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1317 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1317 + difference 0 5) (sourceB1317 + difference 5 0) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1317 + difference 0 5) (sourceB1317 + difference 5 0) sourceC1317) = raw21045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21045; decide +kernel
    rw [ha]
    exact (canonical21045 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1317 + difference 1 5) (sourceB1317 + difference 5 1) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1198) := by
    have ha : (tripleCharges (sourceA1317 + difference 1 5) (sourceB1317 + difference 5 1) sourceC1317) = raw21047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21047; decide +kernel
    rw [ha]
    exact (canonical21047 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1317 + difference 2 5) (sourceB1317 + difference 5 2) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA1317 + difference 2 5) (sourceB1317 + difference 5 2) sourceC1317) = raw21048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21048; decide +kernel
    rw [ha]
    exact (canonical21048 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1317 + difference 3 5) (sourceB1317 + difference 5 3) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA1317 + difference 3 5) (sourceB1317 + difference 5 3) sourceC1317) = raw21049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21049; decide +kernel
    rw [ha]
    exact (canonical21049 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1317 + difference 4 5) (sourceB1317 + difference 5 4) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA1317 + difference 4 5) (sourceB1317 + difference 5 4) sourceC1317) = raw21050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21050; decide +kernel
    rw [ha]
    exact (canonical21050 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1317 + difference 5 5) (sourceB1317 + difference 5 5) sourceC1317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1203) := by
    have ha : (tripleCharges (sourceA1317 + difference 5 5) (sourceB1317 + difference 5 5) sourceC1317) = raw21040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1317 sourceB1317 sourceC1317 difference raw21040; decide +kernel
    rw [ha]
    exact (canonical21040 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1317 + sourceB1317) sourceC1317) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1317 + sourceB1317) sourceC1317) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1317 sourceB1317 sourceC1317 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1317 sourceB1317 sourceC1317
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1317, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1318 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1318 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1318 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceForm1318 : Integer.Sparse Master := [(Sum.inr 1202, 1), (Sum.inr 1897, 1), (Sum.inr 1914, 2), (Sum.inr 2193, 1), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

theorem sourceEq1318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1318 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 0) (sourceB1318 + difference 0 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 0) (sourceB1318 + difference 0 0) sourceC1318) = raw21051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21051; decide +kernel
    rw [ha]
    exact (canonical21051 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 1) (sourceB1318 + difference 1 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 1) (sourceB1318 + difference 1 0) sourceC1318) = raw21052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21052; decide +kernel
    rw [ha]
    exact (canonical21052 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 2) (sourceB1318 + difference 2 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 2) (sourceB1318 + difference 2 0) sourceC1318) = raw21053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21053; decide +kernel
    rw [ha]
    exact (canonical21053 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 3) (sourceB1318 + difference 3 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 3) (sourceB1318 + difference 3 0) sourceC1318) = raw21054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21054; decide +kernel
    rw [ha]
    exact (canonical21054 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 4) (sourceB1318 + difference 4 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 4) (sourceB1318 + difference 4 0) sourceC1318) = raw21055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21055; decide +kernel
    rw [ha]
    exact (canonical21055 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1318 + difference 0 5) (sourceB1318 + difference 5 0) sourceC1318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1318 + difference 0 5) (sourceB1318 + difference 5 0) sourceC1318) = raw21056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1318 sourceB1318 sourceC1318 difference raw21056; decide +kernel
    rw [ha]
    exact (canonical21056 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1318 + sourceB1318) sourceC1318) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1318 + sourceB1318) sourceC1318) = raw21057 := by
      apply Matrix.ext; unfold doubleCharges sourceA1318 sourceB1318 sourceC1318 raw21057; decide +kernel
    rw [ha]
    exact (canonical21057 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1318 sourceB1318 sourceC1318
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1318, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1319 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1319 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1319 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceForm1319 : Integer.Sparse Master := [(Sum.inr 871, 1), (Sum.inr 1105, 1), (Sum.inr 1109, 1), (Sum.inr 1123, 1), (Sum.inr 1202, 1), (Sum.inr 1914, 1), (Sum.inr 4080, -1)]

theorem sourceEq1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1319 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1319 + difference 0 2) (sourceB1319 + difference 2 0) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1319 + difference 0 2) (sourceB1319 + difference 2 0) sourceC1319) = raw21053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21053; decide +kernel
    rw [ha]
    exact (canonical21053 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1319 + difference 1 2) (sourceB1319 + difference 2 1) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1105) := by
    have ha : (tripleCharges (sourceA1319 + difference 1 2) (sourceB1319 + difference 2 1) sourceC1319) = raw21058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21058; decide +kernel
    rw [ha]
    exact (canonical21058 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1319 + difference 2 2) (sourceB1319 + difference 2 2) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1319 + difference 2 2) (sourceB1319 + difference 2 2) sourceC1319) = raw21051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21051; decide +kernel
    rw [ha]
    exact (canonical21051 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1319 + difference 3 2) (sourceB1319 + difference 2 3) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1319 + difference 3 2) (sourceB1319 + difference 2 3) sourceC1319) = raw21059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21059; decide +kernel
    rw [ha]
    exact (canonical21059 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1319 + difference 4 2) (sourceB1319 + difference 2 4) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1109) := by
    have ha : (tripleCharges (sourceA1319 + difference 4 2) (sourceB1319 + difference 2 4) sourceC1319) = raw21060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21060; decide +kernel
    rw [ha]
    exact (canonical21060 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1319 + difference 5 2) (sourceB1319 + difference 2 5) sourceC1319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1319 + difference 5 2) (sourceB1319 + difference 2 5) sourceC1319) = raw21061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1319 sourceB1319 sourceC1319 difference raw21061; decide +kernel
    rw [ha]
    exact (canonical21061 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1319 + sourceB1319) sourceC1319) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1319 + sourceB1319) sourceC1319) = raw21057 := by
      apply Matrix.ext; unfold doubleCharges sourceA1319 sourceB1319 sourceC1319 raw21057; decide +kernel
    rw [ha]
    exact (canonical21057 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1319 sourceB1319 sourceC1319
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1319, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1320 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1320 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1320 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceForm1320 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 1202, 1), (Sum.inr 1204, 1), (Sum.inr 1229, 2), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

theorem sourceEq1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1320 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1320 + difference 0 5) (sourceB1320 + difference 5 0) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1320 + difference 0 5) (sourceB1320 + difference 5 0) sourceC1320) = raw21056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21056; decide +kernel
    rw [ha]
    exact (canonical21056 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1320 + difference 1 5) (sourceB1320 + difference 5 1) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1197) := by
    have ha : (tripleCharges (sourceA1320 + difference 1 5) (sourceB1320 + difference 5 1) sourceC1320) = raw21062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21062; decide +kernel
    rw [ha]
    exact (canonical21062 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1320 + difference 2 5) (sourceB1320 + difference 5 2) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA1320 + difference 2 5) (sourceB1320 + difference 5 2) sourceC1320) = raw21063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21063; decide +kernel
    rw [ha]
    exact (canonical21063 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1320 + difference 3 5) (sourceB1320 + difference 5 3) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA1320 + difference 3 5) (sourceB1320 + difference 5 3) sourceC1320) = raw21064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21064; decide +kernel
    rw [ha]
    exact (canonical21064 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1320 + difference 4 5) (sourceB1320 + difference 5 4) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1204) := by
    have ha : (tripleCharges (sourceA1320 + difference 4 5) (sourceB1320 + difference 5 4) sourceC1320) = raw21065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21065; decide +kernel
    rw [ha]
    exact (canonical21065 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1320 + difference 5 5) (sourceB1320 + difference 5 5) sourceC1320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1320 + difference 5 5) (sourceB1320 + difference 5 5) sourceC1320) = raw21051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1320 sourceB1320 sourceC1320 difference raw21051; decide +kernel
    rw [ha]
    exact (canonical21051 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1320 + sourceB1320) sourceC1320) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1320 + sourceB1320) sourceC1320) = raw21057 := by
      apply Matrix.ext; unfold doubleCharges sourceA1320 sourceB1320 sourceC1320 raw21057; decide +kernel
    rw [ha]
    exact (canonical21057 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1320 sourceB1320 sourceC1320
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1320, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1321 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceB1321 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceC1321 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1321 : Integer.Sparse Master := [(Sum.inr 877, 1), (Sum.inr 1580, 1), (Sum.inr 1584, 1), (Sum.inr 1625, 2), (Sum.inr 1942, 1), (Sum.inr 4070, -1)]

theorem sourceEq1321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1321 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1321 + difference 0 0) (sourceB1321 + difference 0 0) sourceC1321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1942) := by
    have ha : (tripleCharges (sourceA1321 + difference 0 0) (sourceB1321 + difference 0 0) sourceC1321) = raw21066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1321 sourceB1321 sourceC1321 difference raw21066; decide +kernel
    rw [ha]
    exact (canonical21066 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1321 + difference 1 0) (sourceB1321 + difference 0 1) sourceC1321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1580) := by
    have ha : (tripleCharges (sourceA1321 + difference 1 0) (sourceB1321 + difference 0 1) sourceC1321) = raw21067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1321 sourceB1321 sourceC1321 difference raw21067; decide +kernel
    rw [ha]
    exact (canonical21067 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1321 + difference 2 0) (sourceB1321 + difference 0 2) sourceC1321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1625) := by
    have ha : (tripleCharges (sourceA1321 + difference 2 0) (sourceB1321 + difference 0 2) sourceC1321) = raw20843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1321 sourceB1321 sourceC1321 difference raw20843; decide +kernel
    rw [ha]
    exact (canonical20843 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1321 + difference 3 0) (sourceB1321 + difference 0 3) sourceC1321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1625) := by
    have ha : (tripleCharges (sourceA1321 + difference 3 0) (sourceB1321 + difference 0 3) sourceC1321) = raw21068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1321 sourceB1321 sourceC1321 difference raw21068; decide +kernel
    rw [ha]
    exact (canonical21068 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1321 + difference 4 0) (sourceB1321 + difference 0 4) sourceC1321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1584) := by
    have ha : (tripleCharges (sourceA1321 + difference 4 0) (sourceB1321 + difference 0 4) sourceC1321) = raw21069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1321 sourceB1321 sourceC1321 difference raw21069; decide +kernel
    rw [ha]
    exact (canonical21069 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1321 + difference 5 0) (sourceB1321 + difference 0 5) sourceC1321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 877) := by
    have ha : (tripleCharges (sourceA1321 + difference 5 0) (sourceB1321 + difference 0 5) sourceC1321) = raw21070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1321 sourceB1321 sourceC1321 difference raw21070; decide +kernel
    rw [ha]
    exact (canonical21070 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1321 + sourceB1321) sourceC1321) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1321 + sourceB1321) sourceC1321) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1321 sourceB1321 sourceC1321 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1321 sourceB1321 sourceC1321
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1321, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1322 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1322 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC1322 : Charge := ![2, 0, 1, 1, 0, -4]
def sourceForm1322 : Integer.Sparse Master := [(Sum.inr 1199, 1), (Sum.inr 1592, 1), (Sum.inr 1602, 2), (Sum.inr 1710, 1), (Sum.inr 2702, 1), (Sum.inr 4069, -1)]

theorem sourceEq1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1322 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 0) (sourceB1322 + difference 0 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1199) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 0) (sourceB1322 + difference 0 0) sourceC1322) = raw21071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21071; decide +kernel
    rw [ha]
    exact (canonical21071 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 1) (sourceB1322 + difference 1 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1592) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 1) (sourceB1322 + difference 1 0) sourceC1322) = raw21072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21072; decide +kernel
    rw [ha]
    exact (canonical21072 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 2) (sourceB1322 + difference 2 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 2) (sourceB1322 + difference 2 0) sourceC1322) = raw21073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21073; decide +kernel
    rw [ha]
    exact (canonical21073 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 3) (sourceB1322 + difference 3 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 3) (sourceB1322 + difference 3 0) sourceC1322) = raw21074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21074; decide +kernel
    rw [ha]
    exact (canonical21074 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 4) (sourceB1322 + difference 4 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 4) (sourceB1322 + difference 4 0) sourceC1322) = raw21075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21075; decide +kernel
    rw [ha]
    exact (canonical21075 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1322 + difference 0 5) (sourceB1322 + difference 5 0) sourceC1322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1322 + difference 0 5) (sourceB1322 + difference 5 0) sourceC1322) = raw21076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1322 sourceB1322 sourceC1322 difference raw21076; decide +kernel
    rw [ha]
    exact (canonical21076 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1322 + sourceB1322) sourceC1322) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1322 + sourceB1322) sourceC1322) = raw21077 := by
      apply Matrix.ext; unfold doubleCharges sourceA1322 sourceB1322 sourceC1322 raw21077; decide +kernel
    rw [ha]
    exact (canonical21077 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1322 sourceB1322 sourceC1322
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1322, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1323 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1323 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1323 : Charge := ![3, -2, 0, 0, 1, -2]
def sourceForm1323 : Integer.Sparse Master := [(Sum.inr 1055, 1), (Sum.inr 2032, 2), (Sum.inr 2130, 1), (Sum.inr 2218, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

theorem sourceEq1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1323 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 0) (sourceB1323 + difference 0 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1055) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 0) (sourceB1323 + difference 0 0) sourceC1323) = raw21078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21078; decide +kernel
    rw [ha]
    exact (canonical21078 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 1) (sourceB1323 + difference 1 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2130) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 1) (sourceB1323 + difference 1 0) sourceC1323) = raw21079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21079; decide +kernel
    rw [ha]
    exact (canonical21079 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 2) (sourceB1323 + difference 2 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2032) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 2) (sourceB1323 + difference 2 0) sourceC1323) = raw21080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21080; decide +kernel
    rw [ha]
    exact (canonical21080 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 3) (sourceB1323 + difference 3 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2032) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 3) (sourceB1323 + difference 3 0) sourceC1323) = raw21081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21081; decide +kernel
    rw [ha]
    exact (canonical21081 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 4) (sourceB1323 + difference 4 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 4) (sourceB1323 + difference 4 0) sourceC1323) = raw21082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21082; decide +kernel
    rw [ha]
    exact (canonical21082 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1323 + difference 0 5) (sourceB1323 + difference 5 0) sourceC1323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1323 + difference 0 5) (sourceB1323 + difference 5 0) sourceC1323) = raw21083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1323 sourceB1323 sourceC1323 difference raw21083; decide +kernel
    rw [ha]
    exact (canonical21083 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1323 + sourceB1323) sourceC1323) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1323 + sourceB1323) sourceC1323) = raw21084 := by
      apply Matrix.ext; unfold doubleCharges sourceA1323 sourceB1323 sourceC1323 raw21084; decide +kernel
    rw [ha]
    exact (canonical21084 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1323 sourceB1323 sourceC1323
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1323, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1324 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1324 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1324 : Charge := ![3, -2, 0, 0, 1, -2]
def sourceForm1324 : Integer.Sparse Master := [(Sum.inr 1053, 2), (Sum.inr 1055, 1), (Sum.inr 1062, 1), (Sum.inr 1075, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

theorem sourceEq1324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1324 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1324 + difference 0 5) (sourceB1324 + difference 5 0) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1324 + difference 0 5) (sourceB1324 + difference 5 0) sourceC1324) = raw21083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21083; decide +kernel
    rw [ha]
    exact (canonical21083 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1324 + difference 1 5) (sourceB1324 + difference 5 1) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1324 + difference 1 5) (sourceB1324 + difference 5 1) sourceC1324) = raw21085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21085; decide +kernel
    rw [ha]
    exact (canonical21085 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1324 + difference 2 5) (sourceB1324 + difference 5 2) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1053) := by
    have ha : (tripleCharges (sourceA1324 + difference 2 5) (sourceB1324 + difference 5 2) sourceC1324) = raw21086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21086; decide +kernel
    rw [ha]
    exact (canonical21086 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1324 + difference 3 5) (sourceB1324 + difference 5 3) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1053) := by
    have ha : (tripleCharges (sourceA1324 + difference 3 5) (sourceB1324 + difference 5 3) sourceC1324) = raw21087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21087; decide +kernel
    rw [ha]
    exact (canonical21087 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1324 + difference 4 5) (sourceB1324 + difference 5 4) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1062) := by
    have ha : (tripleCharges (sourceA1324 + difference 4 5) (sourceB1324 + difference 5 4) sourceC1324) = raw21088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21088; decide +kernel
    rw [ha]
    exact (canonical21088 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1324 + difference 5 5) (sourceB1324 + difference 5 5) sourceC1324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1055) := by
    have ha : (tripleCharges (sourceA1324 + difference 5 5) (sourceB1324 + difference 5 5) sourceC1324) = raw21078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1324 sourceB1324 sourceC1324 difference raw21078; decide +kernel
    rw [ha]
    exact (canonical21078 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1324 + sourceB1324) sourceC1324) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1324 + sourceB1324) sourceC1324) = raw21084 := by
      apply Matrix.ext; unfold doubleCharges sourceA1324 sourceB1324 sourceC1324 raw21084; decide +kernel
    rw [ha]
    exact (canonical21084 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1324 sourceB1324 sourceC1324
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1324, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1325 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1325 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC1325 : Charge := ![3, -2, 0, 1, -1, -1]
def sourceForm1325 : Integer.Sparse Master := [(Sum.inr 991, 1), (Sum.inr 1926, 1), (Sum.inr 1992, 1), (Sum.inr 2121, 1), (Sum.inr 2197, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

theorem sourceEq1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1325 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 0) (sourceB1325 + difference 0 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 991) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 0) (sourceB1325 + difference 0 0) sourceC1325) = raw21089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21089; decide +kernel
    rw [ha]
    exact (canonical21089 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 1) (sourceB1325 + difference 1 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 1) (sourceB1325 + difference 1 0) sourceC1325) = raw21090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21090; decide +kernel
    rw [ha]
    exact (canonical21090 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 2) (sourceB1325 + difference 2 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1992) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 2) (sourceB1325 + difference 2 0) sourceC1325) = raw21091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21091; decide +kernel
    rw [ha]
    exact (canonical21091 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 3) (sourceB1325 + difference 3 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 3) (sourceB1325 + difference 3 0) sourceC1325) = raw21092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21092; decide +kernel
    rw [ha]
    exact (canonical21092 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 4) (sourceB1325 + difference 4 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 4) (sourceB1325 + difference 4 0) sourceC1325) = raw21093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21093; decide +kernel
    rw [ha]
    exact (canonical21093 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1325 + difference 0 5) (sourceB1325 + difference 5 0) sourceC1325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1325 + difference 0 5) (sourceB1325 + difference 5 0) sourceC1325) = raw21094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1325 sourceB1325 sourceC1325 difference raw21094; decide +kernel
    rw [ha]
    exact (canonical21094 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1325 + sourceB1325) sourceC1325) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1325 + sourceB1325) sourceC1325) = raw21095 := by
      apply Matrix.ext; unfold doubleCharges sourceA1325 sourceB1325 sourceC1325 raw21095; decide +kernel
    rw [ha]
    exact (canonical21095 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1325 sourceB1325 sourceC1325
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1325, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1326 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1326 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC1326 : Charge := ![3, -2, 0, 1, -1, -1]
def sourceForm1326 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 991, 1), (Sum.inr 993, 1), (Sum.inr 1005, 1), (Sum.inr 1054, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

theorem sourceEq1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1326 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1326 + difference 0 5) (sourceB1326 + difference 5 0) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1326 + difference 0 5) (sourceB1326 + difference 5 0) sourceC1326) = raw21094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21094; decide +kernel
    rw [ha]
    exact (canonical21094 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1326 + difference 1 5) (sourceB1326 + difference 5 1) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1326 + difference 1 5) (sourceB1326 + difference 5 1) sourceC1326) = raw21096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21096; decide +kernel
    rw [ha]
    exact (canonical21096 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1326 + difference 2 5) (sourceB1326 + difference 5 2) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA1326 + difference 2 5) (sourceB1326 + difference 5 2) sourceC1326) = raw21097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21097; decide +kernel
    rw [ha]
    exact (canonical21097 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1326 + difference 3 5) (sourceB1326 + difference 5 3) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA1326 + difference 3 5) (sourceB1326 + difference 5 3) sourceC1326) = raw21098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21098; decide +kernel
    rw [ha]
    exact (canonical21098 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1326 + difference 4 5) (sourceB1326 + difference 5 4) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 993) := by
    have ha : (tripleCharges (sourceA1326 + difference 4 5) (sourceB1326 + difference 5 4) sourceC1326) = raw21099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21099; decide +kernel
    rw [ha]
    exact (canonical21099 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1326 + difference 5 5) (sourceB1326 + difference 5 5) sourceC1326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 991) := by
    have ha : (tripleCharges (sourceA1326 + difference 5 5) (sourceB1326 + difference 5 5) sourceC1326) = raw21089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1326 sourceB1326 sourceC1326 difference raw21089; decide +kernel
    rw [ha]
    exact (canonical21089 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1326 + sourceB1326) sourceC1326) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1326 + sourceB1326) sourceC1326) = raw21095 := by
      apply Matrix.ext; unfold doubleCharges sourceA1326 sourceB1326 sourceC1326 raw21095; decide +kernel
    rw [ha]
    exact (canonical21095 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1326 sourceB1326 sourceC1326
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1326, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1327 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1327 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC1327 : Charge := ![3, -2, 0, 1, 0, -2]
def sourceForm1327 : Integer.Sparse Master := [(Sum.inr 989, 1), (Sum.inr 1924, 1), (Sum.inr 1991, 1), (Sum.inr 2119, 1), (Sum.inr 2215, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

theorem sourceEq1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1327 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 0) (sourceB1327 + difference 0 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 0) (sourceB1327 + difference 0 0) sourceC1327) = raw21100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21100; decide +kernel
    rw [ha]
    exact (canonical21100 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 1) (sourceB1327 + difference 1 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2119) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 1) (sourceB1327 + difference 1 0) sourceC1327) = raw21101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21101; decide +kernel
    rw [ha]
    exact (canonical21101 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 2) (sourceB1327 + difference 2 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1991) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 2) (sourceB1327 + difference 2 0) sourceC1327) = raw21102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21102; decide +kernel
    rw [ha]
    exact (canonical21102 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 3) (sourceB1327 + difference 3 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 3) (sourceB1327 + difference 3 0) sourceC1327) = raw21103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21103; decide +kernel
    rw [ha]
    exact (canonical21103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 4) (sourceB1327 + difference 4 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 4) (sourceB1327 + difference 4 0) sourceC1327) = raw21104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21104; decide +kernel
    rw [ha]
    exact (canonical21104 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1327 + difference 0 5) (sourceB1327 + difference 5 0) sourceC1327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1327 + difference 0 5) (sourceB1327 + difference 5 0) sourceC1327) = raw21105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1327 sourceB1327 sourceC1327 difference raw21105; decide +kernel
    rw [ha]
    exact (canonical21105 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1327 + sourceB1327) sourceC1327) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1327 + sourceB1327) sourceC1327) = raw21106 := by
      apply Matrix.ext; unfold doubleCharges sourceA1327 sourceB1327 sourceC1327 raw21106; decide +kernel
    rw [ha]
    exact (canonical21106 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1327 sourceB1327 sourceC1327
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1327, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1328 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1328 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC1328 : Charge := ![3, -2, 0, 1, 0, -2]
def sourceForm1328 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 989, 1), (Sum.inr 992, 1), (Sum.inr 1000, 1), (Sum.inr 1053, 1), (Sum.inr 2215, 1), (Sum.inr 4082, -1)]

theorem sourceEq1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1328 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1328 + difference 0 5) (sourceB1328 + difference 5 0) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1328 + difference 0 5) (sourceB1328 + difference 5 0) sourceC1328) = raw21105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21105; decide +kernel
    rw [ha]
    exact (canonical21105 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1328 + difference 1 5) (sourceB1328 + difference 5 1) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1328 + difference 1 5) (sourceB1328 + difference 5 1) sourceC1328) = raw21107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21107; decide +kernel
    rw [ha]
    exact (canonical21107 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1328 + difference 2 5) (sourceB1328 + difference 5 2) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 987) := by
    have ha : (tripleCharges (sourceA1328 + difference 2 5) (sourceB1328 + difference 5 2) sourceC1328) = raw21108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21108; decide +kernel
    rw [ha]
    exact (canonical21108 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1328 + difference 3 5) (sourceB1328 + difference 5 3) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1053) := by
    have ha : (tripleCharges (sourceA1328 + difference 3 5) (sourceB1328 + difference 5 3) sourceC1328) = raw21109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21109; decide +kernel
    rw [ha]
    exact (canonical21109 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1328 + difference 4 5) (sourceB1328 + difference 5 4) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 992) := by
    have ha : (tripleCharges (sourceA1328 + difference 4 5) (sourceB1328 + difference 5 4) sourceC1328) = raw21110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21110; decide +kernel
    rw [ha]
    exact (canonical21110 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1328 + difference 5 5) (sourceB1328 + difference 5 5) sourceC1328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1328 + difference 5 5) (sourceB1328 + difference 5 5) sourceC1328) = raw21100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1328 sourceB1328 sourceC1328 difference raw21100; decide +kernel
    rw [ha]
    exact (canonical21100 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1328 + sourceB1328) sourceC1328) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1328 + sourceB1328) sourceC1328) = raw21106 := by
      apply Matrix.ext; unfold doubleCharges sourceA1328 sourceB1328 sourceC1328 raw21106; decide +kernel
    rw [ha]
    exact (canonical21106 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1328 sourceB1328 sourceC1328
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1328, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1329 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1329 : Charge := ![1, 1, 1, 0, -2, -1]
def sourceC1329 : Charge := ![3, -1, -1, 0, 1, -2]
def sourceForm1329 : Integer.Sparse Master := [(Sum.inr 1019, 1), (Sum.inr 2008, 1), (Sum.inr 2087, 2), (Sum.inr 2193, 1), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

theorem sourceEq1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1329 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 0) (sourceB1329 + difference 0 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1019) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 0) (sourceB1329 + difference 0 0) sourceC1329) = raw21111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21111; decide +kernel
    rw [ha]
    exact (canonical21111 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 1) (sourceB1329 + difference 1 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2087) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 1) (sourceB1329 + difference 1 0) sourceC1329) = raw21112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21112; decide +kernel
    rw [ha]
    exact (canonical21112 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 2) (sourceB1329 + difference 2 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2087) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 2) (sourceB1329 + difference 2 0) sourceC1329) = raw21113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21113; decide +kernel
    rw [ha]
    exact (canonical21113 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 3) (sourceB1329 + difference 3 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2008) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 3) (sourceB1329 + difference 3 0) sourceC1329) = raw21114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21114; decide +kernel
    rw [ha]
    exact (canonical21114 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 4) (sourceB1329 + difference 4 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 4) (sourceB1329 + difference 4 0) sourceC1329) = raw21115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21115; decide +kernel
    rw [ha]
    exact (canonical21115 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1329 + difference 0 5) (sourceB1329 + difference 5 0) sourceC1329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1329 + difference 0 5) (sourceB1329 + difference 5 0) sourceC1329) = raw21116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1329 sourceB1329 sourceC1329 difference raw21116; decide +kernel
    rw [ha]
    exact (canonical21116 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1329 + sourceB1329) sourceC1329) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1329 + sourceB1329) sourceC1329) = raw21117 := by
      apply Matrix.ext; unfold doubleCharges sourceA1329 sourceB1329 sourceC1329 raw21117; decide +kernel
    rw [ha]
    exact (canonical21117 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1329 sourceB1329 sourceC1329
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1329, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1330 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1330 : Charge := ![1, 1, 1, 0, -2, -1]
def sourceC1330 : Charge := ![3, -1, -1, 0, 1, -2]
def sourceForm1330 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 1019, 1), (Sum.inr 1025, 1), (Sum.inr 1035, 2), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

theorem sourceEq1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1330 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1330 + difference 0 5) (sourceB1330 + difference 5 0) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1330 + difference 0 5) (sourceB1330 + difference 5 0) sourceC1330) = raw21116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21116; decide +kernel
    rw [ha]
    exact (canonical21116 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1330 + difference 1 5) (sourceB1330 + difference 5 1) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1330 + difference 1 5) (sourceB1330 + difference 5 1) sourceC1330) = raw21118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21118; decide +kernel
    rw [ha]
    exact (canonical21118 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1330 + difference 2 5) (sourceB1330 + difference 5 2) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1330 + difference 2 5) (sourceB1330 + difference 5 2) sourceC1330) = raw21119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21119; decide +kernel
    rw [ha]
    exact (canonical21119 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1330 + difference 3 5) (sourceB1330 + difference 5 3) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1017) := by
    have ha : (tripleCharges (sourceA1330 + difference 3 5) (sourceB1330 + difference 5 3) sourceC1330) = raw21120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21120; decide +kernel
    rw [ha]
    exact (canonical21120 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1330 + difference 4 5) (sourceB1330 + difference 5 4) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1025) := by
    have ha : (tripleCharges (sourceA1330 + difference 4 5) (sourceB1330 + difference 5 4) sourceC1330) = raw21121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21121; decide +kernel
    rw [ha]
    exact (canonical21121 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1330 + difference 5 5) (sourceB1330 + difference 5 5) sourceC1330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1019) := by
    have ha : (tripleCharges (sourceA1330 + difference 5 5) (sourceB1330 + difference 5 5) sourceC1330) = raw21111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1330 sourceB1330 sourceC1330 difference raw21111; decide +kernel
    rw [ha]
    exact (canonical21111 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1330 + sourceB1330) sourceC1330) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1330 + sourceB1330) sourceC1330) = raw21117 := by
      apply Matrix.ext; unfold doubleCharges sourceA1330 sourceB1330 sourceC1330 raw21117; decide +kernel
    rw [ha]
    exact (canonical21117 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1330 sourceB1330 sourceC1330
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1330, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1331 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1331 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1331 : Charge := ![3, -1, -1, 1, -1, -1]
def sourceForm1331 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 1898, 1), (Sum.inr 2071, 2), (Sum.inr 2187, 1), (Sum.inr 2191, 1), (Sum.inr 4079, -1)]

theorem sourceEq1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1331 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 0) (sourceB1331 + difference 0 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 972) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 0) (sourceB1331 + difference 0 0) sourceC1331) = raw21122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21122; decide +kernel
    rw [ha]
    exact (canonical21122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 1) (sourceB1331 + difference 1 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 1) (sourceB1331 + difference 1 0) sourceC1331) = raw21123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21123; decide +kernel
    rw [ha]
    exact (canonical21123 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 2) (sourceB1331 + difference 2 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 2) (sourceB1331 + difference 2 0) sourceC1331) = raw21124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21124; decide +kernel
    rw [ha]
    exact (canonical21124 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 3) (sourceB1331 + difference 3 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 3) (sourceB1331 + difference 3 0) sourceC1331) = raw21125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21125; decide +kernel
    rw [ha]
    exact (canonical21125 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 4) (sourceB1331 + difference 4 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 4) (sourceB1331 + difference 4 0) sourceC1331) = raw21126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21126; decide +kernel
    rw [ha]
    exact (canonical21126 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1331 + difference 0 5) (sourceB1331 + difference 5 0) sourceC1331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1331 + difference 0 5) (sourceB1331 + difference 5 0) sourceC1331) = raw21127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1331 sourceB1331 sourceC1331 difference raw21127; decide +kernel
    rw [ha]
    exact (canonical21127 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1331 + sourceB1331) sourceC1331) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1331 + sourceB1331) sourceC1331) = raw21128 := by
      apply Matrix.ext; unfold doubleCharges sourceA1331 sourceB1331 sourceC1331 raw21128; decide +kernel
    rw [ha]
    exact (canonical21128 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1331 sourceB1331 sourceC1331
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1331, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1332 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1332 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1332 : Charge := ![3, -1, -1, 1, -1, -1]
def sourceForm1332 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 974, 1), (Sum.inr 980, 2), (Sum.inr 1018, 1), (Sum.inr 2191, 1), (Sum.inr 4079, -1)]

theorem sourceEq1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1332 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1332 + difference 0 5) (sourceB1332 + difference 5 0) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1332 + difference 0 5) (sourceB1332 + difference 5 0) sourceC1332) = raw21127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21127; decide +kernel
    rw [ha]
    exact (canonical21127 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1332 + difference 1 5) (sourceB1332 + difference 5 1) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1332 + difference 1 5) (sourceB1332 + difference 5 1) sourceC1332) = raw21129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21129; decide +kernel
    rw [ha]
    exact (canonical21129 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1332 + difference 2 5) (sourceB1332 + difference 5 2) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1332 + difference 2 5) (sourceB1332 + difference 5 2) sourceC1332) = raw21130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21130; decide +kernel
    rw [ha]
    exact (canonical21130 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1332 + difference 3 5) (sourceB1332 + difference 5 3) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA1332 + difference 3 5) (sourceB1332 + difference 5 3) sourceC1332) = raw21131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21131; decide +kernel
    rw [ha]
    exact (canonical21131 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1332 + difference 4 5) (sourceB1332 + difference 5 4) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 974) := by
    have ha : (tripleCharges (sourceA1332 + difference 4 5) (sourceB1332 + difference 5 4) sourceC1332) = raw21132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21132; decide +kernel
    rw [ha]
    exact (canonical21132 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1332 + difference 5 5) (sourceB1332 + difference 5 5) sourceC1332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 972) := by
    have ha : (tripleCharges (sourceA1332 + difference 5 5) (sourceB1332 + difference 5 5) sourceC1332) = raw21122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1332 sourceB1332 sourceC1332 difference raw21122; decide +kernel
    rw [ha]
    exact (canonical21122 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1332 + sourceB1332) sourceC1332) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1332 + sourceB1332) sourceC1332) = raw21128 := by
      apply Matrix.ext; unfold doubleCharges sourceA1332 sourceB1332 sourceC1332 raw21128; decide +kernel
    rw [ha]
    exact (canonical21128 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1332 sourceB1332 sourceC1332
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1332, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1333 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1333 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1333 : Charge := ![3, -1, -1, 1, 0, -2]
def sourceForm1333 : Integer.Sparse Master := [(Sum.inr 971, 1), (Sum.inr 1897, 1), (Sum.inr 2070, 2), (Sum.inr 2190, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

theorem sourceEq1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1333 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 0) (sourceB1333 + difference 0 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 971) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 0) (sourceB1333 + difference 0 0) sourceC1333) = raw21133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21133; decide +kernel
    rw [ha]
    exact (canonical21133 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 1) (sourceB1333 + difference 1 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2070) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 1) (sourceB1333 + difference 1 0) sourceC1333) = raw21134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21134; decide +kernel
    rw [ha]
    exact (canonical21134 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 2) (sourceB1333 + difference 2 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2070) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 2) (sourceB1333 + difference 2 0) sourceC1333) = raw21135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21135; decide +kernel
    rw [ha]
    exact (canonical21135 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 3) (sourceB1333 + difference 3 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 3) (sourceB1333 + difference 3 0) sourceC1333) = raw21136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21136; decide +kernel
    rw [ha]
    exact (canonical21136 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 4) (sourceB1333 + difference 4 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 4) (sourceB1333 + difference 4 0) sourceC1333) = raw21137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21137; decide +kernel
    rw [ha]
    exact (canonical21137 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1333 + difference 0 5) (sourceB1333 + difference 5 0) sourceC1333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1333 + difference 0 5) (sourceB1333 + difference 5 0) sourceC1333) = raw21138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1333 sourceB1333 sourceC1333 difference raw21138; decide +kernel
    rw [ha]
    exact (canonical21138 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1333 + sourceB1333) sourceC1333) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1333 + sourceB1333) sourceC1333) = raw21139 := by
      apply Matrix.ext; unfold doubleCharges sourceA1333 sourceB1333 sourceC1333 raw21139; decide +kernel
    rw [ha]
    exact (canonical21139 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1333 sourceB1333 sourceC1333
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1333, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1334 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1334 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1334 : Charge := ![3, -1, -1, 1, 0, -2]
def sourceForm1334 : Integer.Sparse Master := [(Sum.inr 971, 1), (Sum.inr 973, 1), (Sum.inr 977, 2), (Sum.inr 1017, 1), (Sum.inr 2190, 1), (Sum.inr 4080, -1)]

theorem sourceEq1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1334 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1334 + difference 0 5) (sourceB1334 + difference 5 0) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1334 + difference 0 5) (sourceB1334 + difference 5 0) sourceC1334) = raw21138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21138; decide +kernel
    rw [ha]
    exact (canonical21138 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1334 + difference 1 5) (sourceB1334 + difference 5 1) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1334 + difference 1 5) (sourceB1334 + difference 5 1) sourceC1334) = raw21140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21140; decide +kernel
    rw [ha]
    exact (canonical21140 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1334 + difference 2 5) (sourceB1334 + difference 5 2) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1334 + difference 2 5) (sourceB1334 + difference 5 2) sourceC1334) = raw21141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21141; decide +kernel
    rw [ha]
    exact (canonical21141 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1334 + difference 3 5) (sourceB1334 + difference 5 3) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1017) := by
    have ha : (tripleCharges (sourceA1334 + difference 3 5) (sourceB1334 + difference 5 3) sourceC1334) = raw21142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21142; decide +kernel
    rw [ha]
    exact (canonical21142 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1334 + difference 4 5) (sourceB1334 + difference 5 4) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 973) := by
    have ha : (tripleCharges (sourceA1334 + difference 4 5) (sourceB1334 + difference 5 4) sourceC1334) = raw21143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21143; decide +kernel
    rw [ha]
    exact (canonical21143 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1334 + difference 5 5) (sourceB1334 + difference 5 5) sourceC1334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 971) := by
    have ha : (tripleCharges (sourceA1334 + difference 5 5) (sourceB1334 + difference 5 5) sourceC1334) = raw21133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1334 sourceB1334 sourceC1334 difference raw21133; decide +kernel
    rw [ha]
    exact (canonical21133 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1334 + sourceB1334) sourceC1334) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1334 + sourceB1334) sourceC1334) = raw21139 := by
      apply Matrix.ext; unfold doubleCharges sourceA1334 sourceB1334 sourceC1334 raw21139; decide +kernel
    rw [ha]
    exact (canonical21139 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1334 sourceB1334 sourceC1334
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1334, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1335 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1335 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1335 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1335 : Integer.Sparse Master := [(Sum.inr 4153, 2), (Sum.inr 4159, 1), (Sum.inr 4161, 1), (Sum.inr 4183, 1), (Sum.inr 4327, 2), (Sum.inr 4333, 2), (Sum.inr 4335, 2), (Sum.inr 4352, 2), (Sum.inr 4358, 1), (Sum.inr 4367, 2), (Sum.inr 4374, 1), (Sum.inr 4440, 2), (Sum.inr 4445, 1), (Sum.inr 4458, 2), (Sum.inr 4463, 1), (Sum.inr 4467, 1), (Sum.inr 4502, 1), (Sum.inr 4807, 2), (Sum.inr 4871, 1), (Sum.inr 4890, 1), (Sum.inr 4895, 1)]

theorem sourceEq1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1335 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 1) (sourceB1335 + difference 1 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 1) (sourceB1335 + difference 1 0) sourceC1335) = raw11424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11424; decide +kernel
    rw [ha]
    exact (canonical11424 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 2) (sourceB1335 + difference 2 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 2) (sourceB1335 + difference 2 0) sourceC1335) = raw11425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11425; decide +kernel
    rw [ha]
    exact (canonical11425 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 3) (sourceB1335 + difference 3 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 3) (sourceB1335 + difference 3 0) sourceC1335) = raw11426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11426; decide +kernel
    rw [ha]
    exact (canonical11426 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 4) (sourceB1335 + difference 4 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 4) (sourceB1335 + difference 4 0) sourceC1335) = raw11427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11427; decide +kernel
    rw [ha]
    exact (canonical11427 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1335 + difference 0 5) (sourceB1335 + difference 5 0) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1335 + difference 0 5) (sourceB1335 + difference 5 0) sourceC1335) = raw21144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21144; decide +kernel
    rw [ha]
    exact (canonical21144 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 0) (sourceB1335 + difference 0 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4183) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 0) (sourceB1335 + difference 0 1) sourceC1335) = raw21145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21145; decide +kernel
    rw [ha]
    exact (canonical21145 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 2) (sourceB1335 + difference 2 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 2) (sourceB1335 + difference 2 1) sourceC1335) = raw21146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21146; decide +kernel
    rw [ha]
    exact (canonical21146 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 3) (sourceB1335 + difference 3 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 3) (sourceB1335 + difference 3 1) sourceC1335) = raw21147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21147; decide +kernel
    rw [ha]
    exact (canonical21147 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 4) (sourceB1335 + difference 4 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 4) (sourceB1335 + difference 4 1) sourceC1335) = raw21148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21148; decide +kernel
    rw [ha]
    exact (canonical21148 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1335 + difference 1 5) (sourceB1335 + difference 5 1) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1335 + difference 1 5) (sourceB1335 + difference 5 1) sourceC1335) = raw11403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11403; decide +kernel
    rw [ha]
    exact (canonical11403 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 0) (sourceB1335 + difference 0 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 0) (sourceB1335 + difference 0 2) sourceC1335) = raw21149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21149; decide +kernel
    rw [ha]
    exact (canonical21149 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 1) (sourceB1335 + difference 1 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 1) (sourceB1335 + difference 1 2) sourceC1335) = raw21150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21150; decide +kernel
    rw [ha]
    exact (canonical21150 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 3) (sourceB1335 + difference 3 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 3) (sourceB1335 + difference 3 2) sourceC1335) = raw21151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21151; decide +kernel
    rw [ha]
    exact (canonical21151 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 4) (sourceB1335 + difference 4 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 4) (sourceB1335 + difference 4 2) sourceC1335) = raw21152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21152; decide +kernel
    rw [ha]
    exact (canonical21152 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1335 + difference 2 5) (sourceB1335 + difference 5 2) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1335 + difference 2 5) (sourceB1335 + difference 5 2) sourceC1335) = raw11408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11408; decide +kernel
    rw [ha]
    exact (canonical11408 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 0) (sourceB1335 + difference 0 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 0) (sourceB1335 + difference 0 3) sourceC1335) = raw21153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21153; decide +kernel
    rw [ha]
    exact (canonical21153 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 1) (sourceB1335 + difference 1 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 1) (sourceB1335 + difference 1 3) sourceC1335) = raw21154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21154; decide +kernel
    rw [ha]
    exact (canonical21154 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 2) (sourceB1335 + difference 2 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 2) (sourceB1335 + difference 2 3) sourceC1335) = raw21155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21155; decide +kernel
    rw [ha]
    exact (canonical21155 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 4) (sourceB1335 + difference 4 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 4) (sourceB1335 + difference 4 3) sourceC1335) = raw21156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21156; decide +kernel
    rw [ha]
    exact (canonical21156 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1335 + difference 3 5) (sourceB1335 + difference 5 3) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1335 + difference 3 5) (sourceB1335 + difference 5 3) sourceC1335) = raw11413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11413; decide +kernel
    rw [ha]
    exact (canonical11413 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 0) (sourceB1335 + difference 0 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 0) (sourceB1335 + difference 0 4) sourceC1335) = raw21157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21157; decide +kernel
    rw [ha]
    exact (canonical21157 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 1) (sourceB1335 + difference 1 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 1) (sourceB1335 + difference 1 4) sourceC1335) = raw21158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21158; decide +kernel
    rw [ha]
    exact (canonical21158 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 2) (sourceB1335 + difference 2 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 2) (sourceB1335 + difference 2 4) sourceC1335) = raw21159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21159; decide +kernel
    rw [ha]
    exact (canonical21159 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 3) (sourceB1335 + difference 3 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 3) (sourceB1335 + difference 3 4) sourceC1335) = raw21160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21160; decide +kernel
    rw [ha]
    exact (canonical21160 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1335 + difference 4 5) (sourceB1335 + difference 5 4) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1335 + difference 4 5) (sourceB1335 + difference 5 4) sourceC1335) = raw11418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw11418; decide +kernel
    rw [ha]
    exact (canonical11418 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 0) (sourceB1335 + difference 0 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 0) (sourceB1335 + difference 0 5) sourceC1335) = raw21161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21161; decide +kernel
    rw [ha]
    exact (canonical21161 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 1) (sourceB1335 + difference 1 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4358) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 1) (sourceB1335 + difference 1 5) sourceC1335) = raw21162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21162; decide +kernel
    rw [ha]
    exact (canonical21162 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 2) (sourceB1335 + difference 2 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4333) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 2) (sourceB1335 + difference 2 5) sourceC1335) = raw21163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21163; decide +kernel
    rw [ha]
    exact (canonical21163 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 3) (sourceB1335 + difference 3 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4333) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 3) (sourceB1335 + difference 3 5) sourceC1335) = raw21164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21164; decide +kernel
    rw [ha]
    exact (canonical21164 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1335 + difference 5 4) (sourceB1335 + difference 4 5) sourceC1335) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4445) := by
    have ha : (tripleCharges (sourceA1335 + difference 5 4) (sourceB1335 + difference 4 5) sourceC1335) = raw21165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1335 sourceB1335 sourceC1335 difference raw21165; decide +kernel
    rw [ha]
    exact (canonical21165 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1335 sourceB1335 sourceC1335
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1335, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1336 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1336 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1336 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1336 : Integer.Sparse Master := [(Sum.inr 626, 2), (Sum.inr 628, 1), (Sum.inr 635, 1), (Sum.inr 645, 1), (Sum.inr 911, 2), (Sum.inr 936, 1), (Sum.inr 1027, 1), (Sum.inr 1317, 2), (Sum.inr 1324, 1), (Sum.inr 1327, 2), (Sum.inr 1333, 2), (Sum.inr 1340, 2), (Sum.inr 1388, 2), (Sum.inr 1411, 2), (Sum.inr 1413, 1), (Sum.inr 1420, 1), (Sum.inr 1447, 1), (Sum.inr 2574, 2), (Sum.inr 2602, 1), (Sum.inr 2755, 1), (Sum.inr 3229, 1)]

theorem sourceEq1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1336 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1336 + difference 0 1) (sourceB1336 + difference 1 0) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2602) := by
    have ha : (tripleCharges (sourceA1336 + difference 0 1) (sourceB1336 + difference 1 0) sourceC1336) = raw21166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21166; decide +kernel
    rw [ha]
    exact (canonical21166 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1336 + difference 0 2) (sourceB1336 + difference 2 0) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA1336 + difference 0 2) (sourceB1336 + difference 2 0) sourceC1336) = raw21167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21167; decide +kernel
    rw [ha]
    exact (canonical21167 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1336 + difference 0 3) (sourceB1336 + difference 3 0) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA1336 + difference 0 3) (sourceB1336 + difference 3 0) sourceC1336) = raw21168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21168; decide +kernel
    rw [ha]
    exact (canonical21168 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1336 + difference 0 4) (sourceB1336 + difference 4 0) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA1336 + difference 0 4) (sourceB1336 + difference 4 0) sourceC1336) = raw21169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21169; decide +kernel
    rw [ha]
    exact (canonical21169 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1336 + difference 0 5) (sourceB1336 + difference 5 0) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA1336 + difference 0 5) (sourceB1336 + difference 5 0) sourceC1336) = raw21170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21170; decide +kernel
    rw [ha]
    exact (canonical21170 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1336 + difference 1 0) (sourceB1336 + difference 0 1) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 645) := by
    have ha : (tripleCharges (sourceA1336 + difference 1 0) (sourceB1336 + difference 0 1) sourceC1336) = raw21171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21171; decide +kernel
    rw [ha]
    exact (canonical21171 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1336 + difference 1 2) (sourceB1336 + difference 2 1) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1340) := by
    have ha : (tripleCharges (sourceA1336 + difference 1 2) (sourceB1336 + difference 2 1) sourceC1336) = raw21172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21172; decide +kernel
    rw [ha]
    exact (canonical21172 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1336 + difference 1 3) (sourceB1336 + difference 3 1) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1340) := by
    have ha : (tripleCharges (sourceA1336 + difference 1 3) (sourceB1336 + difference 3 1) sourceC1336) = raw21173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21173; decide +kernel
    rw [ha]
    exact (canonical21173 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1336 + difference 1 4) (sourceB1336 + difference 4 1) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1336 + difference 1 4) (sourceB1336 + difference 4 1) sourceC1336) = raw21174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21174; decide +kernel
    rw [ha]
    exact (canonical21174 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1336 + difference 1 5) (sourceB1336 + difference 5 1) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1447) := by
    have ha : (tripleCharges (sourceA1336 + difference 1 5) (sourceB1336 + difference 5 1) sourceC1336) = raw21175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21175; decide +kernel
    rw [ha]
    exact (canonical21175 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1336 + difference 2 0) (sourceB1336 + difference 0 2) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1336 + difference 2 0) (sourceB1336 + difference 0 2) sourceC1336) = raw21176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21176; decide +kernel
    rw [ha]
    exact (canonical21176 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1336 + difference 2 1) (sourceB1336 + difference 1 2) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1336 + difference 2 1) (sourceB1336 + difference 1 2) sourceC1336) = raw21177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21177; decide +kernel
    rw [ha]
    exact (canonical21177 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1336 + difference 2 3) (sourceB1336 + difference 3 2) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1336 + difference 2 3) (sourceB1336 + difference 3 2) sourceC1336) = raw21178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21178; decide +kernel
    rw [ha]
    exact (canonical21178 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1336 + difference 2 4) (sourceB1336 + difference 4 2) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1336 + difference 2 4) (sourceB1336 + difference 4 2) sourceC1336) = raw21179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21179; decide +kernel
    rw [ha]
    exact (canonical21179 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1336 + difference 2 5) (sourceB1336 + difference 5 2) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1336 + difference 2 5) (sourceB1336 + difference 5 2) sourceC1336) = raw21180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21180; decide +kernel
    rw [ha]
    exact (canonical21180 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1336 + difference 3 0) (sourceB1336 + difference 0 3) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1336 + difference 3 0) (sourceB1336 + difference 0 3) sourceC1336) = raw21181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21181; decide +kernel
    rw [ha]
    exact (canonical21181 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1336 + difference 3 1) (sourceB1336 + difference 1 3) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1336 + difference 3 1) (sourceB1336 + difference 1 3) sourceC1336) = raw21182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21182; decide +kernel
    rw [ha]
    exact (canonical21182 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1336 + difference 3 2) (sourceB1336 + difference 2 3) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1336 + difference 3 2) (sourceB1336 + difference 2 3) sourceC1336) = raw21183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21183; decide +kernel
    rw [ha]
    exact (canonical21183 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1336 + difference 3 4) (sourceB1336 + difference 4 3) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1336 + difference 3 4) (sourceB1336 + difference 4 3) sourceC1336) = raw21184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21184; decide +kernel
    rw [ha]
    exact (canonical21184 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1336 + difference 3 5) (sourceB1336 + difference 5 3) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1336 + difference 3 5) (sourceB1336 + difference 5 3) sourceC1336) = raw21185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21185; decide +kernel
    rw [ha]
    exact (canonical21185 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1336 + difference 4 0) (sourceB1336 + difference 0 4) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 635) := by
    have ha : (tripleCharges (sourceA1336 + difference 4 0) (sourceB1336 + difference 0 4) sourceC1336) = raw21186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21186; decide +kernel
    rw [ha]
    exact (canonical21186 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1336 + difference 4 1) (sourceB1336 + difference 1 4) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1324) := by
    have ha : (tripleCharges (sourceA1336 + difference 4 1) (sourceB1336 + difference 1 4) sourceC1336) = raw21187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21187; decide +kernel
    rw [ha]
    exact (canonical21187 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1336 + difference 4 2) (sourceB1336 + difference 2 4) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1336 + difference 4 2) (sourceB1336 + difference 2 4) sourceC1336) = raw21188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21188; decide +kernel
    rw [ha]
    exact (canonical21188 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1336 + difference 4 3) (sourceB1336 + difference 3 4) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1336 + difference 4 3) (sourceB1336 + difference 3 4) sourceC1336) = raw21189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21189; decide +kernel
    rw [ha]
    exact (canonical21189 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1336 + difference 4 5) (sourceB1336 + difference 5 4) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA1336 + difference 4 5) (sourceB1336 + difference 5 4) sourceC1336) = raw21190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21190; decide +kernel
    rw [ha]
    exact (canonical21190 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1336 + difference 5 0) (sourceB1336 + difference 0 5) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1336 + difference 5 0) (sourceB1336 + difference 0 5) sourceC1336) = raw21191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21191; decide +kernel
    rw [ha]
    exact (canonical21191 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1336 + difference 5 1) (sourceB1336 + difference 1 5) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1336 + difference 5 1) (sourceB1336 + difference 1 5) sourceC1336) = raw21192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21192; decide +kernel
    rw [ha]
    exact (canonical21192 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1336 + difference 5 2) (sourceB1336 + difference 2 5) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1336 + difference 5 2) (sourceB1336 + difference 2 5) sourceC1336) = raw21193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21193; decide +kernel
    rw [ha]
    exact (canonical21193 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1336 + difference 5 3) (sourceB1336 + difference 3 5) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1336 + difference 5 3) (sourceB1336 + difference 3 5) sourceC1336) = raw21194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21194; decide +kernel
    rw [ha]
    exact (canonical21194 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1336 + difference 5 4) (sourceB1336 + difference 4 5) sourceC1336) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA1336 + difference 5 4) (sourceB1336 + difference 4 5) sourceC1336) = raw21195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1336 sourceB1336 sourceC1336 difference raw21195; decide +kernel
    rw [ha]
    exact (canonical21195 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1336 sourceB1336 sourceC1336
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1336, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1337 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1337 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1337 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1337 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1532, 1), (Sum.inr 1533, 1), (Sum.inr 1535, 1), (Sum.inr 1670, 2), (Sum.inr 1688, 2), (Sum.inr 1689, 2), (Sum.inr 1690, 2), (Sum.inr 1695, 1), (Sum.inr 1720, 2), (Sum.inr 1723, 2), (Sum.inr 1724, 2), (Sum.inr 1748, 1), (Sum.inr 1749, 1), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 1753, 1), (Sum.inr 2224, 2), (Sum.inr 2287, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 1)]

theorem sourceEq1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1337 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 1) (sourceB1337 + difference 1 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 1) (sourceB1337 + difference 1 0) sourceC1337) = raw11454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11454; decide +kernel
    rw [ha]
    exact (canonical11454 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 2) (sourceB1337 + difference 2 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 2) (sourceB1337 + difference 2 0) sourceC1337) = raw11455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11455; decide +kernel
    rw [ha]
    exact (canonical11455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 3) (sourceB1337 + difference 3 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 3) (sourceB1337 + difference 3 0) sourceC1337) = raw11456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11456; decide +kernel
    rw [ha]
    exact (canonical11456 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 4) (sourceB1337 + difference 4 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 4) (sourceB1337 + difference 4 0) sourceC1337) = raw11457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11457; decide +kernel
    rw [ha]
    exact (canonical11457 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1337 + difference 0 5) (sourceB1337 + difference 5 0) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1337 + difference 0 5) (sourceB1337 + difference 5 0) sourceC1337) = raw21196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21196; decide +kernel
    rw [ha]
    exact (canonical21196 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 0) (sourceB1337 + difference 0 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 0) (sourceB1337 + difference 0 1) sourceC1337) = raw21197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21197; decide +kernel
    rw [ha]
    exact (canonical21197 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 2) (sourceB1337 + difference 2 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 2) (sourceB1337 + difference 2 1) sourceC1337) = raw21198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21198; decide +kernel
    rw [ha]
    exact (canonical21198 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 3) (sourceB1337 + difference 3 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 3) (sourceB1337 + difference 3 1) sourceC1337) = raw21199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21199; decide +kernel
    rw [ha]
    exact (canonical21199 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 4) (sourceB1337 + difference 4 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 4) (sourceB1337 + difference 4 1) sourceC1337) = raw21200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21200; decide +kernel
    rw [ha]
    exact (canonical21200 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1337 + difference 1 5) (sourceB1337 + difference 5 1) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1337 + difference 1 5) (sourceB1337 + difference 5 1) sourceC1337) = raw11433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11433; decide +kernel
    rw [ha]
    exact (canonical11433 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 0) (sourceB1337 + difference 0 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 0) (sourceB1337 + difference 0 2) sourceC1337) = raw21201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21201; decide +kernel
    rw [ha]
    exact (canonical21201 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 1) (sourceB1337 + difference 1 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 1) (sourceB1337 + difference 1 2) sourceC1337) = raw21202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21202; decide +kernel
    rw [ha]
    exact (canonical21202 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 3) (sourceB1337 + difference 3 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 3) (sourceB1337 + difference 3 2) sourceC1337) = raw21203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21203; decide +kernel
    rw [ha]
    exact (canonical21203 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 4) (sourceB1337 + difference 4 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 4) (sourceB1337 + difference 4 2) sourceC1337) = raw21204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21204; decide +kernel
    rw [ha]
    exact (canonical21204 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1337 + difference 2 5) (sourceB1337 + difference 5 2) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1337 + difference 2 5) (sourceB1337 + difference 5 2) sourceC1337) = raw11438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11438; decide +kernel
    rw [ha]
    exact (canonical11438 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 0) (sourceB1337 + difference 0 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 0) (sourceB1337 + difference 0 3) sourceC1337) = raw21205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21205; decide +kernel
    rw [ha]
    exact (canonical21205 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 1) (sourceB1337 + difference 1 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 1) (sourceB1337 + difference 1 3) sourceC1337) = raw21206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21206; decide +kernel
    rw [ha]
    exact (canonical21206 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 2) (sourceB1337 + difference 2 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 2) (sourceB1337 + difference 2 3) sourceC1337) = raw21207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21207; decide +kernel
    rw [ha]
    exact (canonical21207 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 4) (sourceB1337 + difference 4 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 4) (sourceB1337 + difference 4 3) sourceC1337) = raw21208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21208; decide +kernel
    rw [ha]
    exact (canonical21208 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1337 + difference 3 5) (sourceB1337 + difference 5 3) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1337 + difference 3 5) (sourceB1337 + difference 5 3) sourceC1337) = raw11443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11443; decide +kernel
    rw [ha]
    exact (canonical11443 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 0) (sourceB1337 + difference 0 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 0) (sourceB1337 + difference 0 4) sourceC1337) = raw21209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21209; decide +kernel
    rw [ha]
    exact (canonical21209 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 1) (sourceB1337 + difference 1 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 1) (sourceB1337 + difference 1 4) sourceC1337) = raw21210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21210; decide +kernel
    rw [ha]
    exact (canonical21210 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 2) (sourceB1337 + difference 2 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 2) (sourceB1337 + difference 2 4) sourceC1337) = raw21211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21211; decide +kernel
    rw [ha]
    exact (canonical21211 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 3) (sourceB1337 + difference 3 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 3) (sourceB1337 + difference 3 4) sourceC1337) = raw21212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21212; decide +kernel
    rw [ha]
    exact (canonical21212 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1337 + difference 4 5) (sourceB1337 + difference 5 4) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1337 + difference 4 5) (sourceB1337 + difference 5 4) sourceC1337) = raw11448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw11448; decide +kernel
    rw [ha]
    exact (canonical11448 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 0) (sourceB1337 + difference 0 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 0) (sourceB1337 + difference 0 5) sourceC1337) = raw21213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21213; decide +kernel
    rw [ha]
    exact (canonical21213 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 1) (sourceB1337 + difference 1 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 1) (sourceB1337 + difference 1 5) sourceC1337) = raw21214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21214; decide +kernel
    rw [ha]
    exact (canonical21214 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 2) (sourceB1337 + difference 2 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 2) (sourceB1337 + difference 2 5) sourceC1337) = raw21215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21215; decide +kernel
    rw [ha]
    exact (canonical21215 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 3) (sourceB1337 + difference 3 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 3) (sourceB1337 + difference 3 5) sourceC1337) = raw21216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21216; decide +kernel
    rw [ha]
    exact (canonical21216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1337 + difference 5 4) (sourceB1337 + difference 4 5) sourceC1337) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1337 + difference 5 4) (sourceB1337 + difference 4 5) sourceC1337) = raw21217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1337 sourceB1337 sourceC1337 difference raw21217; decide +kernel
    rw [ha]
    exact (canonical21217 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1337 sourceB1337 sourceC1337
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1337, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1338 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1338 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1338 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1338 : Integer.Sparse Master := [(Sum.inr 581, 2), (Sum.inr 587, 1), (Sum.inr 589, 1), (Sum.inr 611, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

theorem sourceEq1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1338 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1338 + difference 0 0) (sourceB1338 + difference 0 0) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1338 + difference 0 0) (sourceB1338 + difference 0 0) sourceC1338) = raw21218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21218; decide +kernel
    rw [ha]
    exact (canonical21218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1338 + difference 1 0) (sourceB1338 + difference 0 1) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 611) := by
    have ha : (tripleCharges (sourceA1338 + difference 1 0) (sourceB1338 + difference 0 1) sourceC1338) = raw21219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21219; decide +kernel
    rw [ha]
    exact (canonical21219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1338 + difference 2 0) (sourceB1338 + difference 0 2) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1338 + difference 2 0) (sourceB1338 + difference 0 2) sourceC1338) = raw21220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21220; decide +kernel
    rw [ha]
    exact (canonical21220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1338 + difference 3 0) (sourceB1338 + difference 0 3) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1338 + difference 3 0) (sourceB1338 + difference 0 3) sourceC1338) = raw21221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21221; decide +kernel
    rw [ha]
    exact (canonical21221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1338 + difference 4 0) (sourceB1338 + difference 0 4) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 589) := by
    have ha : (tripleCharges (sourceA1338 + difference 4 0) (sourceB1338 + difference 0 4) sourceC1338) = raw21222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21222; decide +kernel
    rw [ha]
    exact (canonical21222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1338 + difference 5 0) (sourceB1338 + difference 0 5) sourceC1338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1338 + difference 5 0) (sourceB1338 + difference 0 5) sourceC1338) = raw21223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1338 sourceB1338 sourceC1338 difference raw21223; decide +kernel
    rw [ha]
    exact (canonical21223 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1338 + sourceB1338) sourceC1338) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1338 + sourceB1338) sourceC1338) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1338 sourceB1338 sourceC1338 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1338 sourceB1338 sourceC1338
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1338, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1339 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1339 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1339 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1339 : Integer.Sparse Master := [(Sum.inr 611, 1), (Sum.inr 930, 2), (Sum.inr 1046, 2), (Sum.inr 1086, 1), (Sum.inr 4083, -1)]

theorem sourceEq1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1339 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 0) (sourceB1339 + difference 0 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 611) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 0) (sourceB1339 + difference 0 1) sourceC1339) = raw21219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21219; decide +kernel
    rw [ha]
    exact (canonical21219 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 1) (sourceB1339 + difference 1 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 1) (sourceB1339 + difference 1 1) sourceC1339) = raw21218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21218; decide +kernel
    rw [ha]
    exact (canonical21218 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 2) (sourceB1339 + difference 2 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 2) (sourceB1339 + difference 2 1) sourceC1339) = raw21224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21224; decide +kernel
    rw [ha]
    exact (canonical21224 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 3) (sourceB1339 + difference 3 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 3) (sourceB1339 + difference 3 1) sourceC1339) = raw21225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21225; decide +kernel
    rw [ha]
    exact (canonical21225 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 4) (sourceB1339 + difference 4 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 4) (sourceB1339 + difference 4 1) sourceC1339) = raw21226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21226; decide +kernel
    rw [ha]
    exact (canonical21226 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1339 + difference 1 5) (sourceB1339 + difference 5 1) sourceC1339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1339 + difference 1 5) (sourceB1339 + difference 5 1) sourceC1339) = raw21227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1339 sourceB1339 sourceC1339 difference raw21227; decide +kernel
    rw [ha]
    exact (canonical21227 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1339 + sourceB1339) sourceC1339) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1339 + sourceB1339) sourceC1339) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1339 sourceB1339 sourceC1339 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1339 sourceB1339 sourceC1339
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1339, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1340 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1340 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1340 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1340 : Integer.Sparse Master := [(Sum.inr 945, 2), (Sum.inr 951, 1), (Sum.inr 953, 1), (Sum.inr 1046, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

theorem sourceEq1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1340 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1340 + difference 0 1) (sourceB1340 + difference 1 0) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1340 + difference 0 1) (sourceB1340 + difference 1 0) sourceC1340) = raw11463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw11463; decide +kernel
    rw [ha]
    exact (canonical11463 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1340 + difference 1 1) (sourceB1340 + difference 1 1) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1340 + difference 1 1) (sourceB1340 + difference 1 1) sourceC1340) = raw21218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21218; decide +kernel
    rw [ha]
    exact (canonical21218 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1340 + difference 2 1) (sourceB1340 + difference 1 2) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1340 + difference 2 1) (sourceB1340 + difference 1 2) sourceC1340) = raw21228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21228; decide +kernel
    rw [ha]
    exact (canonical21228 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1340 + difference 3 1) (sourceB1340 + difference 1 3) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1340 + difference 3 1) (sourceB1340 + difference 1 3) sourceC1340) = raw21229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21229; decide +kernel
    rw [ha]
    exact (canonical21229 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1340 + difference 4 1) (sourceB1340 + difference 1 4) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 953) := by
    have ha : (tripleCharges (sourceA1340 + difference 4 1) (sourceB1340 + difference 1 4) sourceC1340) = raw21230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21230; decide +kernel
    rw [ha]
    exact (canonical21230 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1340 + difference 5 1) (sourceB1340 + difference 1 5) sourceC1340) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 951) := by
    have ha : (tripleCharges (sourceA1340 + difference 5 1) (sourceB1340 + difference 1 5) sourceC1340) = raw21231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1340 sourceB1340 sourceC1340 difference raw21231; decide +kernel
    rw [ha]
    exact (canonical21231 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1340 + sourceB1340) sourceC1340) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1340 + sourceB1340) sourceC1340) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1340 sourceB1340 sourceC1340 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1340 sourceB1340 sourceC1340
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1340, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1341 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1341 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1341 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1341 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 911, 1), (Sum.inr 913, 1), (Sum.inr 930, 1), (Sum.inr 1046, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

theorem sourceEq1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1341 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1341 + difference 0 2) (sourceB1341 + difference 2 0) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1341 + difference 0 2) (sourceB1341 + difference 2 0) sourceC1341) = raw21232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21232; decide +kernel
    rw [ha]
    exact (canonical21232 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1341 + difference 1 2) (sourceB1341 + difference 2 1) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1341 + difference 1 2) (sourceB1341 + difference 2 1) sourceC1341) = raw21224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21224; decide +kernel
    rw [ha]
    exact (canonical21224 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1341 + difference 2 2) (sourceB1341 + difference 2 2) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1341 + difference 2 2) (sourceB1341 + difference 2 2) sourceC1341) = raw21218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21218; decide +kernel
    rw [ha]
    exact (canonical21218 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1341 + difference 3 2) (sourceB1341 + difference 2 3) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 905) := by
    have ha : (tripleCharges (sourceA1341 + difference 3 2) (sourceB1341 + difference 2 3) sourceC1341) = raw21233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21233; decide +kernel
    rw [ha]
    exact (canonical21233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1341 + difference 4 2) (sourceB1341 + difference 2 4) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 913) := by
    have ha : (tripleCharges (sourceA1341 + difference 4 2) (sourceB1341 + difference 2 4) sourceC1341) = raw21234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21234; decide +kernel
    rw [ha]
    exact (canonical21234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1341 + difference 5 2) (sourceB1341 + difference 2 5) sourceC1341) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1341 + difference 5 2) (sourceB1341 + difference 2 5) sourceC1341) = raw21235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1341 sourceB1341 sourceC1341 difference raw21235; decide +kernel
    rw [ha]
    exact (canonical21235 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1341 + sourceB1341) sourceC1341) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1341 + sourceB1341) sourceC1341) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1341 sourceB1341 sourceC1341 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1341 sourceB1341 sourceC1341
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1341, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1342 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1342 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1342 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm1342 : Integer.Sparse Master := [(Sum.inr 4105, 2), (Sum.inr 4108, 1), (Sum.inr 4111, 1), (Sum.inr 4128, 1), (Sum.inr 4290, 2), (Sum.inr 4293, 2), (Sum.inr 4296, 2), (Sum.inr 4309, 2), (Sum.inr 4352, 2), (Sum.inr 4356, 1), (Sum.inr 4361, 1), (Sum.inr 4461, 2), (Sum.inr 4463, 2), (Sum.inr 4466, 1), (Sum.inr 4468, 1), (Sum.inr 4503, 1), (Sum.inr 4507, 1), (Sum.inr 5078, 2), (Sum.inr 5174, 1), (Sum.inr 5294, 1), (Sum.inr 5296, 1)]

theorem sourceEq1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1342 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1342 + difference 0 1) (sourceB1342 + difference 1 0) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1342 + difference 0 1) (sourceB1342 + difference 1 0) sourceC1342) = raw17698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw17698; decide +kernel
    rw [ha]
    exact (canonical17698 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1342 + difference 0 2) (sourceB1342 + difference 2 0) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1342 + difference 0 2) (sourceB1342 + difference 2 0) sourceC1342) = raw21236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21236; decide +kernel
    rw [ha]
    exact (canonical21236 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1342 + difference 0 3) (sourceB1342 + difference 3 0) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1342 + difference 0 3) (sourceB1342 + difference 3 0) sourceC1342) = raw21237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21237; decide +kernel
    rw [ha]
    exact (canonical21237 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1342 + difference 0 4) (sourceB1342 + difference 4 0) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1342 + difference 0 4) (sourceB1342 + difference 4 0) sourceC1342) = raw21238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21238; decide +kernel
    rw [ha]
    exact (canonical21238 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1342 + difference 0 5) (sourceB1342 + difference 5 0) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1342 + difference 0 5) (sourceB1342 + difference 5 0) sourceC1342) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1342 + difference 1 0) (sourceB1342 + difference 0 1) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4128) := by
    have ha : (tripleCharges (sourceA1342 + difference 1 0) (sourceB1342 + difference 0 1) sourceC1342) = raw21239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21239; decide +kernel
    rw [ha]
    exact (canonical21239 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1342 + difference 1 2) (sourceB1342 + difference 2 1) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1342 + difference 1 2) (sourceB1342 + difference 2 1) sourceC1342) = raw21240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21240; decide +kernel
    rw [ha]
    exact (canonical21240 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1342 + difference 1 3) (sourceB1342 + difference 3 1) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1342 + difference 1 3) (sourceB1342 + difference 3 1) sourceC1342) = raw21241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21241; decide +kernel
    rw [ha]
    exact (canonical21241 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1342 + difference 1 4) (sourceB1342 + difference 4 1) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1342 + difference 1 4) (sourceB1342 + difference 4 1) sourceC1342) = raw21242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21242; decide +kernel
    rw [ha]
    exact (canonical21242 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1342 + difference 1 5) (sourceB1342 + difference 5 1) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1342 + difference 1 5) (sourceB1342 + difference 5 1) sourceC1342) = raw21243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21243; decide +kernel
    rw [ha]
    exact (canonical21243 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1342 + difference 2 0) (sourceB1342 + difference 0 2) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4105) := by
    have ha : (tripleCharges (sourceA1342 + difference 2 0) (sourceB1342 + difference 0 2) sourceC1342) = raw21244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21244; decide +kernel
    rw [ha]
    exact (canonical21244 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1342 + difference 2 1) (sourceB1342 + difference 1 2) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1342 + difference 2 1) (sourceB1342 + difference 1 2) sourceC1342) = raw21245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21245; decide +kernel
    rw [ha]
    exact (canonical21245 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1342 + difference 2 3) (sourceB1342 + difference 3 2) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4290) := by
    have ha : (tripleCharges (sourceA1342 + difference 2 3) (sourceB1342 + difference 3 2) sourceC1342) = raw21246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21246; decide +kernel
    rw [ha]
    exact (canonical21246 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1342 + difference 2 4) (sourceB1342 + difference 4 2) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1342 + difference 2 4) (sourceB1342 + difference 4 2) sourceC1342) = raw21247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21247; decide +kernel
    rw [ha]
    exact (canonical21247 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1342 + difference 2 5) (sourceB1342 + difference 5 2) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1342 + difference 2 5) (sourceB1342 + difference 5 2) sourceC1342) = raw21248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21248; decide +kernel
    rw [ha]
    exact (canonical21248 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1342 + difference 3 0) (sourceB1342 + difference 0 3) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4105) := by
    have ha : (tripleCharges (sourceA1342 + difference 3 0) (sourceB1342 + difference 0 3) sourceC1342) = raw21249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21249; decide +kernel
    rw [ha]
    exact (canonical21249 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1342 + difference 3 1) (sourceB1342 + difference 1 3) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1342 + difference 3 1) (sourceB1342 + difference 1 3) sourceC1342) = raw21250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21250; decide +kernel
    rw [ha]
    exact (canonical21250 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1342 + difference 3 2) (sourceB1342 + difference 2 3) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4290) := by
    have ha : (tripleCharges (sourceA1342 + difference 3 2) (sourceB1342 + difference 2 3) sourceC1342) = raw21251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21251; decide +kernel
    rw [ha]
    exact (canonical21251 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1342 + difference 3 4) (sourceB1342 + difference 4 3) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1342 + difference 3 4) (sourceB1342 + difference 4 3) sourceC1342) = raw21252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21252; decide +kernel
    rw [ha]
    exact (canonical21252 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1342 + difference 3 5) (sourceB1342 + difference 5 3) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1342 + difference 3 5) (sourceB1342 + difference 5 3) sourceC1342) = raw13591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw13591; decide +kernel
    rw [ha]
    exact (canonical13591 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1342 + difference 4 0) (sourceB1342 + difference 0 4) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4111) := by
    have ha : (tripleCharges (sourceA1342 + difference 4 0) (sourceB1342 + difference 0 4) sourceC1342) = raw21253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21253; decide +kernel
    rw [ha]
    exact (canonical21253 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1342 + difference 4 1) (sourceB1342 + difference 1 4) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1342 + difference 4 1) (sourceB1342 + difference 1 4) sourceC1342) = raw21254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21254; decide +kernel
    rw [ha]
    exact (canonical21254 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1342 + difference 4 2) (sourceB1342 + difference 2 4) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA1342 + difference 4 2) (sourceB1342 + difference 2 4) sourceC1342) = raw21255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21255; decide +kernel
    rw [ha]
    exact (canonical21255 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1342 + difference 4 3) (sourceB1342 + difference 3 4) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA1342 + difference 4 3) (sourceB1342 + difference 3 4) sourceC1342) = raw21256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21256; decide +kernel
    rw [ha]
    exact (canonical21256 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1342 + difference 4 5) (sourceB1342 + difference 5 4) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1342 + difference 4 5) (sourceB1342 + difference 5 4) sourceC1342) = raw21257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21257; decide +kernel
    rw [ha]
    exact (canonical21257 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1342 + difference 5 0) (sourceB1342 + difference 0 5) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4108) := by
    have ha : (tripleCharges (sourceA1342 + difference 5 0) (sourceB1342 + difference 0 5) sourceC1342) = raw21258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21258; decide +kernel
    rw [ha]
    exact (canonical21258 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1342 + difference 5 1) (sourceB1342 + difference 1 5) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1342 + difference 5 1) (sourceB1342 + difference 1 5) sourceC1342) = raw21259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21259; decide +kernel
    rw [ha]
    exact (canonical21259 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1342 + difference 5 2) (sourceB1342 + difference 2 5) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1342 + difference 5 2) (sourceB1342 + difference 2 5) sourceC1342) = raw21260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21260; decide +kernel
    rw [ha]
    exact (canonical21260 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1342 + difference 5 3) (sourceB1342 + difference 3 5) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1342 + difference 5 3) (sourceB1342 + difference 3 5) sourceC1342) = raw21261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21261; decide +kernel
    rw [ha]
    exact (canonical21261 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1342 + difference 5 4) (sourceB1342 + difference 4 5) sourceC1342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1342 + difference 5 4) (sourceB1342 + difference 4 5) sourceC1342) = raw21262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1342 sourceB1342 sourceC1342 difference raw21262; decide +kernel
    rw [ha]
    exact (canonical21262 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1342 sourceB1342 sourceC1342
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1342, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1343 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1343 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1343 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm1343 : Integer.Sparse Master := [(Sum.inr 542, 2), (Sum.inr 545, 1), (Sum.inr 548, 1), (Sum.inr 559, 1), (Sum.inr 868, 2), (Sum.inr 871, 2), (Sum.inr 874, 2), (Sum.inr 887, 2), (Sum.inr 930, 2), (Sum.inr 934, 1), (Sum.inr 939, 1), (Sum.inr 1044, 2), (Sum.inr 1046, 2), (Sum.inr 1049, 1), (Sum.inr 1051, 1), (Sum.inr 1087, 1), (Sum.inr 1091, 1), (Sum.inr 2485, 2), (Sum.inr 2601, 1), (Sum.inr 2768, 1), (Sum.inr 2770, 1)]

theorem sourceEq1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1343 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1343 + difference 0 1) (sourceB1343 + difference 1 0) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1343 + difference 0 1) (sourceB1343 + difference 1 0) sourceC1343) = raw21263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21263; decide +kernel
    rw [ha]
    exact (canonical21263 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1343 + difference 0 2) (sourceB1343 + difference 2 0) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1343 + difference 0 2) (sourceB1343 + difference 2 0) sourceC1343) = raw21264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21264; decide +kernel
    rw [ha]
    exact (canonical21264 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1343 + difference 0 3) (sourceB1343 + difference 3 0) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1343 + difference 0 3) (sourceB1343 + difference 3 0) sourceC1343) = raw21265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21265; decide +kernel
    rw [ha]
    exact (canonical21265 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1343 + difference 0 4) (sourceB1343 + difference 4 0) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA1343 + difference 0 4) (sourceB1343 + difference 4 0) sourceC1343) = raw21266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21266; decide +kernel
    rw [ha]
    exact (canonical21266 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1343 + difference 0 5) (sourceB1343 + difference 5 0) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA1343 + difference 0 5) (sourceB1343 + difference 5 0) sourceC1343) = raw3084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw3084; decide +kernel
    rw [ha]
    exact (canonical3084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1343 + difference 1 0) (sourceB1343 + difference 0 1) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 559) := by
    have ha : (tripleCharges (sourceA1343 + difference 1 0) (sourceB1343 + difference 0 1) sourceC1343) = raw21267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21267; decide +kernel
    rw [ha]
    exact (canonical21267 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1343 + difference 1 2) (sourceB1343 + difference 2 1) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1343 + difference 1 2) (sourceB1343 + difference 2 1) sourceC1343) = raw21268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21268; decide +kernel
    rw [ha]
    exact (canonical21268 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1343 + difference 1 3) (sourceB1343 + difference 3 1) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1343 + difference 1 3) (sourceB1343 + difference 3 1) sourceC1343) = raw21269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21269; decide +kernel
    rw [ha]
    exact (canonical21269 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1343 + difference 1 4) (sourceB1343 + difference 4 1) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1343 + difference 1 4) (sourceB1343 + difference 4 1) sourceC1343) = raw21270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21270; decide +kernel
    rw [ha]
    exact (canonical21270 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1343 + difference 1 5) (sourceB1343 + difference 5 1) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1343 + difference 1 5) (sourceB1343 + difference 5 1) sourceC1343) = raw21271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21271; decide +kernel
    rw [ha]
    exact (canonical21271 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1343 + difference 2 0) (sourceB1343 + difference 0 2) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 542) := by
    have ha : (tripleCharges (sourceA1343 + difference 2 0) (sourceB1343 + difference 0 2) sourceC1343) = raw21272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21272; decide +kernel
    rw [ha]
    exact (canonical21272 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1343 + difference 2 1) (sourceB1343 + difference 1 2) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1343 + difference 2 1) (sourceB1343 + difference 1 2) sourceC1343) = raw21273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21273; decide +kernel
    rw [ha]
    exact (canonical21273 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1343 + difference 2 3) (sourceB1343 + difference 3 2) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 868) := by
    have ha : (tripleCharges (sourceA1343 + difference 2 3) (sourceB1343 + difference 3 2) sourceC1343) = raw21274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21274; decide +kernel
    rw [ha]
    exact (canonical21274 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1343 + difference 2 4) (sourceB1343 + difference 4 2) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1343 + difference 2 4) (sourceB1343 + difference 4 2) sourceC1343) = raw21275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21275; decide +kernel
    rw [ha]
    exact (canonical21275 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1343 + difference 2 5) (sourceB1343 + difference 5 2) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1343 + difference 2 5) (sourceB1343 + difference 5 2) sourceC1343) = raw21276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21276; decide +kernel
    rw [ha]
    exact (canonical21276 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1343 + difference 3 0) (sourceB1343 + difference 0 3) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 542) := by
    have ha : (tripleCharges (sourceA1343 + difference 3 0) (sourceB1343 + difference 0 3) sourceC1343) = raw21277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21277; decide +kernel
    rw [ha]
    exact (canonical21277 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1343 + difference 3 1) (sourceB1343 + difference 1 3) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1343 + difference 3 1) (sourceB1343 + difference 1 3) sourceC1343) = raw21278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21278; decide +kernel
    rw [ha]
    exact (canonical21278 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1343 + difference 3 2) (sourceB1343 + difference 2 3) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 868) := by
    have ha : (tripleCharges (sourceA1343 + difference 3 2) (sourceB1343 + difference 2 3) sourceC1343) = raw21279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21279; decide +kernel
    rw [ha]
    exact (canonical21279 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1343 + difference 3 4) (sourceB1343 + difference 4 3) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1343 + difference 3 4) (sourceB1343 + difference 4 3) sourceC1343) = raw21280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21280; decide +kernel
    rw [ha]
    exact (canonical21280 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1343 + difference 3 5) (sourceB1343 + difference 5 3) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1343 + difference 3 5) (sourceB1343 + difference 5 3) sourceC1343) = raw13613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw13613; decide +kernel
    rw [ha]
    exact (canonical13613 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1343 + difference 4 0) (sourceB1343 + difference 0 4) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 548) := by
    have ha : (tripleCharges (sourceA1343 + difference 4 0) (sourceB1343 + difference 0 4) sourceC1343) = raw21281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21281; decide +kernel
    rw [ha]
    exact (canonical21281 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1343 + difference 4 1) (sourceB1343 + difference 1 4) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 939) := by
    have ha : (tripleCharges (sourceA1343 + difference 4 1) (sourceB1343 + difference 1 4) sourceC1343) = raw21282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21282; decide +kernel
    rw [ha]
    exact (canonical21282 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1343 + difference 4 2) (sourceB1343 + difference 2 4) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 874) := by
    have ha : (tripleCharges (sourceA1343 + difference 4 2) (sourceB1343 + difference 2 4) sourceC1343) = raw21283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21283; decide +kernel
    rw [ha]
    exact (canonical21283 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1343 + difference 4 3) (sourceB1343 + difference 3 4) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 874) := by
    have ha : (tripleCharges (sourceA1343 + difference 4 3) (sourceB1343 + difference 3 4) sourceC1343) = raw21284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21284; decide +kernel
    rw [ha]
    exact (canonical21284 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1343 + difference 4 5) (sourceB1343 + difference 5 4) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1343 + difference 4 5) (sourceB1343 + difference 5 4) sourceC1343) = raw21285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21285; decide +kernel
    rw [ha]
    exact (canonical21285 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1343 + difference 5 0) (sourceB1343 + difference 0 5) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 545) := by
    have ha : (tripleCharges (sourceA1343 + difference 5 0) (sourceB1343 + difference 0 5) sourceC1343) = raw21286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21286; decide +kernel
    rw [ha]
    exact (canonical21286 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1343 + difference 5 1) (sourceB1343 + difference 1 5) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1343 + difference 5 1) (sourceB1343 + difference 1 5) sourceC1343) = raw21287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21287; decide +kernel
    rw [ha]
    exact (canonical21287 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1343 + difference 5 2) (sourceB1343 + difference 2 5) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1343 + difference 5 2) (sourceB1343 + difference 2 5) sourceC1343) = raw21288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21288; decide +kernel
    rw [ha]
    exact (canonical21288 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1343 + difference 5 3) (sourceB1343 + difference 3 5) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1343 + difference 5 3) (sourceB1343 + difference 3 5) sourceC1343) = raw21289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21289; decide +kernel
    rw [ha]
    exact (canonical21289 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1343 + difference 5 4) (sourceB1343 + difference 4 5) sourceC1343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1343 + difference 5 4) (sourceB1343 + difference 4 5) sourceC1343) = raw21290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1343 sourceB1343 sourceC1343 difference raw21290; decide +kernel
    rw [ha]
    exact (canonical21290 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1343 sourceB1343 sourceC1343
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1343, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
