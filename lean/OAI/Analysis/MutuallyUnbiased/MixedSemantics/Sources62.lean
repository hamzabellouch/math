import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical221
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical222

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1984 : Charge := ![1, 1, 0, 2, -1, -3]
def sourceB1984 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1984 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1984 : Integer.Sparse Master := [(Sum.inr 888, 1), (Sum.inr 1779, 1), (Sum.inr 1868, 1), (Sum.inr 1917, 1), (Sum.inr 1944, 1), (Sum.inr 1948, 1), (Sum.inr 4081, -1)]

theorem sourceEq1984 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1984 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1984 + difference 0 0) (sourceB1984 + difference 0 0) sourceC1984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1948) := by
    have ha : (tripleCharges (sourceA1984 + difference 0 0) (sourceB1984 + difference 0 0) sourceC1984) = raw27361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1984 sourceB1984 sourceC1984 difference raw27361; decide +kernel
    rw [ha]
    exact (canonical27361 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1984 + difference 0 1) (sourceB1984 + difference 1 0) sourceC1984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA1984 + difference 0 1) (sourceB1984 + difference 1 0) sourceC1984) = raw27444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1984 sourceB1984 sourceC1984 difference raw27444; decide +kernel
    rw [ha]
    exact (canonical27444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1984 + difference 0 2) (sourceB1984 + difference 2 0) sourceC1984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1868) := by
    have ha : (tripleCharges (sourceA1984 + difference 0 2) (sourceB1984 + difference 2 0) sourceC1984) = raw28186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1984 sourceB1984 sourceC1984 difference raw28186; decide +kernel
    rw [ha]
    exact (canonical28186 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1984 + difference 0 3) (sourceB1984 + difference 3 0) sourceC1984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1944) := by
    have ha : (tripleCharges (sourceA1984 + difference 0 3) (sourceB1984 + difference 3 0) sourceC1984) = raw28187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1984 sourceB1984 sourceC1984 difference raw28187; decide +kernel
    rw [ha]
    exact (canonical28187 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1984 + difference 0 4) (sourceB1984 + difference 4 0) sourceC1984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1779) := by
    have ha : (tripleCharges (sourceA1984 + difference 0 4) (sourceB1984 + difference 4 0) sourceC1984) = raw28188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1984 sourceB1984 sourceC1984 difference raw28188; decide +kernel
    rw [ha]
    exact (canonical28188 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1984 + difference 0 5) (sourceB1984 + difference 5 0) sourceC1984) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA1984 + difference 0 5) (sourceB1984 + difference 5 0) sourceC1984) = raw28189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1984 sourceB1984 sourceC1984 difference raw28189; decide +kernel
    rw [ha]
    exact (canonical28189 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1984 + sourceB1984) sourceC1984) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1984 + sourceB1984) sourceC1984) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1984 sourceB1984 sourceC1984 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1984 sourceB1984 sourceC1984
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1984, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1985 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1985 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1985 : Charge := ![1, 1, 1, 1, -2, -2]
def sourceForm1985 : Integer.Sparse Master := [(Sum.inr 2378, 1), (Sum.inr 2380, 1), (Sum.inr 2383, 2), (Sum.inr 2662, 1), (Sum.inr 3758, 1), (Sum.inr 4087, -1)]

theorem sourceEq1985 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1985 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1985 + difference 0 0) (sourceB1985 + difference 0 0) sourceC1985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2378) := by
    have ha : (tripleCharges (sourceA1985 + difference 0 0) (sourceB1985 + difference 0 0) sourceC1985) = raw28190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1985 sourceB1985 sourceC1985 difference raw28190; decide +kernel
    rw [ha]
    exact (canonical28190 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1985 + difference 0 1) (sourceB1985 + difference 1 0) sourceC1985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2380) := by
    have ha : (tripleCharges (sourceA1985 + difference 0 1) (sourceB1985 + difference 1 0) sourceC1985) = raw28191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1985 sourceB1985 sourceC1985 difference raw28191; decide +kernel
    rw [ha]
    exact (canonical28191 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1985 + difference 0 2) (sourceB1985 + difference 2 0) sourceC1985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2383) := by
    have ha : (tripleCharges (sourceA1985 + difference 0 2) (sourceB1985 + difference 2 0) sourceC1985) = raw28192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1985 sourceB1985 sourceC1985 difference raw28192; decide +kernel
    rw [ha]
    exact (canonical28192 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1985 + difference 0 3) (sourceB1985 + difference 3 0) sourceC1985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2383) := by
    have ha : (tripleCharges (sourceA1985 + difference 0 3) (sourceB1985 + difference 3 0) sourceC1985) = raw28193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1985 sourceB1985 sourceC1985 difference raw28193; decide +kernel
    rw [ha]
    exact (canonical28193 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1985 + difference 0 4) (sourceB1985 + difference 4 0) sourceC1985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA1985 + difference 0 4) (sourceB1985 + difference 4 0) sourceC1985) = raw28194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1985 sourceB1985 sourceC1985 difference raw28194; decide +kernel
    rw [ha]
    exact (canonical28194 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1985 + difference 0 5) (sourceB1985 + difference 5 0) sourceC1985) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA1985 + difference 0 5) (sourceB1985 + difference 5 0) sourceC1985) = raw28195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1985 sourceB1985 sourceC1985 difference raw28195; decide +kernel
    rw [ha]
    exact (canonical28195 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1985 + sourceB1985) sourceC1985) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1985 + sourceB1985) sourceC1985) = raw22391 := by
      apply Matrix.ext; unfold doubleCharges sourceA1985 sourceB1985 sourceC1985 raw22391; decide +kernel
    rw [ha]
    exact (canonical22391 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1985 sourceB1985 sourceC1985
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1985, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1986 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1986 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1986 : Charge := ![1, 1, 1, 1, -2, -2]
def sourceForm1986 : Integer.Sparse Master := [(Sum.inr 2378, 1), (Sum.inr 2913, 1), (Sum.inr 2922, 2), (Sum.inr 3059, 1), (Sum.inr 3758, 1), (Sum.inr 4087, -1)]

theorem sourceEq1986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1986 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1986 + difference 0 5) (sourceB1986 + difference 5 0) sourceC1986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA1986 + difference 0 5) (sourceB1986 + difference 5 0) sourceC1986) = raw28195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1986 sourceB1986 sourceC1986 difference raw28195; decide +kernel
    rw [ha]
    exact (canonical28195 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1986 + difference 1 5) (sourceB1986 + difference 5 1) sourceC1986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA1986 + difference 1 5) (sourceB1986 + difference 5 1) sourceC1986) = raw22389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1986 sourceB1986 sourceC1986 difference raw22389; decide +kernel
    rw [ha]
    exact (canonical22389 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1986 + difference 2 5) (sourceB1986 + difference 5 2) sourceC1986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2922) := by
    have ha : (tripleCharges (sourceA1986 + difference 2 5) (sourceB1986 + difference 5 2) sourceC1986) = raw28196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1986 sourceB1986 sourceC1986 difference raw28196; decide +kernel
    rw [ha]
    exact (canonical28196 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1986 + difference 3 5) (sourceB1986 + difference 5 3) sourceC1986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2922) := by
    have ha : (tripleCharges (sourceA1986 + difference 3 5) (sourceB1986 + difference 5 3) sourceC1986) = raw28197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1986 sourceB1986 sourceC1986 difference raw28197; decide +kernel
    rw [ha]
    exact (canonical28197 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1986 + difference 4 5) (sourceB1986 + difference 5 4) sourceC1986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA1986 + difference 4 5) (sourceB1986 + difference 5 4) sourceC1986) = raw22386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1986 sourceB1986 sourceC1986 difference raw22386; decide +kernel
    rw [ha]
    exact (canonical22386 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1986 + difference 5 5) (sourceB1986 + difference 5 5) sourceC1986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2378) := by
    have ha : (tripleCharges (sourceA1986 + difference 5 5) (sourceB1986 + difference 5 5) sourceC1986) = raw28190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1986 sourceB1986 sourceC1986 difference raw28190; decide +kernel
    rw [ha]
    exact (canonical28190 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1986 + sourceB1986) sourceC1986) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1986 + sourceB1986) sourceC1986) = raw22391 := by
      apply Matrix.ext; unfold doubleCharges sourceA1986 sourceB1986 sourceC1986 raw22391; decide +kernel
    rw [ha]
    exact (canonical22391 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1986 sourceB1986 sourceC1986
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1986, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1987 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1987 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1987 : Charge := ![1, 1, 1, 1, -1, -3]
def sourceForm1987 : Integer.Sparse Master := [(Sum.inr 1898, 1), (Sum.inr 1901, 1), (Sum.inr 1912, 2), (Sum.inr 2191, 1), (Sum.inr 3460, 1), (Sum.inr 4079, -1)]

theorem sourceEq1987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1987 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 0) (sourceB1987 + difference 0 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 0) (sourceB1987 + difference 0 0) sourceC1987) = raw20238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw20238; decide +kernel
    rw [ha]
    exact (canonical20238 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 1) (sourceB1987 + difference 1 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1901) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 1) (sourceB1987 + difference 1 0) sourceC1987) = raw28198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28198; decide +kernel
    rw [ha]
    exact (canonical28198 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 2) (sourceB1987 + difference 2 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 2) (sourceB1987 + difference 2 0) sourceC1987) = raw28199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28199; decide +kernel
    rw [ha]
    exact (canonical28199 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 3) (sourceB1987 + difference 3 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 3) (sourceB1987 + difference 3 0) sourceC1987) = raw28200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28200; decide +kernel
    rw [ha]
    exact (canonical28200 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 4) (sourceB1987 + difference 4 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 4) (sourceB1987 + difference 4 0) sourceC1987) = raw28201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28201; decide +kernel
    rw [ha]
    exact (canonical28201 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1987 + difference 0 5) (sourceB1987 + difference 5 0) sourceC1987) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA1987 + difference 0 5) (sourceB1987 + difference 5 0) sourceC1987) = raw28202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1987 sourceB1987 sourceC1987 difference raw28202; decide +kernel
    rw [ha]
    exact (canonical28202 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1987 + sourceB1987) sourceC1987) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1987 + sourceB1987) sourceC1987) = raw20243 := by
      apply Matrix.ext; unfold doubleCharges sourceA1987 sourceB1987 sourceC1987 raw20243; decide +kernel
    rw [ha]
    exact (canonical20243 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1987 sourceB1987 sourceC1987
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1987, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1988 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1988 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1988 : Charge := ![1, 1, 1, 1, -1, -3]
def sourceForm1988 : Integer.Sparse Master := [(Sum.inr 868, 1), (Sum.inr 1762, 1), (Sum.inr 1877, 1), (Sum.inr 1898, 2), (Sum.inr 1912, 1), (Sum.inr 4079, -1)]

theorem sourceEq1988 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1988 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1988 + difference 0 2) (sourceB1988 + difference 2 0) sourceC1988) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA1988 + difference 0 2) (sourceB1988 + difference 2 0) sourceC1988) = raw28199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1988 sourceB1988 sourceC1988 difference raw28199; decide +kernel
    rw [ha]
    exact (canonical28199 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1988 + difference 1 2) (sourceB1988 + difference 2 1) sourceC1988) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1988 + difference 1 2) (sourceB1988 + difference 2 1) sourceC1988) = raw20239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1988 sourceB1988 sourceC1988 difference raw20239; decide +kernel
    rw [ha]
    exact (canonical20239 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1988 + difference 2 2) (sourceB1988 + difference 2 2) sourceC1988) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1988 + difference 2 2) (sourceB1988 + difference 2 2) sourceC1988) = raw20238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1988 sourceB1988 sourceC1988 difference raw20238; decide +kernel
    rw [ha]
    exact (canonical20238 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1988 + difference 3 2) (sourceB1988 + difference 2 3) sourceC1988) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1877) := by
    have ha : (tripleCharges (sourceA1988 + difference 3 2) (sourceB1988 + difference 2 3) sourceC1988) = raw28203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1988 sourceB1988 sourceC1988 difference raw28203; decide +kernel
    rw [ha]
    exact (canonical28203 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1988 + difference 4 2) (sourceB1988 + difference 2 4) sourceC1988) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1762) := by
    have ha : (tripleCharges (sourceA1988 + difference 4 2) (sourceB1988 + difference 2 4) sourceC1988) = raw28204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1988 sourceB1988 sourceC1988 difference raw28204; decide +kernel
    rw [ha]
    exact (canonical28204 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1988 + difference 5 2) (sourceB1988 + difference 2 5) sourceC1988) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 868) := by
    have ha : (tripleCharges (sourceA1988 + difference 5 2) (sourceB1988 + difference 2 5) sourceC1988) = raw28205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1988 sourceB1988 sourceC1988 difference raw28205; decide +kernel
    rw [ha]
    exact (canonical28205 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1988 + sourceB1988) sourceC1988) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1988 + sourceB1988) sourceC1988) = raw20243 := by
      apply Matrix.ext; unfold doubleCharges sourceA1988 sourceB1988 sourceC1988 raw20243; decide +kernel
    rw [ha]
    exact (canonical20243 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1988 sourceB1988 sourceC1988
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1988, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1989 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1989 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1989 : Charge := ![1, 1, 1, 1, -1, -3]
def sourceForm1989 : Integer.Sparse Master := [(Sum.inr 1898, 1), (Sum.inr 2912, 1), (Sum.inr 2921, 2), (Sum.inr 3058, 1), (Sum.inr 3460, 1), (Sum.inr 4079, -1)]

theorem sourceEq1989 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1989 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1989 + difference 0 5) (sourceB1989 + difference 5 0) sourceC1989) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA1989 + difference 0 5) (sourceB1989 + difference 5 0) sourceC1989) = raw28202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1989 sourceB1989 sourceC1989 difference raw28202; decide +kernel
    rw [ha]
    exact (canonical28202 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1989 + difference 1 5) (sourceB1989 + difference 5 1) sourceC1989) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA1989 + difference 1 5) (sourceB1989 + difference 5 1) sourceC1989) = raw20242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1989 sourceB1989 sourceC1989 difference raw20242; decide +kernel
    rw [ha]
    exact (canonical20242 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1989 + difference 2 5) (sourceB1989 + difference 5 2) sourceC1989) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2921) := by
    have ha : (tripleCharges (sourceA1989 + difference 2 5) (sourceB1989 + difference 5 2) sourceC1989) = raw28206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1989 sourceB1989 sourceC1989 difference raw28206; decide +kernel
    rw [ha]
    exact (canonical28206 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1989 + difference 3 5) (sourceB1989 + difference 5 3) sourceC1989) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2921) := by
    have ha : (tripleCharges (sourceA1989 + difference 3 5) (sourceB1989 + difference 5 3) sourceC1989) = raw28207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1989 sourceB1989 sourceC1989 difference raw28207; decide +kernel
    rw [ha]
    exact (canonical28207 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1989 + difference 4 5) (sourceB1989 + difference 5 4) sourceC1989) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2912) := by
    have ha : (tripleCharges (sourceA1989 + difference 4 5) (sourceB1989 + difference 5 4) sourceC1989) = raw28208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1989 sourceB1989 sourceC1989 difference raw28208; decide +kernel
    rw [ha]
    exact (canonical28208 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1989 + difference 5 5) (sourceB1989 + difference 5 5) sourceC1989) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1989 + difference 5 5) (sourceB1989 + difference 5 5) sourceC1989) = raw20238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1989 sourceB1989 sourceC1989 difference raw20238; decide +kernel
    rw [ha]
    exact (canonical20238 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1989 + sourceB1989) sourceC1989) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1989 + sourceB1989) sourceC1989) = raw20243 := by
      apply Matrix.ext; unfold doubleCharges sourceA1989 sourceB1989 sourceC1989 raw20243; decide +kernel
    rw [ha]
    exact (canonical20243 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1989 sourceB1989 sourceC1989
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1989, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1990 : Charge := ![1, 1, 1, 1, -1, -3]
def sourceB1990 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1990 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1990 : Integer.Sparse Master := [(Sum.inr 875, 1), (Sum.inr 1768, 1), (Sum.inr 1907, 1), (Sum.inr 1940, 1), (Sum.inr 1944, 2), (Sum.inr 4081, -1)]

theorem sourceEq1990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1990 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1990 + difference 0 0) (sourceB1990 + difference 0 0) sourceC1990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1940) := by
    have ha : (tripleCharges (sourceA1990 + difference 0 0) (sourceB1990 + difference 0 0) sourceC1990) = raw27381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1990 sourceB1990 sourceC1990 difference raw27381; decide +kernel
    rw [ha]
    exact (canonical27381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1990 + difference 0 1) (sourceB1990 + difference 1 0) sourceC1990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1907) := by
    have ha : (tripleCharges (sourceA1990 + difference 0 1) (sourceB1990 + difference 1 0) sourceC1990) = raw27454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1990 sourceB1990 sourceC1990 difference raw27454; decide +kernel
    rw [ha]
    exact (canonical27454 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1990 + difference 0 2) (sourceB1990 + difference 2 0) sourceC1990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1944) := by
    have ha : (tripleCharges (sourceA1990 + difference 0 2) (sourceB1990 + difference 2 0) sourceC1990) = raw28187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1990 sourceB1990 sourceC1990 difference raw28187; decide +kernel
    rw [ha]
    exact (canonical28187 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1990 + difference 0 3) (sourceB1990 + difference 3 0) sourceC1990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1944) := by
    have ha : (tripleCharges (sourceA1990 + difference 0 3) (sourceB1990 + difference 3 0) sourceC1990) = raw28209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1990 sourceB1990 sourceC1990 difference raw28209; decide +kernel
    rw [ha]
    exact (canonical28209 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1990 + difference 0 4) (sourceB1990 + difference 4 0) sourceC1990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1768) := by
    have ha : (tripleCharges (sourceA1990 + difference 0 4) (sourceB1990 + difference 4 0) sourceC1990) = raw28210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1990 sourceB1990 sourceC1990 difference raw28210; decide +kernel
    rw [ha]
    exact (canonical28210 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1990 + difference 0 5) (sourceB1990 + difference 5 0) sourceC1990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 875) := by
    have ha : (tripleCharges (sourceA1990 + difference 0 5) (sourceB1990 + difference 5 0) sourceC1990) = raw28211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1990 sourceB1990 sourceC1990 difference raw28211; decide +kernel
    rw [ha]
    exact (canonical28211 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1990 + sourceB1990) sourceC1990) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1990 + sourceB1990) sourceC1990) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1990 sourceB1990 sourceC1990 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1990 sourceB1990 sourceC1990
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1990, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1991 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1991 : Charge := ![2, -1, 1, 0, -2, 0]
def sourceC1991 : Charge := ![1, 2, -1, 0, 1, -3]
def sourceForm1991 : Integer.Sparse Master := [(Sum.inr 2076, 1), (Sum.inr 2080, 1), (Sum.inr 2082, 1), (Sum.inr 2102, 1), (Sum.inr 2206, 1), (Sum.inr 3565, 1), (Sum.inr 4080, -1)]

theorem sourceEq1991 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1991 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 0) (sourceB1991 + difference 0 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2080) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 0) (sourceB1991 + difference 0 0) sourceC1991) = raw28212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28212; decide +kernel
    rw [ha]
    exact (canonical28212 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 1) (sourceB1991 + difference 1 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 1) (sourceB1991 + difference 1 0) sourceC1991) = raw28213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28213; decide +kernel
    rw [ha]
    exact (canonical28213 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 2) (sourceB1991 + difference 2 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2102) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 2) (sourceB1991 + difference 2 0) sourceC1991) = raw28214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28214; decide +kernel
    rw [ha]
    exact (canonical28214 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 3) (sourceB1991 + difference 3 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2076) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 3) (sourceB1991 + difference 3 0) sourceC1991) = raw28215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28215; decide +kernel
    rw [ha]
    exact (canonical28215 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 4) (sourceB1991 + difference 4 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 4) (sourceB1991 + difference 4 0) sourceC1991) = raw28216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28216; decide +kernel
    rw [ha]
    exact (canonical28216 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1991 + difference 0 5) (sourceB1991 + difference 5 0) sourceC1991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA1991 + difference 0 5) (sourceB1991 + difference 5 0) sourceC1991) = raw28217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1991 sourceB1991 sourceC1991 difference raw28217; decide +kernel
    rw [ha]
    exact (canonical28217 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1991 + sourceB1991) sourceC1991) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1991 + sourceB1991) sourceC1991) = raw28218 := by
      apply Matrix.ext; unfold doubleCharges sourceA1991 sourceB1991 sourceC1991 raw28218; decide +kernel
    rw [ha]
    exact (canonical28218 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1991 sourceB1991 sourceC1991
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1991, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1992 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1992 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC1992 : Charge := ![1, 2, -1, 1, -1, -2]
def sourceForm1992 : Integer.Sparse Master := [(Sum.inr 2450, 1), (Sum.inr 2452, 1), (Sum.inr 2462, 1), (Sum.inr 2478, 1), (Sum.inr 2695, 1), (Sum.inr 3794, 1), (Sum.inr 4090, -1)]

theorem sourceEq1992 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1992 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1992 + difference 0 0) (sourceB1992 + difference 0 0) sourceC1992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2450) := by
    have ha : (tripleCharges (sourceA1992 + difference 0 0) (sourceB1992 + difference 0 0) sourceC1992) = raw28219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1992 sourceB1992 sourceC1992 difference raw28219; decide +kernel
    rw [ha]
    exact (canonical28219 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1992 + difference 0 1) (sourceB1992 + difference 1 0) sourceC1992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA1992 + difference 0 1) (sourceB1992 + difference 1 0) sourceC1992) = raw28220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1992 sourceB1992 sourceC1992 difference raw28220; decide +kernel
    rw [ha]
    exact (canonical28220 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1992 + difference 0 2) (sourceB1992 + difference 2 0) sourceC1992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2478) := by
    have ha : (tripleCharges (sourceA1992 + difference 0 2) (sourceB1992 + difference 2 0) sourceC1992) = raw28221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1992 sourceB1992 sourceC1992 difference raw28221; decide +kernel
    rw [ha]
    exact (canonical28221 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1992 + difference 0 3) (sourceB1992 + difference 3 0) sourceC1992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA1992 + difference 0 3) (sourceB1992 + difference 3 0) sourceC1992) = raw28222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1992 sourceB1992 sourceC1992 difference raw28222; decide +kernel
    rw [ha]
    exact (canonical28222 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1992 + difference 0 4) (sourceB1992 + difference 4 0) sourceC1992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA1992 + difference 0 4) (sourceB1992 + difference 4 0) sourceC1992) = raw28223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1992 sourceB1992 sourceC1992 difference raw28223; decide +kernel
    rw [ha]
    exact (canonical28223 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1992 + difference 0 5) (sourceB1992 + difference 5 0) sourceC1992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA1992 + difference 0 5) (sourceB1992 + difference 5 0) sourceC1992) = raw28224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1992 sourceB1992 sourceC1992 difference raw28224; decide +kernel
    rw [ha]
    exact (canonical28224 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1992 + sourceB1992) sourceC1992) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1992 + sourceB1992) sourceC1992) = raw28225 := by
      apply Matrix.ext; unfold doubleCharges sourceA1992 sourceB1992 sourceC1992 raw28225; decide +kernel
    rw [ha]
    exact (canonical28225 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1992 sourceB1992 sourceC1992
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1992, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1993 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1993 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1993 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceForm1993 : Integer.Sparse Master := [(Sum.inr 1325, 1), (Sum.inr 2811, 2), (Sum.inr 2820, 1), (Sum.inr 2886, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

theorem sourceEq1993 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1993 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1993 + difference 0 1) (sourceB1993 + difference 1 0) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA1993 + difference 0 1) (sourceB1993 + difference 1 0) sourceC1993) = raw28226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28226; decide +kernel
    rw [ha]
    exact (canonical28226 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1993 + difference 1 1) (sourceB1993 + difference 1 1) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2886) := by
    have ha : (tripleCharges (sourceA1993 + difference 1 1) (sourceB1993 + difference 1 1) sourceC1993) = raw28227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28227; decide +kernel
    rw [ha]
    exact (canonical28227 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1993 + difference 2 1) (sourceB1993 + difference 1 2) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2811) := by
    have ha : (tripleCharges (sourceA1993 + difference 2 1) (sourceB1993 + difference 1 2) sourceC1993) = raw28228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28228; decide +kernel
    rw [ha]
    exact (canonical28228 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1993 + difference 3 1) (sourceB1993 + difference 1 3) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2811) := by
    have ha : (tripleCharges (sourceA1993 + difference 3 1) (sourceB1993 + difference 1 3) sourceC1993) = raw28229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28229; decide +kernel
    rw [ha]
    exact (canonical28229 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1993 + difference 4 1) (sourceB1993 + difference 1 4) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2820) := by
    have ha : (tripleCharges (sourceA1993 + difference 4 1) (sourceB1993 + difference 1 4) sourceC1993) = raw28230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28230; decide +kernel
    rw [ha]
    exact (canonical28230 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1993 + difference 5 1) (sourceB1993 + difference 1 5) sourceC1993) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1325) := by
    have ha : (tripleCharges (sourceA1993 + difference 5 1) (sourceB1993 + difference 1 5) sourceC1993) = raw28231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1993 sourceB1993 sourceC1993 difference raw28231; decide +kernel
    rw [ha]
    exact (canonical28231 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1993 + sourceB1993) sourceC1993) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1993 + sourceB1993) sourceC1993) = raw28232 := by
      apply Matrix.ext; unfold doubleCharges sourceA1993 sourceB1993 sourceC1993 raw28232; decide +kernel
    rw [ha]
    exact (canonical28232 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1993 sourceB1993 sourceC1993
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1993, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1994 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1994 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceC1994 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm1994 : Integer.Sparse Master := [(Sum.inr 4309, 2), (Sum.inr 4315, 1), (Sum.inr 4319, 1), (Sum.inr 4507, 1), (Sum.inr 4517, 2), (Sum.inr 4520, 1), (Sum.inr 4608, 1), (Sum.inr 4919, 2), (Sum.inr 4925, 1), (Sum.inr 4982, 2), (Sum.inr 5027, 2), (Sum.inr 5078, 2), (Sum.inr 5105, 2), (Sum.inr 5109, 2), (Sum.inr 5110, 1), (Sum.inr 5203, 2), (Sum.inr 5207, 1), (Sum.inr 5293, 1), (Sum.inr 5296, 1), (Sum.inr 5310, 1), (Sum.inr 5451, 1)]

theorem sourceEq1994 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1994 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1994 + difference 0 1) (sourceB1994 + difference 1 0) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA1994 + difference 0 1) (sourceB1994 + difference 1 0) sourceC1994) = raw16245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw16245; decide +kernel
    rw [ha]
    exact (canonical16245 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1994 + difference 0 2) (sourceB1994 + difference 2 0) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA1994 + difference 0 2) (sourceB1994 + difference 2 0) sourceC1994) = raw16246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw16246; decide +kernel
    rw [ha]
    exact (canonical16246 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1994 + difference 0 3) (sourceB1994 + difference 3 0) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA1994 + difference 0 3) (sourceB1994 + difference 3 0) sourceC1994) = raw16247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw16247; decide +kernel
    rw [ha]
    exact (canonical16247 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1994 + difference 0 4) (sourceB1994 + difference 4 0) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA1994 + difference 0 4) (sourceB1994 + difference 4 0) sourceC1994) = raw16248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw16248; decide +kernel
    rw [ha]
    exact (canonical16248 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1994 + difference 0 5) (sourceB1994 + difference 5 0) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1994 + difference 0 5) (sourceB1994 + difference 5 0) sourceC1994) = raw28233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28233; decide +kernel
    rw [ha]
    exact (canonical28233 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1994 + difference 1 0) (sourceB1994 + difference 0 1) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1994 + difference 1 0) (sourceB1994 + difference 0 1) sourceC1994) = raw28234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28234; decide +kernel
    rw [ha]
    exact (canonical28234 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1994 + difference 1 2) (sourceB1994 + difference 2 1) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1994 + difference 1 2) (sourceB1994 + difference 2 1) sourceC1994) = raw28235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28235; decide +kernel
    rw [ha]
    exact (canonical28235 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1994 + difference 1 3) (sourceB1994 + difference 3 1) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1994 + difference 1 3) (sourceB1994 + difference 3 1) sourceC1994) = raw28236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28236; decide +kernel
    rw [ha]
    exact (canonical28236 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1994 + difference 1 4) (sourceB1994 + difference 4 1) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1994 + difference 1 4) (sourceB1994 + difference 4 1) sourceC1994) = raw28237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28237; decide +kernel
    rw [ha]
    exact (canonical28237 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1994 + difference 1 5) (sourceB1994 + difference 5 1) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1994 + difference 1 5) (sourceB1994 + difference 5 1) sourceC1994) = raw16224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw16224; decide +kernel
    rw [ha]
    exact (canonical16224 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1994 + difference 2 0) (sourceB1994 + difference 0 2) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4517) := by
    have ha : (tripleCharges (sourceA1994 + difference 2 0) (sourceB1994 + difference 0 2) sourceC1994) = raw28238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28238; decide +kernel
    rw [ha]
    exact (canonical28238 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1994 + difference 2 1) (sourceB1994 + difference 1 2) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4982) := by
    have ha : (tripleCharges (sourceA1994 + difference 2 1) (sourceB1994 + difference 1 2) sourceC1994) = raw28239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28239; decide +kernel
    rw [ha]
    exact (canonical28239 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1994 + difference 2 3) (sourceB1994 + difference 3 2) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5027) := by
    have ha : (tripleCharges (sourceA1994 + difference 2 3) (sourceB1994 + difference 3 2) sourceC1994) = raw28240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28240; decide +kernel
    rw [ha]
    exact (canonical28240 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1994 + difference 2 4) (sourceB1994 + difference 4 2) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1994 + difference 2 4) (sourceB1994 + difference 4 2) sourceC1994) = raw28241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28241; decide +kernel
    rw [ha]
    exact (canonical28241 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1994 + difference 2 5) (sourceB1994 + difference 5 2) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA1994 + difference 2 5) (sourceB1994 + difference 5 2) sourceC1994) = raw16229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw16229; decide +kernel
    rw [ha]
    exact (canonical16229 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1994 + difference 3 0) (sourceB1994 + difference 0 3) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4517) := by
    have ha : (tripleCharges (sourceA1994 + difference 3 0) (sourceB1994 + difference 0 3) sourceC1994) = raw28242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28242; decide +kernel
    rw [ha]
    exact (canonical28242 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1994 + difference 3 1) (sourceB1994 + difference 1 3) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4982) := by
    have ha : (tripleCharges (sourceA1994 + difference 3 1) (sourceB1994 + difference 1 3) sourceC1994) = raw28243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28243; decide +kernel
    rw [ha]
    exact (canonical28243 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1994 + difference 3 2) (sourceB1994 + difference 2 3) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5027) := by
    have ha : (tripleCharges (sourceA1994 + difference 3 2) (sourceB1994 + difference 2 3) sourceC1994) = raw28244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28244; decide +kernel
    rw [ha]
    exact (canonical28244 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1994 + difference 3 4) (sourceB1994 + difference 4 3) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1994 + difference 3 4) (sourceB1994 + difference 4 3) sourceC1994) = raw28245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28245; decide +kernel
    rw [ha]
    exact (canonical28245 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1994 + difference 3 5) (sourceB1994 + difference 5 3) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA1994 + difference 3 5) (sourceB1994 + difference 5 3) sourceC1994) = raw16234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw16234; decide +kernel
    rw [ha]
    exact (canonical16234 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1994 + difference 4 0) (sourceB1994 + difference 0 4) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4520) := by
    have ha : (tripleCharges (sourceA1994 + difference 4 0) (sourceB1994 + difference 0 4) sourceC1994) = raw28246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28246; decide +kernel
    rw [ha]
    exact (canonical28246 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1994 + difference 4 1) (sourceB1994 + difference 1 4) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4925) := by
    have ha : (tripleCharges (sourceA1994 + difference 4 1) (sourceB1994 + difference 1 4) sourceC1994) = raw28247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28247; decide +kernel
    rw [ha]
    exact (canonical28247 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1994 + difference 4 2) (sourceB1994 + difference 2 4) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA1994 + difference 4 2) (sourceB1994 + difference 2 4) sourceC1994) = raw28248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28248; decide +kernel
    rw [ha]
    exact (canonical28248 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1994 + difference 4 3) (sourceB1994 + difference 3 4) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA1994 + difference 4 3) (sourceB1994 + difference 3 4) sourceC1994) = raw28249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28249; decide +kernel
    rw [ha]
    exact (canonical28249 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1994 + difference 4 5) (sourceB1994 + difference 5 4) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA1994 + difference 4 5) (sourceB1994 + difference 5 4) sourceC1994) = raw16239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw16239; decide +kernel
    rw [ha]
    exact (canonical16239 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1994 + difference 5 0) (sourceB1994 + difference 0 5) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1994 + difference 5 0) (sourceB1994 + difference 0 5) sourceC1994) = raw28250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28250; decide +kernel
    rw [ha]
    exact (canonical28250 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1994 + difference 5 1) (sourceB1994 + difference 1 5) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1994 + difference 5 1) (sourceB1994 + difference 1 5) sourceC1994) = raw28251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28251; decide +kernel
    rw [ha]
    exact (canonical28251 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1994 + difference 5 2) (sourceB1994 + difference 2 5) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1994 + difference 5 2) (sourceB1994 + difference 2 5) sourceC1994) = raw28252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28252; decide +kernel
    rw [ha]
    exact (canonical28252 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1994 + difference 5 3) (sourceB1994 + difference 3 5) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1994 + difference 5 3) (sourceB1994 + difference 3 5) sourceC1994) = raw28253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28253; decide +kernel
    rw [ha]
    exact (canonical28253 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1994 + difference 5 4) (sourceB1994 + difference 4 5) sourceC1994) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1994 + difference 5 4) (sourceB1994 + difference 4 5) sourceC1994) = raw28254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1994 sourceB1994 sourceC1994 difference raw28254; decide +kernel
    rw [ha]
    exact (canonical28254 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1994 sourceB1994 sourceC1994
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1994, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1995 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1995 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceC1995 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm1995 : Integer.Sparse Master := [(Sum.inr 887, 2), (Sum.inr 893, 1), (Sum.inr 897, 1), (Sum.inr 1091, 1), (Sum.inr 1101, 2), (Sum.inr 1104, 1), (Sum.inr 1242, 1), (Sum.inr 2310, 2), (Sum.inr 2315, 1), (Sum.inr 2416, 2), (Sum.inr 2421, 2), (Sum.inr 2485, 2), (Sum.inr 2515, 2), (Sum.inr 2519, 2), (Sum.inr 2522, 1), (Sum.inr 2770, 1), (Sum.inr 2788, 1), (Sum.inr 2884, 2), (Sum.inr 2889, 1), (Sum.inr 3102, 1), (Sum.inr 3987, 1)]

theorem sourceEq1995 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1995 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1995 + difference 0 1) (sourceB1995 + difference 1 0) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA1995 + difference 0 1) (sourceB1995 + difference 1 0) sourceC1995) = raw16275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw16275; decide +kernel
    rw [ha]
    exact (canonical16275 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1995 + difference 0 2) (sourceB1995 + difference 2 0) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA1995 + difference 0 2) (sourceB1995 + difference 2 0) sourceC1995) = raw16276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw16276; decide +kernel
    rw [ha]
    exact (canonical16276 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1995 + difference 0 3) (sourceB1995 + difference 3 0) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA1995 + difference 0 3) (sourceB1995 + difference 3 0) sourceC1995) = raw16277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw16277; decide +kernel
    rw [ha]
    exact (canonical16277 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1995 + difference 0 4) (sourceB1995 + difference 4 0) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA1995 + difference 0 4) (sourceB1995 + difference 4 0) sourceC1995) = raw16278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw16278; decide +kernel
    rw [ha]
    exact (canonical16278 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1995 + difference 0 5) (sourceB1995 + difference 5 0) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA1995 + difference 0 5) (sourceB1995 + difference 5 0) sourceC1995) = raw28255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28255; decide +kernel
    rw [ha]
    exact (canonical28255 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1995 + difference 1 0) (sourceB1995 + difference 0 1) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1995 + difference 1 0) (sourceB1995 + difference 0 1) sourceC1995) = raw28256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28256; decide +kernel
    rw [ha]
    exact (canonical28256 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1995 + difference 1 2) (sourceB1995 + difference 2 1) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1995 + difference 1 2) (sourceB1995 + difference 2 1) sourceC1995) = raw28257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28257; decide +kernel
    rw [ha]
    exact (canonical28257 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1995 + difference 1 3) (sourceB1995 + difference 3 1) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1995 + difference 1 3) (sourceB1995 + difference 3 1) sourceC1995) = raw28258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28258; decide +kernel
    rw [ha]
    exact (canonical28258 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1995 + difference 1 4) (sourceB1995 + difference 4 1) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA1995 + difference 1 4) (sourceB1995 + difference 4 1) sourceC1995) = raw28259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28259; decide +kernel
    rw [ha]
    exact (canonical28259 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1995 + difference 1 5) (sourceB1995 + difference 5 1) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA1995 + difference 1 5) (sourceB1995 + difference 5 1) sourceC1995) = raw16254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw16254; decide +kernel
    rw [ha]
    exact (canonical16254 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1995 + difference 2 0) (sourceB1995 + difference 0 2) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1101) := by
    have ha : (tripleCharges (sourceA1995 + difference 2 0) (sourceB1995 + difference 0 2) sourceC1995) = raw28260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28260; decide +kernel
    rw [ha]
    exact (canonical28260 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1995 + difference 2 1) (sourceB1995 + difference 1 2) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2421) := by
    have ha : (tripleCharges (sourceA1995 + difference 2 1) (sourceB1995 + difference 1 2) sourceC1995) = raw28261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28261; decide +kernel
    rw [ha]
    exact (canonical28261 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1995 + difference 2 3) (sourceB1995 + difference 3 2) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2416) := by
    have ha : (tripleCharges (sourceA1995 + difference 2 3) (sourceB1995 + difference 3 2) sourceC1995) = raw28262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28262; decide +kernel
    rw [ha]
    exact (canonical28262 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1995 + difference 2 4) (sourceB1995 + difference 4 2) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1995 + difference 2 4) (sourceB1995 + difference 4 2) sourceC1995) = raw28263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28263; decide +kernel
    rw [ha]
    exact (canonical28263 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1995 + difference 2 5) (sourceB1995 + difference 5 2) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA1995 + difference 2 5) (sourceB1995 + difference 5 2) sourceC1995) = raw16259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw16259; decide +kernel
    rw [ha]
    exact (canonical16259 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1995 + difference 3 0) (sourceB1995 + difference 0 3) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1101) := by
    have ha : (tripleCharges (sourceA1995 + difference 3 0) (sourceB1995 + difference 0 3) sourceC1995) = raw28264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28264; decide +kernel
    rw [ha]
    exact (canonical28264 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1995 + difference 3 1) (sourceB1995 + difference 1 3) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2421) := by
    have ha : (tripleCharges (sourceA1995 + difference 3 1) (sourceB1995 + difference 1 3) sourceC1995) = raw28265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28265; decide +kernel
    rw [ha]
    exact (canonical28265 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1995 + difference 3 2) (sourceB1995 + difference 2 3) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2416) := by
    have ha : (tripleCharges (sourceA1995 + difference 3 2) (sourceB1995 + difference 2 3) sourceC1995) = raw28266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28266; decide +kernel
    rw [ha]
    exact (canonical28266 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1995 + difference 3 4) (sourceB1995 + difference 4 3) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1995 + difference 3 4) (sourceB1995 + difference 4 3) sourceC1995) = raw28267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28267; decide +kernel
    rw [ha]
    exact (canonical28267 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1995 + difference 3 5) (sourceB1995 + difference 5 3) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA1995 + difference 3 5) (sourceB1995 + difference 5 3) sourceC1995) = raw16264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw16264; decide +kernel
    rw [ha]
    exact (canonical16264 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1995 + difference 4 0) (sourceB1995 + difference 0 4) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1104) := by
    have ha : (tripleCharges (sourceA1995 + difference 4 0) (sourceB1995 + difference 0 4) sourceC1995) = raw28268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28268; decide +kernel
    rw [ha]
    exact (canonical28268 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1995 + difference 4 1) (sourceB1995 + difference 1 4) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2315) := by
    have ha : (tripleCharges (sourceA1995 + difference 4 1) (sourceB1995 + difference 1 4) sourceC1995) = raw28269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28269; decide +kernel
    rw [ha]
    exact (canonical28269 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1995 + difference 4 2) (sourceB1995 + difference 2 4) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2310) := by
    have ha : (tripleCharges (sourceA1995 + difference 4 2) (sourceB1995 + difference 2 4) sourceC1995) = raw28270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28270; decide +kernel
    rw [ha]
    exact (canonical28270 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1995 + difference 4 3) (sourceB1995 + difference 3 4) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2310) := by
    have ha : (tripleCharges (sourceA1995 + difference 4 3) (sourceB1995 + difference 3 4) sourceC1995) = raw28271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28271; decide +kernel
    rw [ha]
    exact (canonical28271 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1995 + difference 4 5) (sourceB1995 + difference 5 4) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA1995 + difference 4 5) (sourceB1995 + difference 5 4) sourceC1995) = raw16269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw16269; decide +kernel
    rw [ha]
    exact (canonical16269 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1995 + difference 5 0) (sourceB1995 + difference 0 5) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1995 + difference 5 0) (sourceB1995 + difference 0 5) sourceC1995) = raw28272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28272; decide +kernel
    rw [ha]
    exact (canonical28272 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1995 + difference 5 1) (sourceB1995 + difference 1 5) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 897) := by
    have ha : (tripleCharges (sourceA1995 + difference 5 1) (sourceB1995 + difference 1 5) sourceC1995) = raw28273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28273; decide +kernel
    rw [ha]
    exact (canonical28273 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1995 + difference 5 2) (sourceB1995 + difference 2 5) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1995 + difference 5 2) (sourceB1995 + difference 2 5) sourceC1995) = raw28274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28274; decide +kernel
    rw [ha]
    exact (canonical28274 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1995 + difference 5 3) (sourceB1995 + difference 3 5) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1995 + difference 5 3) (sourceB1995 + difference 3 5) sourceC1995) = raw28275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28275; decide +kernel
    rw [ha]
    exact (canonical28275 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1995 + difference 5 4) (sourceB1995 + difference 4 5) sourceC1995) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1995 + difference 5 4) (sourceB1995 + difference 4 5) sourceC1995) = raw28276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1995 sourceB1995 sourceC1995 difference raw28276; decide +kernel
    rw [ha]
    exact (canonical28276 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1995 sourceB1995 sourceC1995
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1995, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1996 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1996 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1996 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceForm1996 : Integer.Sparse Master := [(Sum.inr 4367, 2), (Sum.inr 4370, 1), (Sum.inr 4374, 1), (Sum.inr 4476, 1), (Sum.inr 4547, 2), (Sum.inr 4559, 1), (Sum.inr 4609, 1), (Sum.inr 4944, 2), (Sum.inr 4953, 1), (Sum.inr 4972, 2), (Sum.inr 5034, 2), (Sum.inr 5087, 2), (Sum.inr 5102, 2), (Sum.inr 5111, 1), (Sum.inr 5139, 2), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5268, 1), (Sum.inr 5275, 1), (Sum.inr 5302, 1), (Sum.inr 5413, 1)]

theorem sourceEq1996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1996 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 1) (sourceB1996 + difference 1 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 1) (sourceB1996 + difference 1 0) sourceC1996) = raw28277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28277; decide +kernel
    rw [ha]
    exact (canonical28277 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 2) (sourceB1996 + difference 2 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 2) (sourceB1996 + difference 2 0) sourceC1996) = raw28278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28278; decide +kernel
    rw [ha]
    exact (canonical28278 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 3) (sourceB1996 + difference 3 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 3) (sourceB1996 + difference 3 0) sourceC1996) = raw28279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28279; decide +kernel
    rw [ha]
    exact (canonical28279 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 4) (sourceB1996 + difference 4 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 4) (sourceB1996 + difference 4 0) sourceC1996) = raw28280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28280; decide +kernel
    rw [ha]
    exact (canonical28280 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 5) (sourceB1996 + difference 5 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 5) (sourceB1996 + difference 5 0) sourceC1996) = raw28281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28281; decide +kernel
    rw [ha]
    exact (canonical28281 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 0) (sourceB1996 + difference 0 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 0) (sourceB1996 + difference 0 1) sourceC1996) = raw28282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28282; decide +kernel
    rw [ha]
    exact (canonical28282 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 2) (sourceB1996 + difference 2 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 2) (sourceB1996 + difference 2 1) sourceC1996) = raw28283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28283; decide +kernel
    rw [ha]
    exact (canonical28283 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 3) (sourceB1996 + difference 3 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 3) (sourceB1996 + difference 3 1) sourceC1996) = raw28284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28284; decide +kernel
    rw [ha]
    exact (canonical28284 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 4) (sourceB1996 + difference 4 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 4) (sourceB1996 + difference 4 1) sourceC1996) = raw28285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28285; decide +kernel
    rw [ha]
    exact (canonical28285 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 5) (sourceB1996 + difference 5 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 5) (sourceB1996 + difference 5 1) sourceC1996) = raw28286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28286; decide +kernel
    rw [ha]
    exact (canonical28286 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 0) (sourceB1996 + difference 0 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 0) (sourceB1996 + difference 0 2) sourceC1996) = raw28287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28287; decide +kernel
    rw [ha]
    exact (canonical28287 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 1) (sourceB1996 + difference 1 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 1) (sourceB1996 + difference 1 2) sourceC1996) = raw28288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28288; decide +kernel
    rw [ha]
    exact (canonical28288 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 3) (sourceB1996 + difference 3 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 3) (sourceB1996 + difference 3 2) sourceC1996) = raw28289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28289; decide +kernel
    rw [ha]
    exact (canonical28289 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 4) (sourceB1996 + difference 4 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 4) (sourceB1996 + difference 4 2) sourceC1996) = raw28290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28290; decide +kernel
    rw [ha]
    exact (canonical28290 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 5) (sourceB1996 + difference 5 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 5) (sourceB1996 + difference 5 2) sourceC1996) = raw28291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28291; decide +kernel
    rw [ha]
    exact (canonical28291 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 0) (sourceB1996 + difference 0 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 0) (sourceB1996 + difference 0 3) sourceC1996) = raw28292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28292; decide +kernel
    rw [ha]
    exact (canonical28292 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 1) (sourceB1996 + difference 1 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 1) (sourceB1996 + difference 1 3) sourceC1996) = raw28293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28293; decide +kernel
    rw [ha]
    exact (canonical28293 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 2) (sourceB1996 + difference 2 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 2) (sourceB1996 + difference 2 3) sourceC1996) = raw28294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28294; decide +kernel
    rw [ha]
    exact (canonical28294 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 4) (sourceB1996 + difference 4 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 4) (sourceB1996 + difference 4 3) sourceC1996) = raw28295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28295; decide +kernel
    rw [ha]
    exact (canonical28295 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 5) (sourceB1996 + difference 5 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 5) (sourceB1996 + difference 5 3) sourceC1996) = raw28296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28296; decide +kernel
    rw [ha]
    exact (canonical28296 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 0) (sourceB1996 + difference 0 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 0) (sourceB1996 + difference 0 4) sourceC1996) = raw28297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28297; decide +kernel
    rw [ha]
    exact (canonical28297 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 1) (sourceB1996 + difference 1 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 1) (sourceB1996 + difference 1 4) sourceC1996) = raw28298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28298; decide +kernel
    rw [ha]
    exact (canonical28298 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 2) (sourceB1996 + difference 2 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 2) (sourceB1996 + difference 2 4) sourceC1996) = raw28299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28299; decide +kernel
    rw [ha]
    exact (canonical28299 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 3) (sourceB1996 + difference 3 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 3) (sourceB1996 + difference 3 4) sourceC1996) = raw28300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28300; decide +kernel
    rw [ha]
    exact (canonical28300 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 5) (sourceB1996 + difference 5 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 5) (sourceB1996 + difference 5 4) sourceC1996) = raw28301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28301; decide +kernel
    rw [ha]
    exact (canonical28301 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 0) (sourceB1996 + difference 0 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 0) (sourceB1996 + difference 0 5) sourceC1996) = raw28302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28302; decide +kernel
    rw [ha]
    exact (canonical28302 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 1) (sourceB1996 + difference 1 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 1) (sourceB1996 + difference 1 5) sourceC1996) = raw28303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28303; decide +kernel
    rw [ha]
    exact (canonical28303 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 2) (sourceB1996 + difference 2 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 2) (sourceB1996 + difference 2 5) sourceC1996) = raw28304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28304; decide +kernel
    rw [ha]
    exact (canonical28304 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 3) (sourceB1996 + difference 3 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 3) (sourceB1996 + difference 3 5) sourceC1996) = raw28305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28305; decide +kernel
    rw [ha]
    exact (canonical28305 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 4) (sourceB1996 + difference 4 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 4) (sourceB1996 + difference 4 5) sourceC1996) = raw28306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28306; decide +kernel
    rw [ha]
    exact (canonical28306 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1996 sourceB1996 sourceC1996
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1996, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1997 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1997 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1997 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceForm1997 : Integer.Sparse Master := [(Sum.inr 1720, 2), (Sum.inr 1722, 1), (Sum.inr 1729, 1), (Sum.inr 1748, 1), (Sum.inr 3266, 2), (Sum.inr 3277, 1), (Sum.inr 3302, 1), (Sum.inr 3413, 2), (Sum.inr 3423, 1), (Sum.inr 3451, 2), (Sum.inr 3457, 2), (Sum.inr 3471, 2), (Sum.inr 3472, 2), (Sum.inr 3485, 1), (Sum.inr 3523, 2), (Sum.inr 3548, 1), (Sum.inr 3549, 1), (Sum.inr 3624, 2), (Sum.inr 3626, 1), (Sum.inr 3631, 1), (Sum.inr 3817, 1)]

theorem sourceEq1997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1997 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 1) (sourceB1997 + difference 1 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 1) (sourceB1997 + difference 1 0) sourceC1997) = raw28307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28307; decide +kernel
    rw [ha]
    exact (canonical28307 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 2) (sourceB1997 + difference 2 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 2) (sourceB1997 + difference 2 0) sourceC1997) = raw28308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28308; decide +kernel
    rw [ha]
    exact (canonical28308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 3) (sourceB1997 + difference 3 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 3) (sourceB1997 + difference 3 0) sourceC1997) = raw28309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28309; decide +kernel
    rw [ha]
    exact (canonical28309 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 4) (sourceB1997 + difference 4 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 4) (sourceB1997 + difference 4 0) sourceC1997) = raw28310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28310; decide +kernel
    rw [ha]
    exact (canonical28310 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1997 + difference 0 5) (sourceB1997 + difference 5 0) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA1997 + difference 0 5) (sourceB1997 + difference 5 0) sourceC1997) = raw28311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28311; decide +kernel
    rw [ha]
    exact (canonical28311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 0) (sourceB1997 + difference 0 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 0) (sourceB1997 + difference 0 1) sourceC1997) = raw28312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28312; decide +kernel
    rw [ha]
    exact (canonical28312 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 2) (sourceB1997 + difference 2 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 2) (sourceB1997 + difference 2 1) sourceC1997) = raw28313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28313; decide +kernel
    rw [ha]
    exact (canonical28313 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 3) (sourceB1997 + difference 3 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 3) (sourceB1997 + difference 3 1) sourceC1997) = raw28314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28314; decide +kernel
    rw [ha]
    exact (canonical28314 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 4) (sourceB1997 + difference 4 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 4) (sourceB1997 + difference 4 1) sourceC1997) = raw28315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28315; decide +kernel
    rw [ha]
    exact (canonical28315 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1997 + difference 1 5) (sourceB1997 + difference 5 1) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA1997 + difference 1 5) (sourceB1997 + difference 5 1) sourceC1997) = raw28316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28316; decide +kernel
    rw [ha]
    exact (canonical28316 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 0) (sourceB1997 + difference 0 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 0) (sourceB1997 + difference 0 2) sourceC1997) = raw28317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28317; decide +kernel
    rw [ha]
    exact (canonical28317 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 1) (sourceB1997 + difference 1 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 1) (sourceB1997 + difference 1 2) sourceC1997) = raw28318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28318; decide +kernel
    rw [ha]
    exact (canonical28318 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 3) (sourceB1997 + difference 3 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 3) (sourceB1997 + difference 3 2) sourceC1997) = raw28319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28319; decide +kernel
    rw [ha]
    exact (canonical28319 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 4) (sourceB1997 + difference 4 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 4) (sourceB1997 + difference 4 2) sourceC1997) = raw28320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28320; decide +kernel
    rw [ha]
    exact (canonical28320 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1997 + difference 2 5) (sourceB1997 + difference 5 2) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA1997 + difference 2 5) (sourceB1997 + difference 5 2) sourceC1997) = raw28321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28321; decide +kernel
    rw [ha]
    exact (canonical28321 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 0) (sourceB1997 + difference 0 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 0) (sourceB1997 + difference 0 3) sourceC1997) = raw28322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28322; decide +kernel
    rw [ha]
    exact (canonical28322 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 1) (sourceB1997 + difference 1 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 1) (sourceB1997 + difference 1 3) sourceC1997) = raw28323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28323; decide +kernel
    rw [ha]
    exact (canonical28323 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 2) (sourceB1997 + difference 2 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 2) (sourceB1997 + difference 2 3) sourceC1997) = raw28324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28324; decide +kernel
    rw [ha]
    exact (canonical28324 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 4) (sourceB1997 + difference 4 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 4) (sourceB1997 + difference 4 3) sourceC1997) = raw28325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28325; decide +kernel
    rw [ha]
    exact (canonical28325 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1997 + difference 3 5) (sourceB1997 + difference 5 3) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA1997 + difference 3 5) (sourceB1997 + difference 5 3) sourceC1997) = raw28326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28326; decide +kernel
    rw [ha]
    exact (canonical28326 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 0) (sourceB1997 + difference 0 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 0) (sourceB1997 + difference 0 4) sourceC1997) = raw28327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28327; decide +kernel
    rw [ha]
    exact (canonical28327 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 1) (sourceB1997 + difference 1 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 1) (sourceB1997 + difference 1 4) sourceC1997) = raw28328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28328; decide +kernel
    rw [ha]
    exact (canonical28328 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 2) (sourceB1997 + difference 2 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 2) (sourceB1997 + difference 2 4) sourceC1997) = raw28329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28329; decide +kernel
    rw [ha]
    exact (canonical28329 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 3) (sourceB1997 + difference 3 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 3) (sourceB1997 + difference 3 4) sourceC1997) = raw28330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28330; decide +kernel
    rw [ha]
    exact (canonical28330 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1997 + difference 4 5) (sourceB1997 + difference 5 4) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA1997 + difference 4 5) (sourceB1997 + difference 5 4) sourceC1997) = raw28331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28331; decide +kernel
    rw [ha]
    exact (canonical28331 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 0) (sourceB1997 + difference 0 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 0) (sourceB1997 + difference 0 5) sourceC1997) = raw28332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28332; decide +kernel
    rw [ha]
    exact (canonical28332 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 1) (sourceB1997 + difference 1 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 1) (sourceB1997 + difference 1 5) sourceC1997) = raw28333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28333; decide +kernel
    rw [ha]
    exact (canonical28333 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 2) (sourceB1997 + difference 2 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 2) (sourceB1997 + difference 2 5) sourceC1997) = raw28334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28334; decide +kernel
    rw [ha]
    exact (canonical28334 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 3) (sourceB1997 + difference 3 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 3) (sourceB1997 + difference 3 5) sourceC1997) = raw28335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28335; decide +kernel
    rw [ha]
    exact (canonical28335 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1997 + difference 5 4) (sourceB1997 + difference 4 5) sourceC1997) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1997 + difference 5 4) (sourceB1997 + difference 4 5) sourceC1997) = raw28336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1997 sourceB1997 sourceC1997 difference raw28336; decide +kernel
    rw [ha]
    exact (canonical28336 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1997 sourceB1997 sourceC1997
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1997, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1998 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1998 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1998 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceForm1998 : Integer.Sparse Master := [(Sum.inr 4219, 2), (Sum.inr 4225, 1), (Sum.inr 4229, 1), (Sum.inr 4270, 1), (Sum.inr 4514, 2), (Sum.inr 4519, 1), (Sum.inr 4605, 1), (Sum.inr 4650, 2), (Sum.inr 4657, 1), (Sum.inr 4713, 2), (Sum.inr 4719, 2), (Sum.inr 4742, 2), (Sum.inr 4807, 2), (Sum.inr 4839, 2), (Sum.inr 4845, 1), (Sum.inr 4890, 1), (Sum.inr 4896, 1), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5294, 1), (Sum.inr 5443, 1)]

theorem sourceEq1998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1998 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 1) (sourceB1998 + difference 1 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 1) (sourceB1998 + difference 1 0) sourceC1998) = raw28337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28337; decide +kernel
    rw [ha]
    exact (canonical28337 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 2) (sourceB1998 + difference 2 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 2) (sourceB1998 + difference 2 0) sourceC1998) = raw28338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28338; decide +kernel
    rw [ha]
    exact (canonical28338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 3) (sourceB1998 + difference 3 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 3) (sourceB1998 + difference 3 0) sourceC1998) = raw28339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28339; decide +kernel
    rw [ha]
    exact (canonical28339 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 4) (sourceB1998 + difference 4 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 4) (sourceB1998 + difference 4 0) sourceC1998) = raw28340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28340; decide +kernel
    rw [ha]
    exact (canonical28340 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 5) (sourceB1998 + difference 5 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 5) (sourceB1998 + difference 5 0) sourceC1998) = raw3315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw3315; decide +kernel
    rw [ha]
    exact (canonical3315 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 0) (sourceB1998 + difference 0 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 0) (sourceB1998 + difference 0 1) sourceC1998) = raw28341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28341; decide +kernel
    rw [ha]
    exact (canonical28341 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 2) (sourceB1998 + difference 2 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 2) (sourceB1998 + difference 2 1) sourceC1998) = raw28342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28342; decide +kernel
    rw [ha]
    exact (canonical28342 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 3) (sourceB1998 + difference 3 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 3) (sourceB1998 + difference 3 1) sourceC1998) = raw28343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28343; decide +kernel
    rw [ha]
    exact (canonical28343 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 4) (sourceB1998 + difference 4 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 4) (sourceB1998 + difference 4 1) sourceC1998) = raw28344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28344; decide +kernel
    rw [ha]
    exact (canonical28344 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 5) (sourceB1998 + difference 5 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 5) (sourceB1998 + difference 5 1) sourceC1998) = raw3314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw3314; decide +kernel
    rw [ha]
    exact (canonical3314 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 0) (sourceB1998 + difference 0 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 0) (sourceB1998 + difference 0 2) sourceC1998) = raw28345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28345; decide +kernel
    rw [ha]
    exact (canonical28345 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 1) (sourceB1998 + difference 1 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 1) (sourceB1998 + difference 1 2) sourceC1998) = raw28346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28346; decide +kernel
    rw [ha]
    exact (canonical28346 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 3) (sourceB1998 + difference 3 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4713) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 3) (sourceB1998 + difference 3 2) sourceC1998) = raw28347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28347; decide +kernel
    rw [ha]
    exact (canonical28347 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 4) (sourceB1998 + difference 4 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 4) (sourceB1998 + difference 4 2) sourceC1998) = raw28348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28348; decide +kernel
    rw [ha]
    exact (canonical28348 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 5) (sourceB1998 + difference 5 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 5) (sourceB1998 + difference 5 2) sourceC1998) = raw28349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28349; decide +kernel
    rw [ha]
    exact (canonical28349 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 0) (sourceB1998 + difference 0 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 0) (sourceB1998 + difference 0 3) sourceC1998) = raw28350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28350; decide +kernel
    rw [ha]
    exact (canonical28350 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 1) (sourceB1998 + difference 1 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 1) (sourceB1998 + difference 1 3) sourceC1998) = raw28351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28351; decide +kernel
    rw [ha]
    exact (canonical28351 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 2) (sourceB1998 + difference 2 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4713) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 2) (sourceB1998 + difference 2 3) sourceC1998) = raw28352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28352; decide +kernel
    rw [ha]
    exact (canonical28352 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 4) (sourceB1998 + difference 4 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 4) (sourceB1998 + difference 4 3) sourceC1998) = raw28353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28353; decide +kernel
    rw [ha]
    exact (canonical28353 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 5) (sourceB1998 + difference 5 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 5) (sourceB1998 + difference 5 3) sourceC1998) = raw28354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28354; decide +kernel
    rw [ha]
    exact (canonical28354 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 0) (sourceB1998 + difference 0 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4519) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 0) (sourceB1998 + difference 0 4) sourceC1998) = raw28355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28355; decide +kernel
    rw [ha]
    exact (canonical28355 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 1) (sourceB1998 + difference 1 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4657) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 1) (sourceB1998 + difference 1 4) sourceC1998) = raw28356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28356; decide +kernel
    rw [ha]
    exact (canonical28356 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 2) (sourceB1998 + difference 2 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 2) (sourceB1998 + difference 2 4) sourceC1998) = raw28357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28357; decide +kernel
    rw [ha]
    exact (canonical28357 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 3) (sourceB1998 + difference 3 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 3) (sourceB1998 + difference 3 4) sourceC1998) = raw28358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28358; decide +kernel
    rw [ha]
    exact (canonical28358 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 5) (sourceB1998 + difference 5 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 5) (sourceB1998 + difference 5 4) sourceC1998) = raw28359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28359; decide +kernel
    rw [ha]
    exact (canonical28359 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 0) (sourceB1998 + difference 0 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4225) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 0) (sourceB1998 + difference 0 5) sourceC1998) = raw28360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28360; decide +kernel
    rw [ha]
    exact (canonical28360 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 1) (sourceB1998 + difference 1 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4229) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 1) (sourceB1998 + difference 1 5) sourceC1998) = raw28361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28361; decide +kernel
    rw [ha]
    exact (canonical28361 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 2) (sourceB1998 + difference 2 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4219) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 2) (sourceB1998 + difference 2 5) sourceC1998) = raw28362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28362; decide +kernel
    rw [ha]
    exact (canonical28362 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 3) (sourceB1998 + difference 3 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4219) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 3) (sourceB1998 + difference 3 5) sourceC1998) = raw28363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28363; decide +kernel
    rw [ha]
    exact (canonical28363 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 4) (sourceB1998 + difference 4 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 4) (sourceB1998 + difference 4 5) sourceC1998) = raw28364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28364; decide +kernel
    rw [ha]
    exact (canonical28364 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1998 sourceB1998 sourceC1998
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1998, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1999 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1999 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1999 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceForm1999 : Integer.Sparse Master := [(Sum.inr 720, 2), (Sum.inr 726, 1), (Sum.inr 729, 1), (Sum.inr 813, 1), (Sum.inr 1098, 2), (Sum.inr 1103, 1), (Sum.inr 1239, 1), (Sum.inr 1778, 2), (Sum.inr 1783, 1), (Sum.inr 1867, 2), (Sum.inr 1873, 2), (Sum.inr 1915, 2), (Sum.inr 2025, 2), (Sum.inr 2058, 2), (Sum.inr 2065, 1), (Sum.inr 2247, 1), (Sum.inr 2266, 1), (Sum.inr 2881, 2), (Sum.inr 2889, 1), (Sum.inr 3101, 1), (Sum.inr 3862, 1)]

theorem sourceEq1999 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1999 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1999 + difference 0 1) (sourceB1999 + difference 1 0) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA1999 + difference 0 1) (sourceB1999 + difference 1 0) sourceC1999) = raw28365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28365; decide +kernel
    rw [ha]
    exact (canonical28365 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1999 + difference 0 2) (sourceB1999 + difference 2 0) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA1999 + difference 0 2) (sourceB1999 + difference 2 0) sourceC1999) = raw28366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28366; decide +kernel
    rw [ha]
    exact (canonical28366 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1999 + difference 0 3) (sourceB1999 + difference 3 0) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA1999 + difference 0 3) (sourceB1999 + difference 3 0) sourceC1999) = raw28367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28367; decide +kernel
    rw [ha]
    exact (canonical28367 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1999 + difference 0 4) (sourceB1999 + difference 4 0) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA1999 + difference 0 4) (sourceB1999 + difference 4 0) sourceC1999) = raw28368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28368; decide +kernel
    rw [ha]
    exact (canonical28368 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1999 + difference 0 5) (sourceB1999 + difference 5 0) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA1999 + difference 0 5) (sourceB1999 + difference 5 0) sourceC1999) = raw28369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28369; decide +kernel
    rw [ha]
    exact (canonical28369 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1999 + difference 1 0) (sourceB1999 + difference 0 1) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1999 + difference 1 0) (sourceB1999 + difference 0 1) sourceC1999) = raw28370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28370; decide +kernel
    rw [ha]
    exact (canonical28370 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1999 + difference 1 2) (sourceB1999 + difference 2 1) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1999 + difference 1 2) (sourceB1999 + difference 2 1) sourceC1999) = raw28371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28371; decide +kernel
    rw [ha]
    exact (canonical28371 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1999 + difference 1 3) (sourceB1999 + difference 3 1) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1999 + difference 1 3) (sourceB1999 + difference 3 1) sourceC1999) = raw28372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28372; decide +kernel
    rw [ha]
    exact (canonical28372 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1999 + difference 1 4) (sourceB1999 + difference 4 1) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA1999 + difference 1 4) (sourceB1999 + difference 4 1) sourceC1999) = raw28373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28373; decide +kernel
    rw [ha]
    exact (canonical28373 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1999 + difference 1 5) (sourceB1999 + difference 5 1) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA1999 + difference 1 5) (sourceB1999 + difference 5 1) sourceC1999) = raw28374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28374; decide +kernel
    rw [ha]
    exact (canonical28374 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1999 + difference 2 0) (sourceB1999 + difference 0 2) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA1999 + difference 2 0) (sourceB1999 + difference 0 2) sourceC1999) = raw28375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28375; decide +kernel
    rw [ha]
    exact (canonical28375 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1999 + difference 2 1) (sourceB1999 + difference 1 2) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1873) := by
    have ha : (tripleCharges (sourceA1999 + difference 2 1) (sourceB1999 + difference 1 2) sourceC1999) = raw28376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28376; decide +kernel
    rw [ha]
    exact (canonical28376 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1999 + difference 2 3) (sourceB1999 + difference 3 2) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1867) := by
    have ha : (tripleCharges (sourceA1999 + difference 2 3) (sourceB1999 + difference 3 2) sourceC1999) = raw28377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28377; decide +kernel
    rw [ha]
    exact (canonical28377 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1999 + difference 2 4) (sourceB1999 + difference 4 2) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA1999 + difference 2 4) (sourceB1999 + difference 4 2) sourceC1999) = raw28378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28378; decide +kernel
    rw [ha]
    exact (canonical28378 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1999 + difference 2 5) (sourceB1999 + difference 5 2) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA1999 + difference 2 5) (sourceB1999 + difference 5 2) sourceC1999) = raw28379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28379; decide +kernel
    rw [ha]
    exact (canonical28379 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1999 + difference 3 0) (sourceB1999 + difference 0 3) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA1999 + difference 3 0) (sourceB1999 + difference 0 3) sourceC1999) = raw28380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28380; decide +kernel
    rw [ha]
    exact (canonical28380 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1999 + difference 3 1) (sourceB1999 + difference 1 3) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1873) := by
    have ha : (tripleCharges (sourceA1999 + difference 3 1) (sourceB1999 + difference 1 3) sourceC1999) = raw28381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28381; decide +kernel
    rw [ha]
    exact (canonical28381 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1999 + difference 3 2) (sourceB1999 + difference 2 3) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1867) := by
    have ha : (tripleCharges (sourceA1999 + difference 3 2) (sourceB1999 + difference 2 3) sourceC1999) = raw28382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28382; decide +kernel
    rw [ha]
    exact (canonical28382 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1999 + difference 3 4) (sourceB1999 + difference 4 3) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA1999 + difference 3 4) (sourceB1999 + difference 4 3) sourceC1999) = raw28383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28383; decide +kernel
    rw [ha]
    exact (canonical28383 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1999 + difference 3 5) (sourceB1999 + difference 5 3) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA1999 + difference 3 5) (sourceB1999 + difference 5 3) sourceC1999) = raw28384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28384; decide +kernel
    rw [ha]
    exact (canonical28384 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1999 + difference 4 0) (sourceB1999 + difference 0 4) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1103) := by
    have ha : (tripleCharges (sourceA1999 + difference 4 0) (sourceB1999 + difference 0 4) sourceC1999) = raw28385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28385; decide +kernel
    rw [ha]
    exact (canonical28385 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1999 + difference 4 1) (sourceB1999 + difference 1 4) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1783) := by
    have ha : (tripleCharges (sourceA1999 + difference 4 1) (sourceB1999 + difference 1 4) sourceC1999) = raw28386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28386; decide +kernel
    rw [ha]
    exact (canonical28386 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1999 + difference 4 2) (sourceB1999 + difference 2 4) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1778) := by
    have ha : (tripleCharges (sourceA1999 + difference 4 2) (sourceB1999 + difference 2 4) sourceC1999) = raw28387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28387; decide +kernel
    rw [ha]
    exact (canonical28387 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1999 + difference 4 3) (sourceB1999 + difference 3 4) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1778) := by
    have ha : (tripleCharges (sourceA1999 + difference 4 3) (sourceB1999 + difference 3 4) sourceC1999) = raw28388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28388; decide +kernel
    rw [ha]
    exact (canonical28388 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1999 + difference 4 5) (sourceB1999 + difference 5 4) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA1999 + difference 4 5) (sourceB1999 + difference 5 4) sourceC1999) = raw28389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28389; decide +kernel
    rw [ha]
    exact (canonical28389 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1999 + difference 5 0) (sourceB1999 + difference 0 5) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 726) := by
    have ha : (tripleCharges (sourceA1999 + difference 5 0) (sourceB1999 + difference 0 5) sourceC1999) = raw28390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28390; decide +kernel
    rw [ha]
    exact (canonical28390 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1999 + difference 5 1) (sourceB1999 + difference 1 5) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 729) := by
    have ha : (tripleCharges (sourceA1999 + difference 5 1) (sourceB1999 + difference 1 5) sourceC1999) = raw28391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28391; decide +kernel
    rw [ha]
    exact (canonical28391 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1999 + difference 5 2) (sourceB1999 + difference 2 5) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 720) := by
    have ha : (tripleCharges (sourceA1999 + difference 5 2) (sourceB1999 + difference 2 5) sourceC1999) = raw28392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28392; decide +kernel
    rw [ha]
    exact (canonical28392 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1999 + difference 5 3) (sourceB1999 + difference 3 5) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 720) := by
    have ha : (tripleCharges (sourceA1999 + difference 5 3) (sourceB1999 + difference 3 5) sourceC1999) = raw28393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28393; decide +kernel
    rw [ha]
    exact (canonical28393 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1999 + difference 5 4) (sourceB1999 + difference 4 5) sourceC1999) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1999 + difference 5 4) (sourceB1999 + difference 4 5) sourceC1999) = raw28394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1999 sourceB1999 sourceC1999 difference raw28394; decide +kernel
    rw [ha]
    exact (canonical28394 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1999 sourceB1999 sourceC1999
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1999, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2000 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2000 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2000 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceForm2000 : Integer.Sparse Master := [(Sum.inr 4347, 2), (Sum.inr 4358, 1), (Sum.inr 4361, 1), (Sum.inr 4371, 2), (Sum.inr 4375, 1), (Sum.inr 4478, 1), (Sum.inr 4507, 1), (Sum.inr 4682, 2), (Sum.inr 4693, 1), (Sum.inr 4761, 2), (Sum.inr 4770, 2), (Sum.inr 4817, 2), (Sum.inr 4835, 2), (Sum.inr 4843, 2), (Sum.inr 4846, 1), (Sum.inr 4899, 1), (Sum.inr 4901, 1), (Sum.inr 5205, 2), (Sum.inr 5206, 1), (Sum.inr 5275, 1), (Sum.inr 5276, 1)]

theorem sourceEq2000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2000 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 1) (sourceB2000 + difference 1 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 1) (sourceB2000 + difference 1 0) sourceC2000) = raw28395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28395; decide +kernel
    rw [ha]
    exact (canonical28395 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 2) (sourceB2000 + difference 2 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 2) (sourceB2000 + difference 2 0) sourceC2000) = raw28396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28396; decide +kernel
    rw [ha]
    exact (canonical28396 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 3) (sourceB2000 + difference 3 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 3) (sourceB2000 + difference 3 0) sourceC2000) = raw28397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28397; decide +kernel
    rw [ha]
    exact (canonical28397 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 4) (sourceB2000 + difference 4 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 4) (sourceB2000 + difference 4 0) sourceC2000) = raw28398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28398; decide +kernel
    rw [ha]
    exact (canonical28398 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 5) (sourceB2000 + difference 5 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 5) (sourceB2000 + difference 5 0) sourceC2000) = raw28399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28399; decide +kernel
    rw [ha]
    exact (canonical28399 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 0) (sourceB2000 + difference 0 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 0) (sourceB2000 + difference 0 1) sourceC2000) = raw28400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28400; decide +kernel
    rw [ha]
    exact (canonical28400 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 2) (sourceB2000 + difference 2 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 2) (sourceB2000 + difference 2 1) sourceC2000) = raw28401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28401; decide +kernel
    rw [ha]
    exact (canonical28401 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 3) (sourceB2000 + difference 3 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 3) (sourceB2000 + difference 3 1) sourceC2000) = raw28402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28402; decide +kernel
    rw [ha]
    exact (canonical28402 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 4) (sourceB2000 + difference 4 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 4) (sourceB2000 + difference 4 1) sourceC2000) = raw28403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28403; decide +kernel
    rw [ha]
    exact (canonical28403 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 5) (sourceB2000 + difference 5 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 5) (sourceB2000 + difference 5 1) sourceC2000) = raw28404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28404; decide +kernel
    rw [ha]
    exact (canonical28404 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 0) (sourceB2000 + difference 0 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4371) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 0) (sourceB2000 + difference 0 2) sourceC2000) = raw28405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28405; decide +kernel
    rw [ha]
    exact (canonical28405 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 1) (sourceB2000 + difference 1 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 1) (sourceB2000 + difference 1 2) sourceC2000) = raw28406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28406; decide +kernel
    rw [ha]
    exact (canonical28406 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 3) (sourceB2000 + difference 3 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4761) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 3) (sourceB2000 + difference 3 2) sourceC2000) = raw28407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28407; decide +kernel
    rw [ha]
    exact (canonical28407 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 4) (sourceB2000 + difference 4 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 4) (sourceB2000 + difference 4 2) sourceC2000) = raw28408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28408; decide +kernel
    rw [ha]
    exact (canonical28408 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 5) (sourceB2000 + difference 5 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 5) (sourceB2000 + difference 5 2) sourceC2000) = raw28409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28409; decide +kernel
    rw [ha]
    exact (canonical28409 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 0) (sourceB2000 + difference 0 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4371) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 0) (sourceB2000 + difference 0 3) sourceC2000) = raw28410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28410; decide +kernel
    rw [ha]
    exact (canonical28410 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 1) (sourceB2000 + difference 1 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 1) (sourceB2000 + difference 1 3) sourceC2000) = raw28411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28411; decide +kernel
    rw [ha]
    exact (canonical28411 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 2) (sourceB2000 + difference 2 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4761) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 2) (sourceB2000 + difference 2 3) sourceC2000) = raw28412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28412; decide +kernel
    rw [ha]
    exact (canonical28412 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 4) (sourceB2000 + difference 4 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 4) (sourceB2000 + difference 4 3) sourceC2000) = raw28413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28413; decide +kernel
    rw [ha]
    exact (canonical28413 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 5) (sourceB2000 + difference 5 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 5) (sourceB2000 + difference 5 3) sourceC2000) = raw28414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28414; decide +kernel
    rw [ha]
    exact (canonical28414 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 0) (sourceB2000 + difference 0 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4375) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 0) (sourceB2000 + difference 0 4) sourceC2000) = raw28415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28415; decide +kernel
    rw [ha]
    exact (canonical28415 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 1) (sourceB2000 + difference 1 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 1) (sourceB2000 + difference 1 4) sourceC2000) = raw28416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28416; decide +kernel
    rw [ha]
    exact (canonical28416 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 2) (sourceB2000 + difference 2 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4682) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 2) (sourceB2000 + difference 2 4) sourceC2000) = raw28417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28417; decide +kernel
    rw [ha]
    exact (canonical28417 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 3) (sourceB2000 + difference 3 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4682) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 3) (sourceB2000 + difference 3 4) sourceC2000) = raw28418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28418; decide +kernel
    rw [ha]
    exact (canonical28418 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 5) (sourceB2000 + difference 5 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 5) (sourceB2000 + difference 5 4) sourceC2000) = raw28419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28419; decide +kernel
    rw [ha]
    exact (canonical28419 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 0) (sourceB2000 + difference 0 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4358) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 0) (sourceB2000 + difference 0 5) sourceC2000) = raw28420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28420; decide +kernel
    rw [ha]
    exact (canonical28420 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 1) (sourceB2000 + difference 1 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 1) (sourceB2000 + difference 1 5) sourceC2000) = raw28421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28421; decide +kernel
    rw [ha]
    exact (canonical28421 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 2) (sourceB2000 + difference 2 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 2) (sourceB2000 + difference 2 5) sourceC2000) = raw28422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28422; decide +kernel
    rw [ha]
    exact (canonical28422 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 3) (sourceB2000 + difference 3 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 3) (sourceB2000 + difference 3 5) sourceC2000) = raw28423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28423; decide +kernel
    rw [ha]
    exact (canonical28423 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 4) (sourceB2000 + difference 4 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 4) (sourceB2000 + difference 4 5) sourceC2000) = raw28424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28424; decide +kernel
    rw [ha]
    exact (canonical28424 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2000 sourceB2000 sourceC2000
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2000, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2001 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2001 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2001 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceForm2001 : Integer.Sparse Master := [(Sum.inr 1676, 2), (Sum.inr 1694, 1), (Sum.inr 1695, 1), (Sum.inr 1742, 2), (Sum.inr 1743, 1), (Sum.inr 1746, 1), (Sum.inr 1756, 1), (Sum.inr 2153, 2), (Sum.inr 2169, 1), (Sum.inr 2175, 2), (Sum.inr 2186, 2), (Sum.inr 2206, 2), (Sum.inr 2207, 2), (Sum.inr 2229, 1), (Sum.inr 2230, 2), (Sum.inr 2293, 1), (Sum.inr 2294, 1), (Sum.inr 2687, 1), (Sum.inr 2706, 2), (Sum.inr 2743, 1), (Sum.inr 2744, 1)]

theorem sourceEq2001 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2001 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 1) (sourceB2001 + difference 1 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 1) (sourceB2001 + difference 1 0) sourceC2001) = raw28425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28425; decide +kernel
    rw [ha]
    exact (canonical28425 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 2) (sourceB2001 + difference 2 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 2) (sourceB2001 + difference 2 0) sourceC2001) = raw28426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28426; decide +kernel
    rw [ha]
    exact (canonical28426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 3) (sourceB2001 + difference 3 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 3) (sourceB2001 + difference 3 0) sourceC2001) = raw28427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28427; decide +kernel
    rw [ha]
    exact (canonical28427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 4) (sourceB2001 + difference 4 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 4) (sourceB2001 + difference 4 0) sourceC2001) = raw28428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28428; decide +kernel
    rw [ha]
    exact (canonical28428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2001 + difference 0 5) (sourceB2001 + difference 5 0) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2001 + difference 0 5) (sourceB2001 + difference 5 0) sourceC2001) = raw28429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28429; decide +kernel
    rw [ha]
    exact (canonical28429 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 0) (sourceB2001 + difference 0 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 0) (sourceB2001 + difference 0 1) sourceC2001) = raw28430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28430; decide +kernel
    rw [ha]
    exact (canonical28430 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 2) (sourceB2001 + difference 2 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 2) (sourceB2001 + difference 2 1) sourceC2001) = raw28431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28431; decide +kernel
    rw [ha]
    exact (canonical28431 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 3) (sourceB2001 + difference 3 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 3) (sourceB2001 + difference 3 1) sourceC2001) = raw28432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28432; decide +kernel
    rw [ha]
    exact (canonical28432 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 4) (sourceB2001 + difference 4 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 4) (sourceB2001 + difference 4 1) sourceC2001) = raw28433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28433; decide +kernel
    rw [ha]
    exact (canonical28433 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2001 + difference 1 5) (sourceB2001 + difference 5 1) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA2001 + difference 1 5) (sourceB2001 + difference 5 1) sourceC2001) = raw28434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28434; decide +kernel
    rw [ha]
    exact (canonical28434 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 0) (sourceB2001 + difference 0 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1742) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 0) (sourceB2001 + difference 0 2) sourceC2001) = raw28435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28435; decide +kernel
    rw [ha]
    exact (canonical28435 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 1) (sourceB2001 + difference 1 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 1) (sourceB2001 + difference 1 2) sourceC2001) = raw28436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28436; decide +kernel
    rw [ha]
    exact (canonical28436 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 3) (sourceB2001 + difference 3 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2175) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 3) (sourceB2001 + difference 3 2) sourceC2001) = raw28437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28437; decide +kernel
    rw [ha]
    exact (canonical28437 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 4) (sourceB2001 + difference 4 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 4) (sourceB2001 + difference 4 2) sourceC2001) = raw28438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28438; decide +kernel
    rw [ha]
    exact (canonical28438 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2001 + difference 2 5) (sourceB2001 + difference 5 2) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA2001 + difference 2 5) (sourceB2001 + difference 5 2) sourceC2001) = raw28439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28439; decide +kernel
    rw [ha]
    exact (canonical28439 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 0) (sourceB2001 + difference 0 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1742) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 0) (sourceB2001 + difference 0 3) sourceC2001) = raw28440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28440; decide +kernel
    rw [ha]
    exact (canonical28440 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 1) (sourceB2001 + difference 1 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 1) (sourceB2001 + difference 1 3) sourceC2001) = raw28441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28441; decide +kernel
    rw [ha]
    exact (canonical28441 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 2) (sourceB2001 + difference 2 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2175) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 2) (sourceB2001 + difference 2 3) sourceC2001) = raw28442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28442; decide +kernel
    rw [ha]
    exact (canonical28442 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 4) (sourceB2001 + difference 4 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 4) (sourceB2001 + difference 4 3) sourceC2001) = raw28443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28443; decide +kernel
    rw [ha]
    exact (canonical28443 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2001 + difference 3 5) (sourceB2001 + difference 5 3) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA2001 + difference 3 5) (sourceB2001 + difference 5 3) sourceC2001) = raw28444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28444; decide +kernel
    rw [ha]
    exact (canonical28444 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 0) (sourceB2001 + difference 0 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1743) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 0) (sourceB2001 + difference 0 4) sourceC2001) = raw28445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28445; decide +kernel
    rw [ha]
    exact (canonical28445 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 1) (sourceB2001 + difference 1 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 1) (sourceB2001 + difference 1 4) sourceC2001) = raw28446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28446; decide +kernel
    rw [ha]
    exact (canonical28446 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 2) (sourceB2001 + difference 2 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 2) (sourceB2001 + difference 2 4) sourceC2001) = raw28447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28447; decide +kernel
    rw [ha]
    exact (canonical28447 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 3) (sourceB2001 + difference 3 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 3) (sourceB2001 + difference 3 4) sourceC2001) = raw28448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28448; decide +kernel
    rw [ha]
    exact (canonical28448 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2001 + difference 4 5) (sourceB2001 + difference 5 4) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA2001 + difference 4 5) (sourceB2001 + difference 5 4) sourceC2001) = raw28449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28449; decide +kernel
    rw [ha]
    exact (canonical28449 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 0) (sourceB2001 + difference 0 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 0) (sourceB2001 + difference 0 5) sourceC2001) = raw28450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28450; decide +kernel
    rw [ha]
    exact (canonical28450 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 1) (sourceB2001 + difference 1 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 1) (sourceB2001 + difference 1 5) sourceC2001) = raw28451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28451; decide +kernel
    rw [ha]
    exact (canonical28451 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 2) (sourceB2001 + difference 2 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 2) (sourceB2001 + difference 2 5) sourceC2001) = raw28452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28452; decide +kernel
    rw [ha]
    exact (canonical28452 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 3) (sourceB2001 + difference 3 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 3) (sourceB2001 + difference 3 5) sourceC2001) = raw28453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28453; decide +kernel
    rw [ha]
    exact (canonical28453 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2001 + difference 5 4) (sourceB2001 + difference 4 5) sourceC2001) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA2001 + difference 5 4) (sourceB2001 + difference 4 5) sourceC2001) = raw28454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2001 sourceB2001 sourceC2001 difference raw28454; decide +kernel
    rw [ha]
    exact (canonical28454 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2001 sourceB2001 sourceC2001
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2001, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2002 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2002 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2002 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceForm2002 : Integer.Sparse Master := [(Sum.inr 939, 1), (Sum.inr 1819, 1), (Sum.inr 1970, 2), (Sum.inr 2062, 1), (Sum.inr 2066, 1), (Sum.inr 4084, -1)]

theorem sourceEq2002 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2002 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2002 + difference 0 1) (sourceB2002 + difference 1 0) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA2002 + difference 0 1) (sourceB2002 + difference 1 0) sourceC2002) = raw28455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28455; decide +kernel
    rw [ha]
    exact (canonical28455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2002 + difference 1 1) (sourceB2002 + difference 1 1) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA2002 + difference 1 1) (sourceB2002 + difference 1 1) sourceC2002) = raw28456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28456; decide +kernel
    rw [ha]
    exact (canonical28456 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2002 + difference 2 1) (sourceB2002 + difference 1 2) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2002 + difference 2 1) (sourceB2002 + difference 1 2) sourceC2002) = raw28457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28457; decide +kernel
    rw [ha]
    exact (canonical28457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2002 + difference 3 1) (sourceB2002 + difference 1 3) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2002 + difference 3 1) (sourceB2002 + difference 1 3) sourceC2002) = raw28458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28458; decide +kernel
    rw [ha]
    exact (canonical28458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2002 + difference 4 1) (sourceB2002 + difference 1 4) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1819) := by
    have ha : (tripleCharges (sourceA2002 + difference 4 1) (sourceB2002 + difference 1 4) sourceC2002) = raw28459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28459; decide +kernel
    rw [ha]
    exact (canonical28459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2002 + difference 5 1) (sourceB2002 + difference 1 5) sourceC2002) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 939) := by
    have ha : (tripleCharges (sourceA2002 + difference 5 1) (sourceB2002 + difference 1 5) sourceC2002) = raw28460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2002 sourceB2002 sourceC2002 difference raw28460; decide +kernel
    rw [ha]
    exact (canonical28460 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2002 + sourceB2002) sourceC2002) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2002 + sourceB2002) sourceC2002) = raw28461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2002 sourceB2002 sourceC2002 raw28461; decide +kernel
    rw [ha]
    exact (canonical28461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2002 sourceB2002 sourceC2002
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2002, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2003 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2003 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2003 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceForm2003 : Integer.Sparse Master := [(Sum.inr 1315, 1), (Sum.inr 1961, 1), (Sum.inr 1970, 1), (Sum.inr 2062, 2), (Sum.inr 2879, 1), (Sum.inr 4084, -1)]

theorem sourceEq2003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2003 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 0) (sourceB2003 + difference 0 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1315) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 0) (sourceB2003 + difference 0 2) sourceC2003) = raw28462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28462; decide +kernel
    rw [ha]
    exact (canonical28462 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 1) (sourceB2003 + difference 1 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 1) (sourceB2003 + difference 1 2) sourceC2003) = raw28457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28457; decide +kernel
    rw [ha]
    exact (canonical28457 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 2) (sourceB2003 + difference 2 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 2) (sourceB2003 + difference 2 2) sourceC2003) = raw28456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28456; decide +kernel
    rw [ha]
    exact (canonical28456 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 3) (sourceB2003 + difference 3 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1961) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 3) (sourceB2003 + difference 3 2) sourceC2003) = raw28463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28463; decide +kernel
    rw [ha]
    exact (canonical28463 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 4) (sourceB2003 + difference 4 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 4) (sourceB2003 + difference 4 2) sourceC2003) = raw28464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28464; decide +kernel
    rw [ha]
    exact (canonical28464 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2003 + difference 2 5) (sourceB2003 + difference 5 2) sourceC2003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA2003 + difference 2 5) (sourceB2003 + difference 5 2) sourceC2003) = raw28465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2003 sourceB2003 sourceC2003 difference raw28465; decide +kernel
    rw [ha]
    exact (canonical28465 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2003 + sourceB2003) sourceC2003) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2003 + sourceB2003) sourceC2003) = raw28461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2003 sourceB2003 sourceC2003 raw28461; decide +kernel
    rw [ha]
    exact (canonical28461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2003 sourceB2003 sourceC2003
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2003, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2004 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceB2004 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2004 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2004 : Integer.Sparse Master := [(Sum.inr 4420, 2), (Sum.inr 4429, 1), (Sum.inr 4431, 1), (Sum.inr 4492, 1), (Sum.inr 4742, 2), (Sum.inr 4753, 1), (Sum.inr 4754, 1), (Sum.inr 4780, 2), (Sum.inr 4788, 2), (Sum.inr 4789, 2), (Sum.inr 4807, 2), (Sum.inr 4808, 2), (Sum.inr 4829, 2), (Sum.inr 4841, 1), (Sum.inr 4844, 1), (Sum.inr 4871, 2), (Sum.inr 4872, 1), (Sum.inr 5109, 1), (Sum.inr 5139, 2), (Sum.inr 5174, 1)]

theorem sourceEq2004 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2004 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2004 + difference 0 1) (sourceB2004 + difference 1 0) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2004 + difference 0 1) (sourceB2004 + difference 1 0) sourceC2004) = raw27642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27642; decide +kernel
    rw [ha]
    exact (canonical27642 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2004 + difference 0 2) (sourceB2004 + difference 2 0) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2004 + difference 0 2) (sourceB2004 + difference 2 0) sourceC2004) = raw28466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28466; decide +kernel
    rw [ha]
    exact (canonical28466 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2004 + difference 0 3) (sourceB2004 + difference 3 0) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2004 + difference 0 3) (sourceB2004 + difference 3 0) sourceC2004) = raw28467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28467; decide +kernel
    rw [ha]
    exact (canonical28467 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2004 + difference 0 4) (sourceB2004 + difference 4 0) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4753) := by
    have ha : (tripleCharges (sourceA2004 + difference 0 4) (sourceB2004 + difference 4 0) sourceC2004) = raw28468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28468; decide +kernel
    rw [ha]
    exact (canonical28468 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2004 + difference 0 5) (sourceB2004 + difference 5 0) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA2004 + difference 0 5) (sourceB2004 + difference 5 0) sourceC2004) = raw28469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28469; decide +kernel
    rw [ha]
    exact (canonical28469 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2004 + difference 1 0) (sourceB2004 + difference 0 1) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA2004 + difference 1 0) (sourceB2004 + difference 0 1) sourceC2004) = raw28470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28470; decide +kernel
    rw [ha]
    exact (canonical28470 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2004 + difference 1 2) (sourceB2004 + difference 2 1) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4789) := by
    have ha : (tripleCharges (sourceA2004 + difference 1 2) (sourceB2004 + difference 2 1) sourceC2004) = raw28471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28471; decide +kernel
    rw [ha]
    exact (canonical28471 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2004 + difference 1 3) (sourceB2004 + difference 3 1) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4789) := by
    have ha : (tripleCharges (sourceA2004 + difference 1 3) (sourceB2004 + difference 3 1) sourceC2004) = raw28472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28472; decide +kernel
    rw [ha]
    exact (canonical28472 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2004 + difference 1 4) (sourceB2004 + difference 4 1) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA2004 + difference 1 4) (sourceB2004 + difference 4 1) sourceC2004) = raw28473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28473; decide +kernel
    rw [ha]
    exact (canonical28473 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2004 + difference 1 5) (sourceB2004 + difference 5 1) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4429) := by
    have ha : (tripleCharges (sourceA2004 + difference 1 5) (sourceB2004 + difference 5 1) sourceC2004) = raw28474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28474; decide +kernel
    rw [ha]
    exact (canonical28474 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2004 + difference 2 0) (sourceB2004 + difference 0 2) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA2004 + difference 2 0) (sourceB2004 + difference 0 2) sourceC2004) = raw28475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28475; decide +kernel
    rw [ha]
    exact (canonical28475 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2004 + difference 2 1) (sourceB2004 + difference 1 2) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2004 + difference 2 1) (sourceB2004 + difference 1 2) sourceC2004) = raw27652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27652; decide +kernel
    rw [ha]
    exact (canonical27652 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2004 + difference 2 3) (sourceB2004 + difference 3 2) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4780) := by
    have ha : (tripleCharges (sourceA2004 + difference 2 3) (sourceB2004 + difference 3 2) sourceC2004) = raw28476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28476; decide +kernel
    rw [ha]
    exact (canonical28476 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2004 + difference 2 4) (sourceB2004 + difference 4 2) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2004 + difference 2 4) (sourceB2004 + difference 4 2) sourceC2004) = raw28477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28477; decide +kernel
    rw [ha]
    exact (canonical28477 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2004 + difference 2 5) (sourceB2004 + difference 5 2) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4420) := by
    have ha : (tripleCharges (sourceA2004 + difference 2 5) (sourceB2004 + difference 5 2) sourceC2004) = raw28478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28478; decide +kernel
    rw [ha]
    exact (canonical28478 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2004 + difference 3 0) (sourceB2004 + difference 0 3) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA2004 + difference 3 0) (sourceB2004 + difference 0 3) sourceC2004) = raw28128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28128; decide +kernel
    rw [ha]
    exact (canonical28128 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2004 + difference 3 1) (sourceB2004 + difference 1 3) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2004 + difference 3 1) (sourceB2004 + difference 1 3) sourceC2004) = raw27657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27657; decide +kernel
    rw [ha]
    exact (canonical27657 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2004 + difference 3 2) (sourceB2004 + difference 2 3) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4780) := by
    have ha : (tripleCharges (sourceA2004 + difference 3 2) (sourceB2004 + difference 2 3) sourceC2004) = raw28129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28129; decide +kernel
    rw [ha]
    exact (canonical28129 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2004 + difference 3 4) (sourceB2004 + difference 4 3) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2004 + difference 3 4) (sourceB2004 + difference 4 3) sourceC2004) = raw27958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27958; decide +kernel
    rw [ha]
    exact (canonical27958 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2004 + difference 3 5) (sourceB2004 + difference 5 3) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4420) := by
    have ha : (tripleCharges (sourceA2004 + difference 3 5) (sourceB2004 + difference 5 3) sourceC2004) = raw28130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw28130; decide +kernel
    rw [ha]
    exact (canonical28130 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2004 + difference 4 0) (sourceB2004 + difference 0 4) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4872) := by
    have ha : (tripleCharges (sourceA2004 + difference 4 0) (sourceB2004 + difference 0 4) sourceC2004) = raw27763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27763; decide +kernel
    rw [ha]
    exact (canonical27763 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2004 + difference 4 1) (sourceB2004 + difference 1 4) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2004 + difference 4 1) (sourceB2004 + difference 1 4) sourceC2004) = raw27662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27662; decide +kernel
    rw [ha]
    exact (canonical27662 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2004 + difference 4 2) (sourceB2004 + difference 2 4) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4829) := by
    have ha : (tripleCharges (sourceA2004 + difference 4 2) (sourceB2004 + difference 2 4) sourceC2004) = raw27764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27764; decide +kernel
    rw [ha]
    exact (canonical27764 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2004 + difference 4 3) (sourceB2004 + difference 3 4) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4829) := by
    have ha : (tripleCharges (sourceA2004 + difference 4 3) (sourceB2004 + difference 3 4) sourceC2004) = raw27765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27765; decide +kernel
    rw [ha]
    exact (canonical27765 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2004 + difference 4 5) (sourceB2004 + difference 5 4) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4492) := by
    have ha : (tripleCharges (sourceA2004 + difference 4 5) (sourceB2004 + difference 5 4) sourceC2004) = raw27766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27766; decide +kernel
    rw [ha]
    exact (canonical27766 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2004 + difference 5 0) (sourceB2004 + difference 0 5) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2004 + difference 5 0) (sourceB2004 + difference 0 5) sourceC2004) = raw27643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27643; decide +kernel
    rw [ha]
    exact (canonical27643 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2004 + difference 5 1) (sourceB2004 + difference 1 5) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2004 + difference 5 1) (sourceB2004 + difference 1 5) sourceC2004) = raw27780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27780; decide +kernel
    rw [ha]
    exact (canonical27780 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2004 + difference 5 2) (sourceB2004 + difference 2 5) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2004 + difference 5 2) (sourceB2004 + difference 2 5) sourceC2004) = raw27644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27644; decide +kernel
    rw [ha]
    exact (canonical27644 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2004 + difference 5 3) (sourceB2004 + difference 3 5) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2004 + difference 5 3) (sourceB2004 + difference 3 5) sourceC2004) = raw27645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27645; decide +kernel
    rw [ha]
    exact (canonical27645 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2004 + difference 5 4) (sourceB2004 + difference 4 5) sourceC2004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2004 + difference 5 4) (sourceB2004 + difference 4 5) sourceC2004) = raw27646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2004 sourceB2004 sourceC2004 difference raw27646; decide +kernel
    rw [ha]
    exact (canonical27646 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2004 sourceB2004 sourceC2004
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2004, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2005 : Charge := ![1, 2, 0, 1, -1, -3]
def sourceB2005 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC2005 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2005 : Integer.Sparse Master := [(Sum.inr 882, 1), (Sum.inr 1774, 1), (Sum.inr 1864, 1), (Sum.inr 1944, 1), (Sum.inr 1946, 1), (Sum.inr 1953, 1), (Sum.inr 4081, -1)]

theorem sourceEq2005 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2005 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2005 + difference 0 0) (sourceB2005 + difference 0 0) sourceC2005) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1946) := by
    have ha : (tripleCharges (sourceA2005 + difference 0 0) (sourceB2005 + difference 0 0) sourceC2005) = raw27413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2005 sourceB2005 sourceC2005 difference raw27413; decide +kernel
    rw [ha]
    exact (canonical27413 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2005 + difference 0 1) (sourceB2005 + difference 1 0) sourceC2005) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1944) := by
    have ha : (tripleCharges (sourceA2005 + difference 0 1) (sourceB2005 + difference 1 0) sourceC2005) = raw28187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2005 sourceB2005 sourceC2005 difference raw28187; decide +kernel
    rw [ha]
    exact (canonical28187 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2005 + difference 0 2) (sourceB2005 + difference 2 0) sourceC2005) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1864) := by
    have ha : (tripleCharges (sourceA2005 + difference 0 2) (sourceB2005 + difference 2 0) sourceC2005) = raw28479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2005 sourceB2005 sourceC2005 difference raw28479; decide +kernel
    rw [ha]
    exact (canonical28479 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2005 + difference 0 3) (sourceB2005 + difference 3 0) sourceC2005) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1953) := by
    have ha : (tripleCharges (sourceA2005 + difference 0 3) (sourceB2005 + difference 3 0) sourceC2005) = raw28480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2005 sourceB2005 sourceC2005 difference raw28480; decide +kernel
    rw [ha]
    exact (canonical28480 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2005 + difference 0 4) (sourceB2005 + difference 4 0) sourceC2005) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1774) := by
    have ha : (tripleCharges (sourceA2005 + difference 0 4) (sourceB2005 + difference 4 0) sourceC2005) = raw28481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2005 sourceB2005 sourceC2005 difference raw28481; decide +kernel
    rw [ha]
    exact (canonical28481 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2005 + difference 0 5) (sourceB2005 + difference 5 0) sourceC2005) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA2005 + difference 0 5) (sourceB2005 + difference 5 0) sourceC2005) = raw28482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2005 sourceB2005 sourceC2005 difference raw28482; decide +kernel
    rw [ha]
    exact (canonical28482 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2005 + sourceB2005) sourceC2005) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA2005 + sourceB2005) sourceC2005) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2005 sourceB2005 sourceC2005 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2005 sourceB2005 sourceC2005
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2005, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2006 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2006 : Charge := ![2, -2, 1, 0, 0, -1]
def sourceC2006 : Charge := ![1, 3, -1, 0, -1, -2]
def sourceForm2006 : Integer.Sparse Master := [(Sum.inr 2460, 1), (Sum.inr 2465, 1), (Sum.inr 2467, 1), (Sum.inr 2506, 1), (Sum.inr 2706, 1), (Sum.inr 3624, 1), (Sum.inr 4080, -1)]

theorem sourceEq2006 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2006 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2006 + difference 0 0) (sourceB2006 + difference 0 0) sourceC2006) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA2006 + difference 0 0) (sourceB2006 + difference 0 0) sourceC2006) = raw28483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2006 sourceB2006 sourceC2006 difference raw28483; decide +kernel
    rw [ha]
    exact (canonical28483 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2006 + difference 0 1) (sourceB2006 + difference 1 0) sourceC2006) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA2006 + difference 0 1) (sourceB2006 + difference 1 0) sourceC2006) = raw28484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2006 sourceB2006 sourceC2006 difference raw28484; decide +kernel
    rw [ha]
    exact (canonical28484 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2006 + difference 0 2) (sourceB2006 + difference 2 0) sourceC2006) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2506) := by
    have ha : (tripleCharges (sourceA2006 + difference 0 2) (sourceB2006 + difference 2 0) sourceC2006) = raw28485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2006 sourceB2006 sourceC2006 difference raw28485; decide +kernel
    rw [ha]
    exact (canonical28485 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2006 + difference 0 3) (sourceB2006 + difference 3 0) sourceC2006) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2460) := by
    have ha : (tripleCharges (sourceA2006 + difference 0 3) (sourceB2006 + difference 3 0) sourceC2006) = raw28486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2006 sourceB2006 sourceC2006 difference raw28486; decide +kernel
    rw [ha]
    exact (canonical28486 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2006 + difference 0 4) (sourceB2006 + difference 4 0) sourceC2006) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA2006 + difference 0 4) (sourceB2006 + difference 4 0) sourceC2006) = raw28487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2006 sourceB2006 sourceC2006 difference raw28487; decide +kernel
    rw [ha]
    exact (canonical28487 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2006 + difference 0 5) (sourceB2006 + difference 5 0) sourceC2006) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA2006 + difference 0 5) (sourceB2006 + difference 5 0) sourceC2006) = raw28488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2006 sourceB2006 sourceC2006 difference raw28488; decide +kernel
    rw [ha]
    exact (canonical28488 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2006 + sourceB2006) sourceC2006) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2006 + sourceB2006) sourceC2006) = raw28489 := by
      apply Matrix.ext; unfold doubleCharges sourceA2006 sourceB2006 sourceC2006 raw28489; decide +kernel
    rw [ha]
    exact (canonical28489 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2006 sourceB2006 sourceC2006
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2006, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2007 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2007 : Charge := ![2, -2, 1, 0, 0, -1]
def sourceC2007 : Charge := ![1, 3, -1, 0, -1, -2]
def sourceForm2007 : Integer.Sparse Master := [(Sum.inr 2254, 1), (Sum.inr 2465, 1), (Sum.inr 2833, 1), (Sum.inr 2835, 1), (Sum.inr 2840, 1), (Sum.inr 3624, 1), (Sum.inr 4080, -1)]

theorem sourceEq2007 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2007 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2007 + difference 0 5) (sourceB2007 + difference 5 0) sourceC2007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA2007 + difference 0 5) (sourceB2007 + difference 5 0) sourceC2007) = raw28488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2007 sourceB2007 sourceC2007 difference raw28488; decide +kernel
    rw [ha]
    exact (canonical28488 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2007 + difference 1 5) (sourceB2007 + difference 5 1) sourceC2007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA2007 + difference 1 5) (sourceB2007 + difference 5 1) sourceC2007) = raw28490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2007 sourceB2007 sourceC2007 difference raw28490; decide +kernel
    rw [ha]
    exact (canonical28490 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2007 + difference 2 5) (sourceB2007 + difference 5 2) sourceC2007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2840) := by
    have ha : (tripleCharges (sourceA2007 + difference 2 5) (sourceB2007 + difference 5 2) sourceC2007) = raw28491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2007 sourceB2007 sourceC2007 difference raw28491; decide +kernel
    rw [ha]
    exact (canonical28491 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2007 + difference 3 5) (sourceB2007 + difference 5 3) sourceC2007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA2007 + difference 3 5) (sourceB2007 + difference 5 3) sourceC2007) = raw28492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2007 sourceB2007 sourceC2007 difference raw28492; decide +kernel
    rw [ha]
    exact (canonical28492 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2007 + difference 4 5) (sourceB2007 + difference 5 4) sourceC2007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2835) := by
    have ha : (tripleCharges (sourceA2007 + difference 4 5) (sourceB2007 + difference 5 4) sourceC2007) = raw28493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2007 sourceB2007 sourceC2007 difference raw28493; decide +kernel
    rw [ha]
    exact (canonical28493 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2007 + difference 5 5) (sourceB2007 + difference 5 5) sourceC2007) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA2007 + difference 5 5) (sourceB2007 + difference 5 5) sourceC2007) = raw28483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2007 sourceB2007 sourceC2007 difference raw28483; decide +kernel
    rw [ha]
    exact (canonical28483 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2007 + sourceB2007) sourceC2007) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2007 + sourceB2007) sourceC2007) = raw28489 := by
      apply Matrix.ext; unfold doubleCharges sourceA2007 sourceB2007 sourceC2007 raw28489; decide +kernel
    rw [ha]
    exact (canonical28489 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2007 sourceB2007 sourceC2007
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2007, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2008 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2008 : Charge := ![1, 2, 0, 0, -3, 0]
def sourceC2008 : Charge := ![2, -1, 0, 0, 2, -3]
def sourceForm2008 : Integer.Sparse Master := [(Sum.inr 2128, 2), (Sum.inr 2130, 1), (Sum.inr 2137, 1), (Sum.inr 2276, 1), (Sum.inr 2687, 1), (Sum.inr 4082, -1)]

theorem sourceEq2008 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2008 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 0) (sourceB2008 + difference 0 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2130) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 0) (sourceB2008 + difference 0 0) sourceC2008) = raw20273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw20273; decide +kernel
    rw [ha]
    exact (canonical20273 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 1) (sourceB2008 + difference 1 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2137) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 1) (sourceB2008 + difference 1 0) sourceC2008) = raw28494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28494; decide +kernel
    rw [ha]
    exact (canonical28494 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 2) (sourceB2008 + difference 2 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 2) (sourceB2008 + difference 2 0) sourceC2008) = raw28495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28495; decide +kernel
    rw [ha]
    exact (canonical28495 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 3) (sourceB2008 + difference 3 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 3) (sourceB2008 + difference 3 0) sourceC2008) = raw28496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28496; decide +kernel
    rw [ha]
    exact (canonical28496 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 4) (sourceB2008 + difference 4 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 4) (sourceB2008 + difference 4 0) sourceC2008) = raw28497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28497; decide +kernel
    rw [ha]
    exact (canonical28497 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2008 + difference 0 5) (sourceB2008 + difference 5 0) sourceC2008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA2008 + difference 0 5) (sourceB2008 + difference 5 0) sourceC2008) = raw28498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2008 sourceB2008 sourceC2008 difference raw28498; decide +kernel
    rw [ha]
    exact (canonical28498 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2008 + sourceB2008) sourceC2008) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2008 + sourceB2008) sourceC2008) = raw19488 := by
      apply Matrix.ext; unfold doubleCharges sourceA2008 sourceB2008 sourceC2008 raw19488; decide +kernel
    rw [ha]
    exact (canonical19488 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2008 sourceB2008 sourceC2008
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2008, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2009 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2009 : Charge := ![1, 2, 0, -1, -2, 0]
def sourceC2009 : Charge := ![2, -1, 0, 1, 1, -3]
def sourceForm2009 : Integer.Sparse Master := [(Sum.inr 2085, 1), (Sum.inr 2087, 1), (Sum.inr 2093, 1), (Sum.inr 2101, 1), (Sum.inr 2242, 1), (Sum.inr 3570, 1), (Sum.inr 4080, -1)]

theorem sourceEq2009 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2009 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 0) (sourceB2009 + difference 0 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2087) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 0) (sourceB2009 + difference 0 0) sourceC2009) = raw20311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw20311; decide +kernel
    rw [ha]
    exact (canonical20311 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 1) (sourceB2009 + difference 1 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2093) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 1) (sourceB2009 + difference 1 0) sourceC2009) = raw28499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28499; decide +kernel
    rw [ha]
    exact (canonical28499 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 2) (sourceB2009 + difference 2 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2085) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 2) (sourceB2009 + difference 2 0) sourceC2009) = raw28500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28500; decide +kernel
    rw [ha]
    exact (canonical28500 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 3) (sourceB2009 + difference 3 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 3) (sourceB2009 + difference 3 0) sourceC2009) = raw28501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28501; decide +kernel
    rw [ha]
    exact (canonical28501 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 4) (sourceB2009 + difference 4 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 4) (sourceB2009 + difference 4 0) sourceC2009) = raw28502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28502; decide +kernel
    rw [ha]
    exact (canonical28502 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2009 + difference 0 5) (sourceB2009 + difference 5 0) sourceC2009) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA2009 + difference 0 5) (sourceB2009 + difference 5 0) sourceC2009) = raw28503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2009 sourceB2009 sourceC2009 difference raw28503; decide +kernel
    rw [ha]
    exact (canonical28503 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2009 + sourceB2009) sourceC2009) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2009 + sourceB2009) sourceC2009) = raw19499 := by
      apply Matrix.ext; unfold doubleCharges sourceA2009 sourceB2009 sourceC2009 raw19499; decide +kernel
    rw [ha]
    exact (canonical19499 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2009 sourceB2009 sourceC2009
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2009, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2010 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2010 : Charge := ![1, 2, 0, -2, 0, -1]
def sourceC2010 : Charge := ![2, -1, 0, 2, -1, -2]
def sourceForm2010 : Integer.Sparse Master := [(Sum.inr 2490, 1), (Sum.inr 2492, 1), (Sum.inr 2498, 1), (Sum.inr 2505, 1), (Sum.inr 2729, 1), (Sum.inr 3811, 1), (Sum.inr 4088, -1)]

theorem sourceEq2010 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2010 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2010 + difference 0 0) (sourceB2010 + difference 0 0) sourceC2010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2492) := by
    have ha : (tripleCharges (sourceA2010 + difference 0 0) (sourceB2010 + difference 0 0) sourceC2010) = raw20316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2010 sourceB2010 sourceC2010 difference raw20316; decide +kernel
    rw [ha]
    exact (canonical20316 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2010 + difference 0 1) (sourceB2010 + difference 1 0) sourceC2010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2498) := by
    have ha : (tripleCharges (sourceA2010 + difference 0 1) (sourceB2010 + difference 1 0) sourceC2010) = raw28504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2010 sourceB2010 sourceC2010 difference raw28504; decide +kernel
    rw [ha]
    exact (canonical28504 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2010 + difference 0 2) (sourceB2010 + difference 2 0) sourceC2010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2490) := by
    have ha : (tripleCharges (sourceA2010 + difference 0 2) (sourceB2010 + difference 2 0) sourceC2010) = raw28505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2010 sourceB2010 sourceC2010 difference raw28505; decide +kernel
    rw [ha]
    exact (canonical28505 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2010 + difference 0 3) (sourceB2010 + difference 3 0) sourceC2010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA2010 + difference 0 3) (sourceB2010 + difference 3 0) sourceC2010) = raw28506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2010 sourceB2010 sourceC2010 difference raw28506; decide +kernel
    rw [ha]
    exact (canonical28506 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2010 + difference 0 4) (sourceB2010 + difference 4 0) sourceC2010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA2010 + difference 0 4) (sourceB2010 + difference 4 0) sourceC2010) = raw28507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2010 sourceB2010 sourceC2010 difference raw28507; decide +kernel
    rw [ha]
    exact (canonical28507 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2010 + difference 0 5) (sourceB2010 + difference 5 0) sourceC2010) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2010 + difference 0 5) (sourceB2010 + difference 5 0) sourceC2010) = raw28508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2010 sourceB2010 sourceC2010 difference raw28508; decide +kernel
    rw [ha]
    exact (canonical28508 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2010 + sourceB2010) sourceC2010) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2010 + sourceB2010) sourceC2010) = raw20321 := by
      apply Matrix.ext; unfold doubleCharges sourceA2010 sourceB2010 sourceC2010 raw20321; decide +kernel
    rw [ha]
    exact (canonical20321 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2010 sourceB2010 sourceC2010
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2010, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2011 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2011 : Charge := ![1, 2, 0, -2, 0, -1]
def sourceC2011 : Charge := ![2, -1, 0, 2, -1, -2]
def sourceForm2011 : Integer.Sparse Master := [(Sum.inr 2492, 1), (Sum.inr 2606, 1), (Sum.inr 2608, 1), (Sum.inr 2629, 1), (Sum.inr 2672, 1), (Sum.inr 3811, 1), (Sum.inr 4088, -1)]

theorem sourceEq2011 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2011 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2011 + difference 0 5) (sourceB2011 + difference 5 0) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2011 + difference 0 5) (sourceB2011 + difference 5 0) sourceC2011) = raw28508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw28508; decide +kernel
    rw [ha]
    exact (canonical28508 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2011 + difference 1 5) (sourceB2011 + difference 5 1) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2011 + difference 1 5) (sourceB2011 + difference 5 1) sourceC2011) = raw20320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw20320; decide +kernel
    rw [ha]
    exact (canonical20320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2011 + difference 2 5) (sourceB2011 + difference 5 2) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2606) := by
    have ha : (tripleCharges (sourceA2011 + difference 2 5) (sourceB2011 + difference 5 2) sourceC2011) = raw28509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw28509; decide +kernel
    rw [ha]
    exact (canonical28509 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2011 + difference 3 5) (sourceB2011 + difference 5 3) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2629) := by
    have ha : (tripleCharges (sourceA2011 + difference 3 5) (sourceB2011 + difference 5 3) sourceC2011) = raw28510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw28510; decide +kernel
    rw [ha]
    exact (canonical28510 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2011 + difference 4 5) (sourceB2011 + difference 5 4) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2608) := by
    have ha : (tripleCharges (sourceA2011 + difference 4 5) (sourceB2011 + difference 5 4) sourceC2011) = raw28511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw28511; decide +kernel
    rw [ha]
    exact (canonical28511 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2011 + difference 5 5) (sourceB2011 + difference 5 5) sourceC2011) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2492) := by
    have ha : (tripleCharges (sourceA2011 + difference 5 5) (sourceB2011 + difference 5 5) sourceC2011) = raw20316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2011 sourceB2011 sourceC2011 difference raw20316; decide +kernel
    rw [ha]
    exact (canonical20316 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2011 + sourceB2011) sourceC2011) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2011 + sourceB2011) sourceC2011) = raw20321 := by
      apply Matrix.ext; unfold doubleCharges sourceA2011 sourceB2011 sourceC2011 raw20321; decide +kernel
    rw [ha]
    exact (canonical20321 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2011 sourceB2011 sourceC2011
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2011, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2012 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2012 : Charge := ![1, 2, 0, -2, -1, 0]
def sourceC2012 : Charge := ![2, -1, 0, 2, 0, -3]
def sourceForm2012 : Integer.Sparse Master := [(Sum.inr 2030, 1), (Sum.inr 2032, 1), (Sum.inr 2038, 1), (Sum.inr 2048, 1), (Sum.inr 2276, 1), (Sum.inr 3538, 1), (Sum.inr 4082, -1)]

theorem sourceEq2012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2012 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 0) (sourceB2012 + difference 0 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2032) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 0) (sourceB2012 + difference 0 0) sourceC2012) = raw20327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw20327; decide +kernel
    rw [ha]
    exact (canonical20327 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 1) (sourceB2012 + difference 1 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2038) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 1) (sourceB2012 + difference 1 0) sourceC2012) = raw28512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28512; decide +kernel
    rw [ha]
    exact (canonical28512 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 2) (sourceB2012 + difference 2 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2030) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 2) (sourceB2012 + difference 2 0) sourceC2012) = raw28513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28513; decide +kernel
    rw [ha]
    exact (canonical28513 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 3) (sourceB2012 + difference 3 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 3) (sourceB2012 + difference 3 0) sourceC2012) = raw28514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28514; decide +kernel
    rw [ha]
    exact (canonical28514 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 4) (sourceB2012 + difference 4 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 4) (sourceB2012 + difference 4 0) sourceC2012) = raw28515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28515; decide +kernel
    rw [ha]
    exact (canonical28515 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2012 + difference 0 5) (sourceB2012 + difference 5 0) sourceC2012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2012 + difference 0 5) (sourceB2012 + difference 5 0) sourceC2012) = raw28516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2012 sourceB2012 sourceC2012 difference raw28516; decide +kernel
    rw [ha]
    exact (canonical28516 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2012 + sourceB2012) sourceC2012) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2012 + sourceB2012) sourceC2012) = raw20332 := by
      apply Matrix.ext; unfold doubleCharges sourceA2012 sourceB2012 sourceC2012 raw20332; decide +kernel
    rw [ha]
    exact (canonical20332 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2012 sourceB2012 sourceC2012
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2012, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2013 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2013 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC2013 : Charge := ![2, -1, 1, 1, -1, -2]
def sourceForm2013 : Integer.Sparse Master := [(Sum.inr 2469, 1), (Sum.inr 2472, 1), (Sum.inr 2477, 2), (Sum.inr 2708, 1), (Sum.inr 3799, 1), (Sum.inr 4090, -1)]

theorem sourceEq2013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2013 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2013 + difference 0 0) (sourceB2013 + difference 0 0) sourceC2013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2469) := by
    have ha : (tripleCharges (sourceA2013 + difference 0 0) (sourceB2013 + difference 0 0) sourceC2013) = raw20334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2013 sourceB2013 sourceC2013 difference raw20334; decide +kernel
    rw [ha]
    exact (canonical20334 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2013 + difference 0 1) (sourceB2013 + difference 1 0) sourceC2013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2472) := by
    have ha : (tripleCharges (sourceA2013 + difference 0 1) (sourceB2013 + difference 1 0) sourceC2013) = raw28517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2013 sourceB2013 sourceC2013 difference raw28517; decide +kernel
    rw [ha]
    exact (canonical28517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2013 + difference 0 2) (sourceB2013 + difference 2 0) sourceC2013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA2013 + difference 0 2) (sourceB2013 + difference 2 0) sourceC2013) = raw28518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2013 sourceB2013 sourceC2013 difference raw28518; decide +kernel
    rw [ha]
    exact (canonical28518 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2013 + difference 0 3) (sourceB2013 + difference 3 0) sourceC2013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA2013 + difference 0 3) (sourceB2013 + difference 3 0) sourceC2013) = raw28519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2013 sourceB2013 sourceC2013 difference raw28519; decide +kernel
    rw [ha]
    exact (canonical28519 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2013 + difference 0 4) (sourceB2013 + difference 4 0) sourceC2013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA2013 + difference 0 4) (sourceB2013 + difference 4 0) sourceC2013) = raw28520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2013 sourceB2013 sourceC2013 difference raw28520; decide +kernel
    rw [ha]
    exact (canonical28520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2013 + difference 0 5) (sourceB2013 + difference 5 0) sourceC2013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2013 + difference 0 5) (sourceB2013 + difference 5 0) sourceC2013) = raw28521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2013 sourceB2013 sourceC2013 difference raw28521; decide +kernel
    rw [ha]
    exact (canonical28521 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2013 + sourceB2013) sourceC2013) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2013 + sourceB2013) sourceC2013) = raw20339 := by
      apply Matrix.ext; unfold doubleCharges sourceA2013 sourceB2013 sourceC2013 raw20339; decide +kernel
    rw [ha]
    exact (canonical20339 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2013 sourceB2013 sourceC2013
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2013, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2014 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2014 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC2014 : Charge := ![2, -1, 1, 1, -1, -2]
def sourceForm2014 : Integer.Sparse Master := [(Sum.inr 2469, 1), (Sum.inr 2609, 1), (Sum.inr 2613, 2), (Sum.inr 2694, 1), (Sum.inr 3799, 1), (Sum.inr 4090, -1)]

theorem sourceEq2014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2014 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2014 + difference 0 5) (sourceB2014 + difference 5 0) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2014 + difference 0 5) (sourceB2014 + difference 5 0) sourceC2014) = raw28521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw28521; decide +kernel
    rw [ha]
    exact (canonical28521 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2014 + difference 1 5) (sourceB2014 + difference 5 1) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2014 + difference 1 5) (sourceB2014 + difference 5 1) sourceC2014) = raw20338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw20338; decide +kernel
    rw [ha]
    exact (canonical20338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2014 + difference 2 5) (sourceB2014 + difference 5 2) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA2014 + difference 2 5) (sourceB2014 + difference 5 2) sourceC2014) = raw28522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw28522; decide +kernel
    rw [ha]
    exact (canonical28522 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2014 + difference 3 5) (sourceB2014 + difference 5 3) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA2014 + difference 3 5) (sourceB2014 + difference 5 3) sourceC2014) = raw28523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw28523; decide +kernel
    rw [ha]
    exact (canonical28523 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2014 + difference 4 5) (sourceB2014 + difference 5 4) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2609) := by
    have ha : (tripleCharges (sourceA2014 + difference 4 5) (sourceB2014 + difference 5 4) sourceC2014) = raw28524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw28524; decide +kernel
    rw [ha]
    exact (canonical28524 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2014 + difference 5 5) (sourceB2014 + difference 5 5) sourceC2014) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2469) := by
    have ha : (tripleCharges (sourceA2014 + difference 5 5) (sourceB2014 + difference 5 5) sourceC2014) = raw20334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2014 sourceB2014 sourceC2014 difference raw20334; decide +kernel
    rw [ha]
    exact (canonical20334 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2014 + sourceB2014) sourceC2014) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2014 + sourceB2014) sourceC2014) = raw20339 := by
      apply Matrix.ext; unfold doubleCharges sourceA2014 sourceB2014 sourceC2014 raw20339; decide +kernel
    rw [ha]
    exact (canonical20339 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2014 sourceB2014 sourceC2014
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2014, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2015 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2015 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC2015 : Charge := ![2, -1, 1, 1, 0, -3]
def sourceForm2015 : Integer.Sparse Master := [(Sum.inr 2008, 1), (Sum.inr 2011, 1), (Sum.inr 2016, 2), (Sum.inr 2242, 1), (Sum.inr 3524, 1), (Sum.inr 4080, -1)]

theorem sourceEq2015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2015 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 0) (sourceB2015 + difference 0 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2008) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 0) (sourceB2015 + difference 0 0) sourceC2015) = raw20345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw20345; decide +kernel
    rw [ha]
    exact (canonical20345 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 1) (sourceB2015 + difference 1 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2011) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 1) (sourceB2015 + difference 1 0) sourceC2015) = raw28525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28525; decide +kernel
    rw [ha]
    exact (canonical28525 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 2) (sourceB2015 + difference 2 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2016) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 2) (sourceB2015 + difference 2 0) sourceC2015) = raw28526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28526; decide +kernel
    rw [ha]
    exact (canonical28526 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 3) (sourceB2015 + difference 3 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2016) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 3) (sourceB2015 + difference 3 0) sourceC2015) = raw28527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28527; decide +kernel
    rw [ha]
    exact (canonical28527 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 4) (sourceB2015 + difference 4 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 4) (sourceB2015 + difference 4 0) sourceC2015) = raw28528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28528; decide +kernel
    rw [ha]
    exact (canonical28528 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2015 + difference 0 5) (sourceB2015 + difference 5 0) sourceC2015) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA2015 + difference 0 5) (sourceB2015 + difference 5 0) sourceC2015) = raw28529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2015 sourceB2015 sourceC2015 difference raw28529; decide +kernel
    rw [ha]
    exact (canonical28529 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2015 + sourceB2015) sourceC2015) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2015 + sourceB2015) sourceC2015) = raw20350 := by
      apply Matrix.ext; unfold doubleCharges sourceA2015 sourceB2015 sourceC2015 raw20350; decide +kernel
    rw [ha]
    exact (canonical20350 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2015 sourceB2015 sourceC2015
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2015, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
