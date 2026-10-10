import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical165
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical182

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1504 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1504 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC1504 : Charge := ![3, -2, 0, 1, -2, 0]
def sourceForm1504 : Integer.Sparse Master := [(Sum.inr 992, 1), (Sum.inr 1928, 1), (Sum.inr 1993, 1), (Sum.inr 2122, 1), (Sum.inr 2215, 1), (Sum.inr 2217, 1), (Sum.inr 4082, -1)]

theorem sourceEq1504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1504 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 0) (sourceB1504 + difference 0 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 992) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 0) (sourceB1504 + difference 0 0) sourceC1504) = raw22891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22891; decide +kernel
    rw [ha]
    exact (canonical22891 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 1) (sourceB1504 + difference 1 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2122) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 1) (sourceB1504 + difference 1 0) sourceC1504) = raw22892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22892; decide +kernel
    rw [ha]
    exact (canonical22892 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 2) (sourceB1504 + difference 2 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1993) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 2) (sourceB1504 + difference 2 0) sourceC1504) = raw22893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22893; decide +kernel
    rw [ha]
    exact (canonical22893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 3) (sourceB1504 + difference 3 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 3) (sourceB1504 + difference 3 0) sourceC1504) = raw22894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22894; decide +kernel
    rw [ha]
    exact (canonical22894 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 4) (sourceB1504 + difference 4 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 4) (sourceB1504 + difference 4 0) sourceC1504) = raw22895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22895; decide +kernel
    rw [ha]
    exact (canonical22895 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 5) (sourceB1504 + difference 5 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 5) (sourceB1504 + difference 5 0) sourceC1504) = raw22896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22896; decide +kernel
    rw [ha]
    exact (canonical22896 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1504 + sourceB1504) sourceC1504) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1504 + sourceB1504) sourceC1504) = raw22897 := by
      apply Matrix.ext; unfold doubleCharges sourceA1504 sourceB1504 sourceC1504 raw22897; decide +kernel
    rw [ha]
    exact (canonical22897 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1504 sourceB1504 sourceC1504
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1504, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1505 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1505 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC1505 : Charge := ![3, -2, 0, 1, -1, -1]
def sourceForm1505 : Integer.Sparse Master := [(Sum.inr 993, 1), (Sum.inr 1929, 1), (Sum.inr 1994, 1), (Sum.inr 2123, 1), (Sum.inr 2216, 2), (Sum.inr 4080, -1)]

theorem sourceEq1505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1505 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 0) (sourceB1505 + difference 0 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 993) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 0) (sourceB1505 + difference 0 0) sourceC1505) = raw21099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw21099; decide +kernel
    rw [ha]
    exact (canonical21099 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 1) (sourceB1505 + difference 1 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2123) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 1) (sourceB1505 + difference 1 0) sourceC1505) = raw22898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw22898; decide +kernel
    rw [ha]
    exact (canonical22898 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 2) (sourceB1505 + difference 2 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1994) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 2) (sourceB1505 + difference 2 0) sourceC1505) = raw22899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw22899; decide +kernel
    rw [ha]
    exact (canonical22899 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 3) (sourceB1505 + difference 3 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1929) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 3) (sourceB1505 + difference 3 0) sourceC1505) = raw22900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw22900; decide +kernel
    rw [ha]
    exact (canonical22900 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 4) (sourceB1505 + difference 4 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 4) (sourceB1505 + difference 4 0) sourceC1505) = raw21094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw21094; decide +kernel
    rw [ha]
    exact (canonical21094 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 5) (sourceB1505 + difference 5 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 5) (sourceB1505 + difference 5 0) sourceC1505) = raw22901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw22901; decide +kernel
    rw [ha]
    exact (canonical22901 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1505 + sourceB1505) sourceC1505) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1505 + sourceB1505) sourceC1505) = raw21095 := by
      apply Matrix.ext; unfold doubleCharges sourceA1505 sourceB1505 sourceC1505 raw21095; decide +kernel
    rw [ha]
    exact (canonical21095 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1505 sourceB1505 sourceC1505
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1505, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1506 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1506 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC1506 : Charge := ![3, -1, -1, 0, -2, 1]
def sourceForm1506 : Integer.Sparse Master := [(Sum.inr 1025, 1), (Sum.inr 2011, 1), (Sum.inr 2093, 2), (Sum.inr 2242, 1), (Sum.inr 2246, 1), (Sum.inr 4080, -1)]

theorem sourceEq1506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1506 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 0) (sourceB1506 + difference 0 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1025) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 0) (sourceB1506 + difference 0 0) sourceC1506) = raw22902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22902; decide +kernel
    rw [ha]
    exact (canonical22902 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 1) (sourceB1506 + difference 1 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2093) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 1) (sourceB1506 + difference 1 0) sourceC1506) = raw22903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22903; decide +kernel
    rw [ha]
    exact (canonical22903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 2) (sourceB1506 + difference 2 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2093) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 2) (sourceB1506 + difference 2 0) sourceC1506) = raw22904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22904; decide +kernel
    rw [ha]
    exact (canonical22904 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 3) (sourceB1506 + difference 3 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2011) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 3) (sourceB1506 + difference 3 0) sourceC1506) = raw22905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22905; decide +kernel
    rw [ha]
    exact (canonical22905 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 4) (sourceB1506 + difference 4 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 4) (sourceB1506 + difference 4 0) sourceC1506) = raw22906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22906; decide +kernel
    rw [ha]
    exact (canonical22906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 5) (sourceB1506 + difference 5 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 5) (sourceB1506 + difference 5 0) sourceC1506) = raw22907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22907; decide +kernel
    rw [ha]
    exact (canonical22907 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1506 + sourceB1506) sourceC1506) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1506 + sourceB1506) sourceC1506) = raw22908 := by
      apply Matrix.ext; unfold doubleCharges sourceA1506 sourceB1506 sourceC1506 raw22908; decide +kernel
    rw [ha]
    exact (canonical22908 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1506 sourceB1506 sourceC1506
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1506, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1507 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1507 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1507 : Charge := ![3, -1, -1, 1, -2, 0]
def sourceForm1507 : Integer.Sparse Master := [(Sum.inr 973, 1), (Sum.inr 1900, 1), (Sum.inr 2072, 2), (Sum.inr 2190, 1), (Sum.inr 2192, 1), (Sum.inr 4080, -1)]

theorem sourceEq1507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1507 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 0) (sourceB1507 + difference 0 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 973) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 0) (sourceB1507 + difference 0 0) sourceC1507) = raw22909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22909; decide +kernel
    rw [ha]
    exact (canonical22909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 1) (sourceB1507 + difference 1 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2072) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 1) (sourceB1507 + difference 1 0) sourceC1507) = raw22910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22910; decide +kernel
    rw [ha]
    exact (canonical22910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 2) (sourceB1507 + difference 2 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2072) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 2) (sourceB1507 + difference 2 0) sourceC1507) = raw22911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22911; decide +kernel
    rw [ha]
    exact (canonical22911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 3) (sourceB1507 + difference 3 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1900) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 3) (sourceB1507 + difference 3 0) sourceC1507) = raw22912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22912; decide +kernel
    rw [ha]
    exact (canonical22912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 4) (sourceB1507 + difference 4 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 4) (sourceB1507 + difference 4 0) sourceC1507) = raw22913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22913; decide +kernel
    rw [ha]
    exact (canonical22913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 5) (sourceB1507 + difference 5 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 5) (sourceB1507 + difference 5 0) sourceC1507) = raw22914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22914; decide +kernel
    rw [ha]
    exact (canonical22914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1507 + sourceB1507) sourceC1507) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1507 + sourceB1507) sourceC1507) = raw22915 := by
      apply Matrix.ext; unfold doubleCharges sourceA1507 sourceB1507 sourceC1507 raw22915; decide +kernel
    rw [ha]
    exact (canonical22915 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1507 sourceB1507 sourceC1507
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1507, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1508 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1508 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1508 : Charge := ![3, -1, -1, 1, -1, -1]
def sourceForm1508 : Integer.Sparse Master := [(Sum.inr 974, 1), (Sum.inr 1901, 1), (Sum.inr 2073, 2), (Sum.inr 2191, 2), (Sum.inr 4079, -1)]

theorem sourceEq1508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1508 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 0) (sourceB1508 + difference 0 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 974) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 0) (sourceB1508 + difference 0 0) sourceC1508) = raw21132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw21132; decide +kernel
    rw [ha]
    exact (canonical21132 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 1) (sourceB1508 + difference 1 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2073) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 1) (sourceB1508 + difference 1 0) sourceC1508) = raw22916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw22916; decide +kernel
    rw [ha]
    exact (canonical22916 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 2) (sourceB1508 + difference 2 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2073) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 2) (sourceB1508 + difference 2 0) sourceC1508) = raw22917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw22917; decide +kernel
    rw [ha]
    exact (canonical22917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 3) (sourceB1508 + difference 3 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1901) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 3) (sourceB1508 + difference 3 0) sourceC1508) = raw22918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw22918; decide +kernel
    rw [ha]
    exact (canonical22918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 4) (sourceB1508 + difference 4 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 4) (sourceB1508 + difference 4 0) sourceC1508) = raw21127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw21127; decide +kernel
    rw [ha]
    exact (canonical21127 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 5) (sourceB1508 + difference 5 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 5) (sourceB1508 + difference 5 0) sourceC1508) = raw22919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw22919; decide +kernel
    rw [ha]
    exact (canonical22919 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1508 + sourceB1508) sourceC1508) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1508 + sourceB1508) sourceC1508) = raw21128 := by
      apply Matrix.ext; unfold doubleCharges sourceA1508 sourceB1508 sourceC1508 raw21128; decide +kernel
    rw [ha]
    exact (canonical21128 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1508 sourceB1508 sourceC1508
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1508, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1509 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1509 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceC1509 : Charge := ![3, -1, 0, 0, -3, 1]
def sourceForm1509 : Integer.Sparse Master := [(Sum.inr 1048, 1), (Sum.inr 2027, 2), (Sum.inr 2114, 1), (Sum.inr 2261, 1), (Sum.inr 2267, 1), (Sum.inr 4081, -1)]

theorem sourceEq1509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1509 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 0) (sourceB1509 + difference 0 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1048) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 0) (sourceB1509 + difference 0 0) sourceC1509) = raw22920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22920; decide +kernel
    rw [ha]
    exact (canonical22920 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 1) (sourceB1509 + difference 1 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2114) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 1) (sourceB1509 + difference 1 0) sourceC1509) = raw22921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22921; decide +kernel
    rw [ha]
    exact (canonical22921 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 2) (sourceB1509 + difference 2 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2027) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 2) (sourceB1509 + difference 2 0) sourceC1509) = raw22922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22922; decide +kernel
    rw [ha]
    exact (canonical22922 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 3) (sourceB1509 + difference 3 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2027) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 3) (sourceB1509 + difference 3 0) sourceC1509) = raw22923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22923; decide +kernel
    rw [ha]
    exact (canonical22923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 4) (sourceB1509 + difference 4 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 4) (sourceB1509 + difference 4 0) sourceC1509) = raw22924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22924; decide +kernel
    rw [ha]
    exact (canonical22924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 5) (sourceB1509 + difference 5 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 5) (sourceB1509 + difference 5 0) sourceC1509) = raw22925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22925; decide +kernel
    rw [ha]
    exact (canonical22925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1509 + sourceB1509) sourceC1509) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1509 + sourceB1509) sourceC1509) = raw22926 := by
      apply Matrix.ext; unfold doubleCharges sourceA1509 sourceB1509 sourceC1509 raw22926; decide +kernel
    rw [ha]
    exact (canonical22926 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1509 sourceB1509 sourceC1509
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1509, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1510 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1510 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1510 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm1510 : Integer.Sparse Master := [(Sum.inr 4154, 2), (Sum.inr 4160, 1), (Sum.inr 4162, 1), (Sum.inr 4185, 1), (Sum.inr 4328, 2), (Sum.inr 4334, 2), (Sum.inr 4336, 2), (Sum.inr 4354, 2), (Sum.inr 4368, 2), (Sum.inr 4373, 1), (Sum.inr 4375, 1), (Sum.inr 4457, 2), (Sum.inr 4459, 2), (Sum.inr 4460, 1), (Sum.inr 4464, 1), (Sum.inr 4498, 1), (Sum.inr 4503, 1), (Sum.inr 4810, 2), (Sum.inr 4874, 1), (Sum.inr 4894, 1), (Sum.inr 4896, 1)]

theorem sourceEq1510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1510 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 1) (sourceB1510 + difference 1 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 1) (sourceB1510 + difference 1 0) sourceC1510) = raw22927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22927; decide +kernel
    rw [ha]
    exact (canonical22927 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 2) (sourceB1510 + difference 2 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 2) (sourceB1510 + difference 2 0) sourceC1510) = raw22928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22928; decide +kernel
    rw [ha]
    exact (canonical22928 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 3) (sourceB1510 + difference 3 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 3) (sourceB1510 + difference 3 0) sourceC1510) = raw22929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22929; decide +kernel
    rw [ha]
    exact (canonical22929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 4) (sourceB1510 + difference 4 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 4) (sourceB1510 + difference 4 0) sourceC1510) = raw22930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22930; decide +kernel
    rw [ha]
    exact (canonical22930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 5) (sourceB1510 + difference 5 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 5) (sourceB1510 + difference 5 0) sourceC1510) = raw22931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22931; decide +kernel
    rw [ha]
    exact (canonical22931 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 0) (sourceB1510 + difference 0 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 0) (sourceB1510 + difference 0 1) sourceC1510) = raw22932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22932; decide +kernel
    rw [ha]
    exact (canonical22932 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 2) (sourceB1510 + difference 2 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 2) (sourceB1510 + difference 2 1) sourceC1510) = raw22933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22933; decide +kernel
    rw [ha]
    exact (canonical22933 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 3) (sourceB1510 + difference 3 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 3) (sourceB1510 + difference 3 1) sourceC1510) = raw22934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22934; decide +kernel
    rw [ha]
    exact (canonical22934 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 4) (sourceB1510 + difference 4 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 4) (sourceB1510 + difference 4 1) sourceC1510) = raw22935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22935; decide +kernel
    rw [ha]
    exact (canonical22935 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 5) (sourceB1510 + difference 5 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 5) (sourceB1510 + difference 5 1) sourceC1510) = raw22936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22936; decide +kernel
    rw [ha]
    exact (canonical22936 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 0) (sourceB1510 + difference 0 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4154) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 0) (sourceB1510 + difference 0 2) sourceC1510) = raw22937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22937; decide +kernel
    rw [ha]
    exact (canonical22937 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 1) (sourceB1510 + difference 1 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 1) (sourceB1510 + difference 1 2) sourceC1510) = raw22938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22938; decide +kernel
    rw [ha]
    exact (canonical22938 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 3) (sourceB1510 + difference 3 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 3) (sourceB1510 + difference 3 2) sourceC1510) = raw22939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22939; decide +kernel
    rw [ha]
    exact (canonical22939 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 4) (sourceB1510 + difference 4 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 4) (sourceB1510 + difference 4 2) sourceC1510) = raw22940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22940; decide +kernel
    rw [ha]
    exact (canonical22940 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 5) (sourceB1510 + difference 5 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 5) (sourceB1510 + difference 5 2) sourceC1510) = raw22941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22941; decide +kernel
    rw [ha]
    exact (canonical22941 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 0) (sourceB1510 + difference 0 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4154) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 0) (sourceB1510 + difference 0 3) sourceC1510) = raw22942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22942; decide +kernel
    rw [ha]
    exact (canonical22942 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 1) (sourceB1510 + difference 1 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 1) (sourceB1510 + difference 1 3) sourceC1510) = raw22943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22943; decide +kernel
    rw [ha]
    exact (canonical22943 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 2) (sourceB1510 + difference 2 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 2) (sourceB1510 + difference 2 3) sourceC1510) = raw22944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22944; decide +kernel
    rw [ha]
    exact (canonical22944 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 4) (sourceB1510 + difference 4 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 4) (sourceB1510 + difference 4 3) sourceC1510) = raw22945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22945; decide +kernel
    rw [ha]
    exact (canonical22945 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 5) (sourceB1510 + difference 5 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 5) (sourceB1510 + difference 5 3) sourceC1510) = raw22946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22946; decide +kernel
    rw [ha]
    exact (canonical22946 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 0) (sourceB1510 + difference 0 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4160) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 0) (sourceB1510 + difference 0 4) sourceC1510) = raw22947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22947; decide +kernel
    rw [ha]
    exact (canonical22947 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 1) (sourceB1510 + difference 1 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4373) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 1) (sourceB1510 + difference 1 4) sourceC1510) = raw22948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22948; decide +kernel
    rw [ha]
    exact (canonical22948 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 2) (sourceB1510 + difference 2 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 2) (sourceB1510 + difference 2 4) sourceC1510) = raw22949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22949; decide +kernel
    rw [ha]
    exact (canonical22949 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 3) (sourceB1510 + difference 3 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 3) (sourceB1510 + difference 3 4) sourceC1510) = raw22950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22950; decide +kernel
    rw [ha]
    exact (canonical22950 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 5) (sourceB1510 + difference 5 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 5) (sourceB1510 + difference 5 4) sourceC1510) = raw22951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22951; decide +kernel
    rw [ha]
    exact (canonical22951 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 0) (sourceB1510 + difference 0 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4162) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 0) (sourceB1510 + difference 0 5) sourceC1510) = raw22952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22952; decide +kernel
    rw [ha]
    exact (canonical22952 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 1) (sourceB1510 + difference 1 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4375) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 1) (sourceB1510 + difference 1 5) sourceC1510) = raw22953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22953; decide +kernel
    rw [ha]
    exact (canonical22953 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 2) (sourceB1510 + difference 2 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4336) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 2) (sourceB1510 + difference 2 5) sourceC1510) = raw22954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22954; decide +kernel
    rw [ha]
    exact (canonical22954 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 3) (sourceB1510 + difference 3 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4336) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 3) (sourceB1510 + difference 3 5) sourceC1510) = raw22955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22955; decide +kernel
    rw [ha]
    exact (canonical22955 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 4) (sourceB1510 + difference 4 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 4) (sourceB1510 + difference 4 5) sourceC1510) = raw22956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22956; decide +kernel
    rw [ha]
    exact (canonical22956 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1510 sourceB1510 sourceC1510
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1510, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1511 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1511 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1511 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm1511 : Integer.Sparse Master := [(Sum.inr 631, 2), (Sum.inr 634, 1), (Sum.inr 636, 1), (Sum.inr 648, 1), (Sum.inr 1321, 2), (Sum.inr 1323, 1), (Sum.inr 1325, 1), (Sum.inr 1330, 2), (Sum.inr 1332, 2), (Sum.inr 1334, 2), (Sum.inr 1343, 2), (Sum.inr 1406, 2), (Sum.inr 1408, 1), (Sum.inr 1414, 2), (Sum.inr 1416, 1), (Sum.inr 1442, 1), (Sum.inr 1448, 1), (Sum.inr 3187, 1), (Sum.inr 3206, 2), (Sum.inr 3225, 1), (Sum.inr 3230, 1)]

theorem sourceEq1511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1511 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1511 + difference 0 1) (sourceB1511 + difference 1 0) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA1511 + difference 0 1) (sourceB1511 + difference 1 0) sourceC1511) = raw22957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22957; decide +kernel
    rw [ha]
    exact (canonical22957 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1511 + difference 0 2) (sourceB1511 + difference 2 0) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA1511 + difference 0 2) (sourceB1511 + difference 2 0) sourceC1511) = raw22958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22958; decide +kernel
    rw [ha]
    exact (canonical22958 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1511 + difference 0 3) (sourceB1511 + difference 3 0) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA1511 + difference 0 3) (sourceB1511 + difference 3 0) sourceC1511) = raw22959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22959; decide +kernel
    rw [ha]
    exact (canonical22959 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1511 + difference 0 4) (sourceB1511 + difference 4 0) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA1511 + difference 0 4) (sourceB1511 + difference 4 0) sourceC1511) = raw22960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22960; decide +kernel
    rw [ha]
    exact (canonical22960 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1511 + difference 0 5) (sourceB1511 + difference 5 0) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA1511 + difference 0 5) (sourceB1511 + difference 5 0) sourceC1511) = raw22961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22961; decide +kernel
    rw [ha]
    exact (canonical22961 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1511 + difference 1 0) (sourceB1511 + difference 0 1) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 648) := by
    have ha : (tripleCharges (sourceA1511 + difference 1 0) (sourceB1511 + difference 0 1) sourceC1511) = raw22962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22962; decide +kernel
    rw [ha]
    exact (canonical22962 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1511 + difference 1 2) (sourceB1511 + difference 2 1) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1343) := by
    have ha : (tripleCharges (sourceA1511 + difference 1 2) (sourceB1511 + difference 2 1) sourceC1511) = raw22963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22963; decide +kernel
    rw [ha]
    exact (canonical22963 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1511 + difference 1 3) (sourceB1511 + difference 3 1) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1343) := by
    have ha : (tripleCharges (sourceA1511 + difference 1 3) (sourceB1511 + difference 3 1) sourceC1511) = raw22964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22964; decide +kernel
    rw [ha]
    exact (canonical22964 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1511 + difference 1 4) (sourceB1511 + difference 4 1) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1442) := by
    have ha : (tripleCharges (sourceA1511 + difference 1 4) (sourceB1511 + difference 4 1) sourceC1511) = raw22965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22965; decide +kernel
    rw [ha]
    exact (canonical22965 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1511 + difference 1 5) (sourceB1511 + difference 5 1) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1511 + difference 1 5) (sourceB1511 + difference 5 1) sourceC1511) = raw22966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22966; decide +kernel
    rw [ha]
    exact (canonical22966 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1511 + difference 2 0) (sourceB1511 + difference 0 2) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 631) := by
    have ha : (tripleCharges (sourceA1511 + difference 2 0) (sourceB1511 + difference 0 2) sourceC1511) = raw22967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22967; decide +kernel
    rw [ha]
    exact (canonical22967 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1511 + difference 2 1) (sourceB1511 + difference 1 2) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA1511 + difference 2 1) (sourceB1511 + difference 1 2) sourceC1511) = raw22968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22968; decide +kernel
    rw [ha]
    exact (canonical22968 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1511 + difference 2 3) (sourceB1511 + difference 3 2) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA1511 + difference 2 3) (sourceB1511 + difference 3 2) sourceC1511) = raw22969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22969; decide +kernel
    rw [ha]
    exact (canonical22969 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1511 + difference 2 4) (sourceB1511 + difference 4 2) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA1511 + difference 2 4) (sourceB1511 + difference 4 2) sourceC1511) = raw22970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22970; decide +kernel
    rw [ha]
    exact (canonical22970 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1511 + difference 2 5) (sourceB1511 + difference 5 2) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1511 + difference 2 5) (sourceB1511 + difference 5 2) sourceC1511) = raw22971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22971; decide +kernel
    rw [ha]
    exact (canonical22971 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1511 + difference 3 0) (sourceB1511 + difference 0 3) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 631) := by
    have ha : (tripleCharges (sourceA1511 + difference 3 0) (sourceB1511 + difference 0 3) sourceC1511) = raw22972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22972; decide +kernel
    rw [ha]
    exact (canonical22972 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1511 + difference 3 1) (sourceB1511 + difference 1 3) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA1511 + difference 3 1) (sourceB1511 + difference 1 3) sourceC1511) = raw22973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22973; decide +kernel
    rw [ha]
    exact (canonical22973 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1511 + difference 3 2) (sourceB1511 + difference 2 3) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA1511 + difference 3 2) (sourceB1511 + difference 2 3) sourceC1511) = raw22974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22974; decide +kernel
    rw [ha]
    exact (canonical22974 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1511 + difference 3 4) (sourceB1511 + difference 4 3) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA1511 + difference 3 4) (sourceB1511 + difference 4 3) sourceC1511) = raw22975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22975; decide +kernel
    rw [ha]
    exact (canonical22975 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1511 + difference 3 5) (sourceB1511 + difference 5 3) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1511 + difference 3 5) (sourceB1511 + difference 5 3) sourceC1511) = raw22976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22976; decide +kernel
    rw [ha]
    exact (canonical22976 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1511 + difference 4 0) (sourceB1511 + difference 0 4) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 636) := by
    have ha : (tripleCharges (sourceA1511 + difference 4 0) (sourceB1511 + difference 0 4) sourceC1511) = raw22977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22977; decide +kernel
    rw [ha]
    exact (canonical22977 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1511 + difference 4 1) (sourceB1511 + difference 1 4) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1325) := by
    have ha : (tripleCharges (sourceA1511 + difference 4 1) (sourceB1511 + difference 1 4) sourceC1511) = raw22978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22978; decide +kernel
    rw [ha]
    exact (canonical22978 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1511 + difference 4 2) (sourceB1511 + difference 2 4) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA1511 + difference 4 2) (sourceB1511 + difference 2 4) sourceC1511) = raw22979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22979; decide +kernel
    rw [ha]
    exact (canonical22979 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1511 + difference 4 3) (sourceB1511 + difference 3 4) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA1511 + difference 4 3) (sourceB1511 + difference 3 4) sourceC1511) = raw22980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22980; decide +kernel
    rw [ha]
    exact (canonical22980 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1511 + difference 4 5) (sourceB1511 + difference 5 4) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1511 + difference 4 5) (sourceB1511 + difference 5 4) sourceC1511) = raw22981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22981; decide +kernel
    rw [ha]
    exact (canonical22981 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1511 + difference 5 0) (sourceB1511 + difference 0 5) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 634) := by
    have ha : (tripleCharges (sourceA1511 + difference 5 0) (sourceB1511 + difference 0 5) sourceC1511) = raw22982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22982; decide +kernel
    rw [ha]
    exact (canonical22982 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1511 + difference 5 1) (sourceB1511 + difference 1 5) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1323) := by
    have ha : (tripleCharges (sourceA1511 + difference 5 1) (sourceB1511 + difference 1 5) sourceC1511) = raw22983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22983; decide +kernel
    rw [ha]
    exact (canonical22983 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1511 + difference 5 2) (sourceB1511 + difference 2 5) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1332) := by
    have ha : (tripleCharges (sourceA1511 + difference 5 2) (sourceB1511 + difference 2 5) sourceC1511) = raw22984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22984; decide +kernel
    rw [ha]
    exact (canonical22984 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1511 + difference 5 3) (sourceB1511 + difference 3 5) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1332) := by
    have ha : (tripleCharges (sourceA1511 + difference 5 3) (sourceB1511 + difference 3 5) sourceC1511) = raw22985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22985; decide +kernel
    rw [ha]
    exact (canonical22985 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1511 + difference 5 4) (sourceB1511 + difference 4 5) sourceC1511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA1511 + difference 5 4) (sourceB1511 + difference 4 5) sourceC1511) = raw22986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1511 sourceB1511 sourceC1511 difference raw22986; decide +kernel
    rw [ha]
    exact (canonical22986 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1511 sourceB1511 sourceC1511
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1511, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1512 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1512 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1512 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm1512 : Integer.Sparse Master := [(Sum.inr 1511, 2), (Sum.inr 1523, 1), (Sum.inr 1525, 1), (Sum.inr 1529, 1), (Sum.inr 1667, 2), (Sum.inr 1679, 2), (Sum.inr 1681, 2), (Sum.inr 1685, 2), (Sum.inr 1707, 2), (Sum.inr 1712, 2), (Sum.inr 1714, 2), (Sum.inr 1725, 1), (Sum.inr 1727, 1), (Sum.inr 1735, 1), (Sum.inr 1739, 1), (Sum.inr 1743, 1), (Sum.inr 1745, 1), (Sum.inr 2215, 2), (Sum.inr 2264, 1), (Sum.inr 2276, 1), (Sum.inr 2278, 1)]

theorem sourceEq1512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1512 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 1) (sourceB1512 + difference 1 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 1) (sourceB1512 + difference 1 0) sourceC1512) = raw22987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22987; decide +kernel
    rw [ha]
    exact (canonical22987 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 2) (sourceB1512 + difference 2 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 2) (sourceB1512 + difference 2 0) sourceC1512) = raw22988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22988; decide +kernel
    rw [ha]
    exact (canonical22988 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 3) (sourceB1512 + difference 3 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 3) (sourceB1512 + difference 3 0) sourceC1512) = raw22989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22989; decide +kernel
    rw [ha]
    exact (canonical22989 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 4) (sourceB1512 + difference 4 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 4) (sourceB1512 + difference 4 0) sourceC1512) = raw22990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22990; decide +kernel
    rw [ha]
    exact (canonical22990 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 5) (sourceB1512 + difference 5 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 5) (sourceB1512 + difference 5 0) sourceC1512) = raw22991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22991; decide +kernel
    rw [ha]
    exact (canonical22991 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 0) (sourceB1512 + difference 0 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 0) (sourceB1512 + difference 0 1) sourceC1512) = raw22992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22992; decide +kernel
    rw [ha]
    exact (canonical22992 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 2) (sourceB1512 + difference 2 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 2) (sourceB1512 + difference 2 1) sourceC1512) = raw22993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22993; decide +kernel
    rw [ha]
    exact (canonical22993 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 3) (sourceB1512 + difference 3 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 3) (sourceB1512 + difference 3 1) sourceC1512) = raw22994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22994; decide +kernel
    rw [ha]
    exact (canonical22994 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 4) (sourceB1512 + difference 4 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 4) (sourceB1512 + difference 4 1) sourceC1512) = raw22995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22995; decide +kernel
    rw [ha]
    exact (canonical22995 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 5) (sourceB1512 + difference 5 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 5) (sourceB1512 + difference 5 1) sourceC1512) = raw22996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22996; decide +kernel
    rw [ha]
    exact (canonical22996 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 0) (sourceB1512 + difference 0 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 0) (sourceB1512 + difference 0 2) sourceC1512) = raw22997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22997; decide +kernel
    rw [ha]
    exact (canonical22997 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 1) (sourceB1512 + difference 1 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 1) (sourceB1512 + difference 1 2) sourceC1512) = raw22998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22998; decide +kernel
    rw [ha]
    exact (canonical22998 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 3) (sourceB1512 + difference 3 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 3) (sourceB1512 + difference 3 2) sourceC1512) = raw22999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22999; decide +kernel
    rw [ha]
    exact (canonical22999 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 4) (sourceB1512 + difference 4 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 4) (sourceB1512 + difference 4 2) sourceC1512) = raw23000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23000; decide +kernel
    rw [ha]
    exact (canonical23000 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 5) (sourceB1512 + difference 5 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 5) (sourceB1512 + difference 5 2) sourceC1512) = raw23001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23001; decide +kernel
    rw [ha]
    exact (canonical23001 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 0) (sourceB1512 + difference 0 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 0) (sourceB1512 + difference 0 3) sourceC1512) = raw23002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23002; decide +kernel
    rw [ha]
    exact (canonical23002 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 1) (sourceB1512 + difference 1 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 1) (sourceB1512 + difference 1 3) sourceC1512) = raw23003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23003; decide +kernel
    rw [ha]
    exact (canonical23003 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 2) (sourceB1512 + difference 2 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 2) (sourceB1512 + difference 2 3) sourceC1512) = raw23004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23004; decide +kernel
    rw [ha]
    exact (canonical23004 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 4) (sourceB1512 + difference 4 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 4) (sourceB1512 + difference 4 3) sourceC1512) = raw23005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23005; decide +kernel
    rw [ha]
    exact (canonical23005 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 5) (sourceB1512 + difference 5 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 5) (sourceB1512 + difference 5 3) sourceC1512) = raw23006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23006; decide +kernel
    rw [ha]
    exact (canonical23006 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 0) (sourceB1512 + difference 0 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 0) (sourceB1512 + difference 0 4) sourceC1512) = raw23007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23007; decide +kernel
    rw [ha]
    exact (canonical23007 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 1) (sourceB1512 + difference 1 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 1) (sourceB1512 + difference 1 4) sourceC1512) = raw23008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23008; decide +kernel
    rw [ha]
    exact (canonical23008 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 2) (sourceB1512 + difference 2 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 2) (sourceB1512 + difference 2 4) sourceC1512) = raw23009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23009; decide +kernel
    rw [ha]
    exact (canonical23009 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 3) (sourceB1512 + difference 3 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 3) (sourceB1512 + difference 3 4) sourceC1512) = raw23010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23010; decide +kernel
    rw [ha]
    exact (canonical23010 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 5) (sourceB1512 + difference 5 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 5) (sourceB1512 + difference 5 4) sourceC1512) = raw23011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23011; decide +kernel
    rw [ha]
    exact (canonical23011 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 0) (sourceB1512 + difference 0 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 0) (sourceB1512 + difference 0 5) sourceC1512) = raw23012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23012; decide +kernel
    rw [ha]
    exact (canonical23012 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 1) (sourceB1512 + difference 1 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1743) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 1) (sourceB1512 + difference 1 5) sourceC1512) = raw23013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23013; decide +kernel
    rw [ha]
    exact (canonical23013 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 2) (sourceB1512 + difference 2 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 2) (sourceB1512 + difference 2 5) sourceC1512) = raw23014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23014; decide +kernel
    rw [ha]
    exact (canonical23014 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 3) (sourceB1512 + difference 3 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 3) (sourceB1512 + difference 3 5) sourceC1512) = raw23015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23015; decide +kernel
    rw [ha]
    exact (canonical23015 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 4) (sourceB1512 + difference 4 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 4) (sourceB1512 + difference 4 5) sourceC1512) = raw23016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23016; decide +kernel
    rw [ha]
    exact (canonical23016 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1512 sourceB1512 sourceC1512
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1512, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1513 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1513 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1513 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm1513 : Integer.Sparse Master := [(Sum.inr 582, 2), (Sum.inr 588, 1), (Sum.inr 590, 1), (Sum.inr 613, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

theorem sourceEq1513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1513 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1513 + difference 0 0) (sourceB1513 + difference 0 0) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1513 + difference 0 0) (sourceB1513 + difference 0 0) sourceC1513) = raw23017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23017; decide +kernel
    rw [ha]
    exact (canonical23017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1513 + difference 1 0) (sourceB1513 + difference 0 1) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1513 + difference 1 0) (sourceB1513 + difference 0 1) sourceC1513) = raw23018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23018; decide +kernel
    rw [ha]
    exact (canonical23018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1513 + difference 2 0) (sourceB1513 + difference 0 2) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1513 + difference 2 0) (sourceB1513 + difference 0 2) sourceC1513) = raw23019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23019; decide +kernel
    rw [ha]
    exact (canonical23019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1513 + difference 3 0) (sourceB1513 + difference 0 3) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1513 + difference 3 0) (sourceB1513 + difference 0 3) sourceC1513) = raw23020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23020; decide +kernel
    rw [ha]
    exact (canonical23020 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1513 + difference 4 0) (sourceB1513 + difference 0 4) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 588) := by
    have ha : (tripleCharges (sourceA1513 + difference 4 0) (sourceB1513 + difference 0 4) sourceC1513) = raw23021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23021; decide +kernel
    rw [ha]
    exact (canonical23021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1513 + difference 5 0) (sourceB1513 + difference 0 5) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 590) := by
    have ha : (tripleCharges (sourceA1513 + difference 5 0) (sourceB1513 + difference 0 5) sourceC1513) = raw23022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23022; decide +kernel
    rw [ha]
    exact (canonical23022 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1513 + sourceB1513) sourceC1513) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1513 + sourceB1513) sourceC1513) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1513 sourceB1513 sourceC1513 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1513 sourceB1513 sourceC1513
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1513, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1514 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1514 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1514 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm1514 : Integer.Sparse Master := [(Sum.inr 613, 1), (Sum.inr 932, 2), (Sum.inr 1049, 1), (Sum.inr 1082, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

theorem sourceEq1514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1514 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 0) (sourceB1514 + difference 0 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 0) (sourceB1514 + difference 0 1) sourceC1514) = raw23018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23018; decide +kernel
    rw [ha]
    exact (canonical23018 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 1) (sourceB1514 + difference 1 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 1) (sourceB1514 + difference 1 1) sourceC1514) = raw23017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23017; decide +kernel
    rw [ha]
    exact (canonical23017 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 2) (sourceB1514 + difference 2 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 2) (sourceB1514 + difference 2 1) sourceC1514) = raw23024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23024; decide +kernel
    rw [ha]
    exact (canonical23024 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 3) (sourceB1514 + difference 3 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 3) (sourceB1514 + difference 3 1) sourceC1514) = raw23025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23025; decide +kernel
    rw [ha]
    exact (canonical23025 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 4) (sourceB1514 + difference 4 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 4) (sourceB1514 + difference 4 1) sourceC1514) = raw23026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23026; decide +kernel
    rw [ha]
    exact (canonical23026 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 5) (sourceB1514 + difference 5 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 5) (sourceB1514 + difference 5 1) sourceC1514) = raw23027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23027; decide +kernel
    rw [ha]
    exact (canonical23027 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1514 + sourceB1514) sourceC1514) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1514 + sourceB1514) sourceC1514) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1514 sourceB1514 sourceC1514 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1514 sourceB1514 sourceC1514
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1514, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1515 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1515 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1515 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm1515 : Integer.Sparse Master := [(Sum.inr 946, 2), (Sum.inr 952, 1), (Sum.inr 954, 1), (Sum.inr 1049, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

theorem sourceEq1515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1515 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1515 + difference 0 1) (sourceB1515 + difference 1 0) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA1515 + difference 0 1) (sourceB1515 + difference 1 0) sourceC1515) = raw23028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23028; decide +kernel
    rw [ha]
    exact (canonical23028 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1515 + difference 1 1) (sourceB1515 + difference 1 1) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1515 + difference 1 1) (sourceB1515 + difference 1 1) sourceC1515) = raw23017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23017; decide +kernel
    rw [ha]
    exact (canonical23017 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1515 + difference 2 1) (sourceB1515 + difference 1 2) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1515 + difference 2 1) (sourceB1515 + difference 1 2) sourceC1515) = raw23029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23029; decide +kernel
    rw [ha]
    exact (canonical23029 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1515 + difference 3 1) (sourceB1515 + difference 1 3) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1515 + difference 3 1) (sourceB1515 + difference 1 3) sourceC1515) = raw23030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23030; decide +kernel
    rw [ha]
    exact (canonical23030 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1515 + difference 4 1) (sourceB1515 + difference 1 4) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 952) := by
    have ha : (tripleCharges (sourceA1515 + difference 4 1) (sourceB1515 + difference 1 4) sourceC1515) = raw23031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23031; decide +kernel
    rw [ha]
    exact (canonical23031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1515 + difference 5 1) (sourceB1515 + difference 1 5) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 954) := by
    have ha : (tripleCharges (sourceA1515 + difference 5 1) (sourceB1515 + difference 1 5) sourceC1515) = raw23032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23032; decide +kernel
    rw [ha]
    exact (canonical23032 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1515 + sourceB1515) sourceC1515) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1515 + sourceB1515) sourceC1515) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1515 sourceB1515 sourceC1515 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1515 sourceB1515 sourceC1515
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1515, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1516 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1516 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1516 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm1516 : Integer.Sparse Master := [(Sum.inr 582, 1), (Sum.inr 906, 1), (Sum.inr 946, 1), (Sum.inr 1040, 1), (Sum.inr 1042, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

theorem sourceEq1516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1516 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 0) (sourceB1516 + difference 0 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 0) (sourceB1516 + difference 0 2) sourceC1516) = raw23019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23019; decide +kernel
    rw [ha]
    exact (canonical23019 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 1) (sourceB1516 + difference 1 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 1) (sourceB1516 + difference 1 2) sourceC1516) = raw23029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23029; decide +kernel
    rw [ha]
    exact (canonical23029 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 2) (sourceB1516 + difference 2 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 2) (sourceB1516 + difference 2 2) sourceC1516) = raw23017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23017; decide +kernel
    rw [ha]
    exact (canonical23017 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 3) (sourceB1516 + difference 3 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 906) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 3) (sourceB1516 + difference 3 2) sourceC1516) = raw23033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23033; decide +kernel
    rw [ha]
    exact (canonical23033 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 4) (sourceB1516 + difference 4 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 4) (sourceB1516 + difference 4 2) sourceC1516) = raw23034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23034; decide +kernel
    rw [ha]
    exact (canonical23034 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 5) (sourceB1516 + difference 5 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 5) (sourceB1516 + difference 5 2) sourceC1516) = raw23035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23035; decide +kernel
    rw [ha]
    exact (canonical23035 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1516 + sourceB1516) sourceC1516) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1516 + sourceB1516) sourceC1516) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1516 sourceB1516 sourceC1516 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1516 sourceB1516 sourceC1516
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1516, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1517 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1517 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC1517 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm1517 : Integer.Sparse Master := [(Sum.inr 4106, 2), (Sum.inr 4109, 1), (Sum.inr 4111, 1), (Sum.inr 4132, 1), (Sum.inr 4291, 2), (Sum.inr 4294, 2), (Sum.inr 4296, 2), (Sum.inr 4313, 2), (Sum.inr 4354, 2), (Sum.inr 4359, 1), (Sum.inr 4361, 1), (Sum.inr 4452, 2), (Sum.inr 4454, 1), (Sum.inr 4461, 2), (Sum.inr 4463, 1), (Sum.inr 4491, 1), (Sum.inr 4503, 1), (Sum.inr 5080, 2), (Sum.inr 5176, 1), (Sum.inr 5291, 1), (Sum.inr 5294, 1)]

theorem sourceEq1517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1517 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 1) (sourceB1517 + difference 1 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 1) (sourceB1517 + difference 1 0) sourceC1517) = raw17694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw17694; decide +kernel
    rw [ha]
    exact (canonical17694 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 2) (sourceB1517 + difference 2 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 2) (sourceB1517 + difference 2 0) sourceC1517) = raw23036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23036; decide +kernel
    rw [ha]
    exact (canonical23036 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 3) (sourceB1517 + difference 3 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 3) (sourceB1517 + difference 3 0) sourceC1517) = raw23037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23037; decide +kernel
    rw [ha]
    exact (canonical23037 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 4) (sourceB1517 + difference 4 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 4) (sourceB1517 + difference 4 0) sourceC1517) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 5) (sourceB1517 + difference 5 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 5) (sourceB1517 + difference 5 0) sourceC1517) = raw3049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw3049; decide +kernel
    rw [ha]
    exact (canonical3049 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 0) (sourceB1517 + difference 0 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4132) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 0) (sourceB1517 + difference 0 1) sourceC1517) = raw23038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23038; decide +kernel
    rw [ha]
    exact (canonical23038 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 2) (sourceB1517 + difference 2 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 2) (sourceB1517 + difference 2 1) sourceC1517) = raw23039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23039; decide +kernel
    rw [ha]
    exact (canonical23039 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 3) (sourceB1517 + difference 3 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 3) (sourceB1517 + difference 3 1) sourceC1517) = raw23040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23040; decide +kernel
    rw [ha]
    exact (canonical23040 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 4) (sourceB1517 + difference 4 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 4) (sourceB1517 + difference 4 1) sourceC1517) = raw21243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21243; decide +kernel
    rw [ha]
    exact (canonical21243 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 5) (sourceB1517 + difference 5 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 5) (sourceB1517 + difference 5 1) sourceC1517) = raw23041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23041; decide +kernel
    rw [ha]
    exact (canonical23041 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 0) (sourceB1517 + difference 0 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4106) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 0) (sourceB1517 + difference 0 2) sourceC1517) = raw23042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23042; decide +kernel
    rw [ha]
    exact (canonical23042 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 1) (sourceB1517 + difference 1 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 1) (sourceB1517 + difference 1 2) sourceC1517) = raw23043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23043; decide +kernel
    rw [ha]
    exact (canonical23043 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 3) (sourceB1517 + difference 3 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 3) (sourceB1517 + difference 3 2) sourceC1517) = raw23044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23044; decide +kernel
    rw [ha]
    exact (canonical23044 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 4) (sourceB1517 + difference 4 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 4) (sourceB1517 + difference 4 2) sourceC1517) = raw21248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21248; decide +kernel
    rw [ha]
    exact (canonical21248 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 5) (sourceB1517 + difference 5 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 5) (sourceB1517 + difference 5 2) sourceC1517) = raw23045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23045; decide +kernel
    rw [ha]
    exact (canonical23045 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 0) (sourceB1517 + difference 0 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4106) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 0) (sourceB1517 + difference 0 3) sourceC1517) = raw23046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23046; decide +kernel
    rw [ha]
    exact (canonical23046 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 1) (sourceB1517 + difference 1 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 1) (sourceB1517 + difference 1 3) sourceC1517) = raw23047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23047; decide +kernel
    rw [ha]
    exact (canonical23047 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 2) (sourceB1517 + difference 2 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 2) (sourceB1517 + difference 2 3) sourceC1517) = raw23048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23048; decide +kernel
    rw [ha]
    exact (canonical23048 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 4) (sourceB1517 + difference 4 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 4) (sourceB1517 + difference 4 3) sourceC1517) = raw13591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw13591; decide +kernel
    rw [ha]
    exact (canonical13591 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 5) (sourceB1517 + difference 5 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 5) (sourceB1517 + difference 5 3) sourceC1517) = raw13587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw13587; decide +kernel
    rw [ha]
    exact (canonical13587 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 0) (sourceB1517 + difference 0 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4109) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 0) (sourceB1517 + difference 0 4) sourceC1517) = raw23049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23049; decide +kernel
    rw [ha]
    exact (canonical23049 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 1) (sourceB1517 + difference 1 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 1) (sourceB1517 + difference 1 4) sourceC1517) = raw23050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23050; decide +kernel
    rw [ha]
    exact (canonical23050 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 2) (sourceB1517 + difference 2 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4294) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 2) (sourceB1517 + difference 2 4) sourceC1517) = raw23051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23051; decide +kernel
    rw [ha]
    exact (canonical23051 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 3) (sourceB1517 + difference 3 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4294) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 3) (sourceB1517 + difference 3 4) sourceC1517) = raw23052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23052; decide +kernel
    rw [ha]
    exact (canonical23052 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 5) (sourceB1517 + difference 5 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 5) (sourceB1517 + difference 5 4) sourceC1517) = raw23053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23053; decide +kernel
    rw [ha]
    exact (canonical23053 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 0) (sourceB1517 + difference 0 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4111) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 0) (sourceB1517 + difference 0 5) sourceC1517) = raw21253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21253; decide +kernel
    rw [ha]
    exact (canonical21253 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 1) (sourceB1517 + difference 1 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 1) (sourceB1517 + difference 1 5) sourceC1517) = raw21254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21254; decide +kernel
    rw [ha]
    exact (canonical21254 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 2) (sourceB1517 + difference 2 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 2) (sourceB1517 + difference 2 5) sourceC1517) = raw21255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21255; decide +kernel
    rw [ha]
    exact (canonical21255 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 3) (sourceB1517 + difference 3 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 3) (sourceB1517 + difference 3 5) sourceC1517) = raw21256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21256; decide +kernel
    rw [ha]
    exact (canonical21256 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 4) (sourceB1517 + difference 4 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 4) (sourceB1517 + difference 4 5) sourceC1517) = raw23054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23054; decide +kernel
    rw [ha]
    exact (canonical23054 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1517 sourceB1517 sourceC1517
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1517, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1518 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1518 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC1518 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm1518 : Integer.Sparse Master := [(Sum.inr 543, 2), (Sum.inr 546, 1), (Sum.inr 548, 1), (Sum.inr 562, 1), (Sum.inr 869, 2), (Sum.inr 872, 2), (Sum.inr 874, 2), (Sum.inr 891, 2), (Sum.inr 932, 2), (Sum.inr 937, 1), (Sum.inr 939, 1), (Sum.inr 1035, 2), (Sum.inr 1037, 1), (Sum.inr 1044, 2), (Sum.inr 1046, 1), (Sum.inr 1075, 1), (Sum.inr 1087, 1), (Sum.inr 2488, 2), (Sum.inr 2604, 1), (Sum.inr 2765, 1), (Sum.inr 2768, 1)]

theorem sourceEq1518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1518 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1518 + difference 0 1) (sourceB1518 + difference 1 0) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA1518 + difference 0 1) (sourceB1518 + difference 1 0) sourceC1518) = raw23055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23055; decide +kernel
    rw [ha]
    exact (canonical23055 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1518 + difference 0 2) (sourceB1518 + difference 2 0) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA1518 + difference 0 2) (sourceB1518 + difference 2 0) sourceC1518) = raw23056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23056; decide +kernel
    rw [ha]
    exact (canonical23056 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1518 + difference 0 3) (sourceB1518 + difference 3 0) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA1518 + difference 0 3) (sourceB1518 + difference 3 0) sourceC1518) = raw23057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23057; decide +kernel
    rw [ha]
    exact (canonical23057 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1518 + difference 0 4) (sourceB1518 + difference 4 0) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA1518 + difference 0 4) (sourceB1518 + difference 4 0) sourceC1518) = raw3084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw3084; decide +kernel
    rw [ha]
    exact (canonical3084 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1518 + difference 0 5) (sourceB1518 + difference 5 0) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA1518 + difference 0 5) (sourceB1518 + difference 5 0) sourceC1518) = raw3079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw3079; decide +kernel
    rw [ha]
    exact (canonical3079 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1518 + difference 1 0) (sourceB1518 + difference 0 1) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 562) := by
    have ha : (tripleCharges (sourceA1518 + difference 1 0) (sourceB1518 + difference 0 1) sourceC1518) = raw23058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23058; decide +kernel
    rw [ha]
    exact (canonical23058 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1518 + difference 1 2) (sourceB1518 + difference 2 1) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 891) := by
    have ha : (tripleCharges (sourceA1518 + difference 1 2) (sourceB1518 + difference 2 1) sourceC1518) = raw23059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23059; decide +kernel
    rw [ha]
    exact (canonical23059 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1518 + difference 1 3) (sourceB1518 + difference 3 1) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 891) := by
    have ha : (tripleCharges (sourceA1518 + difference 1 3) (sourceB1518 + difference 3 1) sourceC1518) = raw23060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23060; decide +kernel
    rw [ha]
    exact (canonical23060 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1518 + difference 1 4) (sourceB1518 + difference 4 1) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1518 + difference 1 4) (sourceB1518 + difference 4 1) sourceC1518) = raw21271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw21271; decide +kernel
    rw [ha]
    exact (canonical21271 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1518 + difference 1 5) (sourceB1518 + difference 5 1) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1518 + difference 1 5) (sourceB1518 + difference 5 1) sourceC1518) = raw23061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23061; decide +kernel
    rw [ha]
    exact (canonical23061 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1518 + difference 2 0) (sourceB1518 + difference 0 2) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 543) := by
    have ha : (tripleCharges (sourceA1518 + difference 2 0) (sourceB1518 + difference 0 2) sourceC1518) = raw23062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23062; decide +kernel
    rw [ha]
    exact (canonical23062 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1518 + difference 2 1) (sourceB1518 + difference 1 2) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA1518 + difference 2 1) (sourceB1518 + difference 1 2) sourceC1518) = raw23063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23063; decide +kernel
    rw [ha]
    exact (canonical23063 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1518 + difference 2 3) (sourceB1518 + difference 3 2) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 869) := by
    have ha : (tripleCharges (sourceA1518 + difference 2 3) (sourceB1518 + difference 3 2) sourceC1518) = raw23064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23064; decide +kernel
    rw [ha]
    exact (canonical23064 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1518 + difference 2 4) (sourceB1518 + difference 4 2) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1518 + difference 2 4) (sourceB1518 + difference 4 2) sourceC1518) = raw21276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw21276; decide +kernel
    rw [ha]
    exact (canonical21276 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1518 + difference 2 5) (sourceB1518 + difference 5 2) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1518 + difference 2 5) (sourceB1518 + difference 5 2) sourceC1518) = raw23065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23065; decide +kernel
    rw [ha]
    exact (canonical23065 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1518 + difference 3 0) (sourceB1518 + difference 0 3) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 543) := by
    have ha : (tripleCharges (sourceA1518 + difference 3 0) (sourceB1518 + difference 0 3) sourceC1518) = raw23066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23066; decide +kernel
    rw [ha]
    exact (canonical23066 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1518 + difference 3 1) (sourceB1518 + difference 1 3) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA1518 + difference 3 1) (sourceB1518 + difference 1 3) sourceC1518) = raw23067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23067; decide +kernel
    rw [ha]
    exact (canonical23067 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1518 + difference 3 2) (sourceB1518 + difference 2 3) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 869) := by
    have ha : (tripleCharges (sourceA1518 + difference 3 2) (sourceB1518 + difference 2 3) sourceC1518) = raw23068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23068; decide +kernel
    rw [ha]
    exact (canonical23068 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1518 + difference 3 4) (sourceB1518 + difference 4 3) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1518 + difference 3 4) (sourceB1518 + difference 4 3) sourceC1518) = raw13613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw13613; decide +kernel
    rw [ha]
    exact (canonical13613 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1518 + difference 3 5) (sourceB1518 + difference 5 3) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1518 + difference 3 5) (sourceB1518 + difference 5 3) sourceC1518) = raw13609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw13609; decide +kernel
    rw [ha]
    exact (canonical13609 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1518 + difference 4 0) (sourceB1518 + difference 0 4) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 546) := by
    have ha : (tripleCharges (sourceA1518 + difference 4 0) (sourceB1518 + difference 0 4) sourceC1518) = raw23069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23069; decide +kernel
    rw [ha]
    exact (canonical23069 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1518 + difference 4 1) (sourceB1518 + difference 1 4) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 937) := by
    have ha : (tripleCharges (sourceA1518 + difference 4 1) (sourceB1518 + difference 1 4) sourceC1518) = raw23070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23070; decide +kernel
    rw [ha]
    exact (canonical23070 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1518 + difference 4 2) (sourceB1518 + difference 2 4) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 872) := by
    have ha : (tripleCharges (sourceA1518 + difference 4 2) (sourceB1518 + difference 2 4) sourceC1518) = raw23071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23071; decide +kernel
    rw [ha]
    exact (canonical23071 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1518 + difference 4 3) (sourceB1518 + difference 3 4) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 872) := by
    have ha : (tripleCharges (sourceA1518 + difference 4 3) (sourceB1518 + difference 3 4) sourceC1518) = raw23072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23072; decide +kernel
    rw [ha]
    exact (canonical23072 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1518 + difference 4 5) (sourceB1518 + difference 5 4) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1518 + difference 4 5) (sourceB1518 + difference 5 4) sourceC1518) = raw23073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23073; decide +kernel
    rw [ha]
    exact (canonical23073 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1518 + difference 5 0) (sourceB1518 + difference 0 5) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 548) := by
    have ha : (tripleCharges (sourceA1518 + difference 5 0) (sourceB1518 + difference 0 5) sourceC1518) = raw21281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw21281; decide +kernel
    rw [ha]
    exact (canonical21281 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1518 + difference 5 1) (sourceB1518 + difference 1 5) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 939) := by
    have ha : (tripleCharges (sourceA1518 + difference 5 1) (sourceB1518 + difference 1 5) sourceC1518) = raw21282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw21282; decide +kernel
    rw [ha]
    exact (canonical21282 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1518 + difference 5 2) (sourceB1518 + difference 2 5) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 874) := by
    have ha : (tripleCharges (sourceA1518 + difference 5 2) (sourceB1518 + difference 2 5) sourceC1518) = raw21283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw21283; decide +kernel
    rw [ha]
    exact (canonical21283 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1518 + difference 5 3) (sourceB1518 + difference 3 5) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 874) := by
    have ha : (tripleCharges (sourceA1518 + difference 5 3) (sourceB1518 + difference 3 5) sourceC1518) = raw21284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw21284; decide +kernel
    rw [ha]
    exact (canonical21284 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1518 + difference 5 4) (sourceB1518 + difference 4 5) sourceC1518) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1518 + difference 5 4) (sourceB1518 + difference 4 5) sourceC1518) = raw23074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1518 sourceB1518 sourceC1518 difference raw23074; decide +kernel
    rw [ha]
    exact (canonical23074 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1518 sourceB1518 sourceC1518
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1518, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1519 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1519 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC1519 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1519 : Integer.Sparse Master := [(Sum.inr 4255, 2), (Sum.inr 4272, 1), (Sum.inr 4273, 1), (Sum.inr 4278, 1), (Sum.inr 4392, 2), (Sum.inr 4403, 2), (Sum.inr 4404, 2), (Sum.inr 4411, 2), (Sum.inr 4443, 2), (Sum.inr 4444, 2), (Sum.inr 4465, 1), (Sum.inr 4466, 2), (Sum.inr 4467, 1), (Sum.inr 4479, 1), (Sum.inr 4480, 1), (Sum.inr 4510, 1), (Sum.inr 4511, 1), (Sum.inr 4592, 2), (Sum.inr 4611, 1), (Sum.inr 4612, 1), (Sum.inr 4627, 1)]

theorem sourceEq1519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1519 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1519 + difference 0 1) (sourceB1519 + difference 1 0) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1519 + difference 0 1) (sourceB1519 + difference 1 0) sourceC1519) = raw22627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw22627; decide +kernel
    rw [ha]
    exact (canonical22627 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1519 + difference 0 2) (sourceB1519 + difference 2 0) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1519 + difference 0 2) (sourceB1519 + difference 2 0) sourceC1519) = raw23075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23075; decide +kernel
    rw [ha]
    exact (canonical23075 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1519 + difference 0 3) (sourceB1519 + difference 3 0) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1519 + difference 0 3) (sourceB1519 + difference 3 0) sourceC1519) = raw22778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw22778; decide +kernel
    rw [ha]
    exact (canonical22778 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1519 + difference 0 4) (sourceB1519 + difference 4 0) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1519 + difference 0 4) (sourceB1519 + difference 4 0) sourceC1519) = raw22614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw22614; decide +kernel
    rw [ha]
    exact (canonical22614 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1519 + difference 0 5) (sourceB1519 + difference 5 0) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1519 + difference 0 5) (sourceB1519 + difference 5 0) sourceC1519) = raw23076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23076; decide +kernel
    rw [ha]
    exact (canonical23076 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1519 + difference 1 0) (sourceB1519 + difference 0 1) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4278) := by
    have ha : (tripleCharges (sourceA1519 + difference 1 0) (sourceB1519 + difference 0 1) sourceC1519) = raw23077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23077; decide +kernel
    rw [ha]
    exact (canonical23077 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1519 + difference 1 2) (sourceB1519 + difference 2 1) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4411) := by
    have ha : (tripleCharges (sourceA1519 + difference 1 2) (sourceB1519 + difference 2 1) sourceC1519) = raw23078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23078; decide +kernel
    rw [ha]
    exact (canonical23078 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1519 + difference 1 3) (sourceB1519 + difference 3 1) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4411) := by
    have ha : (tripleCharges (sourceA1519 + difference 1 3) (sourceB1519 + difference 3 1) sourceC1519) = raw23079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23079; decide +kernel
    rw [ha]
    exact (canonical23079 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1519 + difference 1 4) (sourceB1519 + difference 4 1) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA1519 + difference 1 4) (sourceB1519 + difference 4 1) sourceC1519) = raw23080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23080; decide +kernel
    rw [ha]
    exact (canonical23080 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1519 + difference 1 5) (sourceB1519 + difference 5 1) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4479) := by
    have ha : (tripleCharges (sourceA1519 + difference 1 5) (sourceB1519 + difference 5 1) sourceC1519) = raw23081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23081; decide +kernel
    rw [ha]
    exact (canonical23081 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1519 + difference 2 0) (sourceB1519 + difference 0 2) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA1519 + difference 2 0) (sourceB1519 + difference 0 2) sourceC1519) = raw23082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23082; decide +kernel
    rw [ha]
    exact (canonical23082 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1519 + difference 2 1) (sourceB1519 + difference 1 2) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1519 + difference 2 1) (sourceB1519 + difference 1 2) sourceC1519) = raw23083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23083; decide +kernel
    rw [ha]
    exact (canonical23083 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1519 + difference 2 3) (sourceB1519 + difference 3 2) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4392) := by
    have ha : (tripleCharges (sourceA1519 + difference 2 3) (sourceB1519 + difference 3 2) sourceC1519) = raw23084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23084; decide +kernel
    rw [ha]
    exact (canonical23084 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1519 + difference 2 4) (sourceB1519 + difference 4 2) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1519 + difference 2 4) (sourceB1519 + difference 4 2) sourceC1519) = raw23085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23085; decide +kernel
    rw [ha]
    exact (canonical23085 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1519 + difference 2 5) (sourceB1519 + difference 5 2) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4443) := by
    have ha : (tripleCharges (sourceA1519 + difference 2 5) (sourceB1519 + difference 5 2) sourceC1519) = raw23086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23086; decide +kernel
    rw [ha]
    exact (canonical23086 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1519 + difference 3 0) (sourceB1519 + difference 0 3) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA1519 + difference 3 0) (sourceB1519 + difference 0 3) sourceC1519) = raw23087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23087; decide +kernel
    rw [ha]
    exact (canonical23087 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1519 + difference 3 1) (sourceB1519 + difference 1 3) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1519 + difference 3 1) (sourceB1519 + difference 1 3) sourceC1519) = raw23088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23088; decide +kernel
    rw [ha]
    exact (canonical23088 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1519 + difference 3 2) (sourceB1519 + difference 2 3) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4392) := by
    have ha : (tripleCharges (sourceA1519 + difference 3 2) (sourceB1519 + difference 2 3) sourceC1519) = raw23089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23089; decide +kernel
    rw [ha]
    exact (canonical23089 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1519 + difference 3 4) (sourceB1519 + difference 4 3) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1519 + difference 3 4) (sourceB1519 + difference 4 3) sourceC1519) = raw23090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23090; decide +kernel
    rw [ha]
    exact (canonical23090 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1519 + difference 3 5) (sourceB1519 + difference 5 3) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4443) := by
    have ha : (tripleCharges (sourceA1519 + difference 3 5) (sourceB1519 + difference 5 3) sourceC1519) = raw23091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23091; decide +kernel
    rw [ha]
    exact (canonical23091 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1519 + difference 4 0) (sourceB1519 + difference 0 4) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1519 + difference 4 0) (sourceB1519 + difference 0 4) sourceC1519) = raw23092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23092; decide +kernel
    rw [ha]
    exact (canonical23092 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1519 + difference 4 1) (sourceB1519 + difference 1 4) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1519 + difference 4 1) (sourceB1519 + difference 1 4) sourceC1519) = raw23093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23093; decide +kernel
    rw [ha]
    exact (canonical23093 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1519 + difference 4 2) (sourceB1519 + difference 2 4) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA1519 + difference 4 2) (sourceB1519 + difference 2 4) sourceC1519) = raw23094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23094; decide +kernel
    rw [ha]
    exact (canonical23094 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1519 + difference 4 3) (sourceB1519 + difference 3 4) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA1519 + difference 4 3) (sourceB1519 + difference 3 4) sourceC1519) = raw23095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23095; decide +kernel
    rw [ha]
    exact (canonical23095 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1519 + difference 4 5) (sourceB1519 + difference 5 4) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4465) := by
    have ha : (tripleCharges (sourceA1519 + difference 4 5) (sourceB1519 + difference 5 4) sourceC1519) = raw23096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23096; decide +kernel
    rw [ha]
    exact (canonical23096 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1519 + difference 5 0) (sourceB1519 + difference 0 5) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1519 + difference 5 0) (sourceB1519 + difference 0 5) sourceC1519) = raw23097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23097; decide +kernel
    rw [ha]
    exact (canonical23097 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1519 + difference 5 1) (sourceB1519 + difference 1 5) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1519 + difference 5 1) (sourceB1519 + difference 1 5) sourceC1519) = raw22623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw22623; decide +kernel
    rw [ha]
    exact (canonical22623 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1519 + difference 5 2) (sourceB1519 + difference 2 5) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1519 + difference 5 2) (sourceB1519 + difference 2 5) sourceC1519) = raw23098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw23098; decide +kernel
    rw [ha]
    exact (canonical23098 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1519 + difference 5 3) (sourceB1519 + difference 3 5) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1519 + difference 5 3) (sourceB1519 + difference 3 5) sourceC1519) = raw22775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw22775; decide +kernel
    rw [ha]
    exact (canonical22775 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1519 + difference 5 4) (sourceB1519 + difference 4 5) sourceC1519) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1519 + difference 5 4) (sourceB1519 + difference 4 5) sourceC1519) = raw22611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1519 sourceB1519 sourceC1519 difference raw22611; decide +kernel
    rw [ha]
    exact (canonical22611 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1519 sourceB1519 sourceC1519
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1519, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1520 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1520 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC1520 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1520 : Integer.Sparse Master := [(Sum.inr 789, 2), (Sum.inr 815, 1), (Sum.inr 816, 1), (Sum.inr 830, 1), (Sum.inr 973, 2), (Sum.inr 984, 2), (Sum.inr 985, 2), (Sum.inr 992, 2), (Sum.inr 1025, 2), (Sum.inr 1026, 2), (Sum.inr 1048, 1), (Sum.inr 1049, 2), (Sum.inr 1050, 1), (Sum.inr 1062, 1), (Sum.inr 1063, 1), (Sum.inr 1094, 1), (Sum.inr 1095, 1), (Sum.inr 1219, 2), (Sum.inr 1273, 1), (Sum.inr 1274, 1), (Sum.inr 1311, 1)]

theorem sourceEq1520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1520 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1520 + difference 0 1) (sourceB1520 + difference 1 0) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1520 + difference 0 1) (sourceB1520 + difference 1 0) sourceC1520) = raw22649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw22649; decide +kernel
    rw [ha]
    exact (canonical22649 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1520 + difference 0 2) (sourceB1520 + difference 2 0) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1520 + difference 0 2) (sourceB1520 + difference 2 0) sourceC1520) = raw23099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23099; decide +kernel
    rw [ha]
    exact (canonical23099 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1520 + difference 0 3) (sourceB1520 + difference 3 0) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1520 + difference 0 3) (sourceB1520 + difference 3 0) sourceC1520) = raw22799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw22799; decide +kernel
    rw [ha]
    exact (canonical22799 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1520 + difference 0 4) (sourceB1520 + difference 4 0) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1520 + difference 0 4) (sourceB1520 + difference 4 0) sourceC1520) = raw22636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw22636; decide +kernel
    rw [ha]
    exact (canonical22636 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1520 + difference 0 5) (sourceB1520 + difference 5 0) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1520 + difference 0 5) (sourceB1520 + difference 5 0) sourceC1520) = raw23100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23100; decide +kernel
    rw [ha]
    exact (canonical23100 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1520 + difference 1 0) (sourceB1520 + difference 0 1) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA1520 + difference 1 0) (sourceB1520 + difference 0 1) sourceC1520) = raw23101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23101; decide +kernel
    rw [ha]
    exact (canonical23101 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1520 + difference 1 2) (sourceB1520 + difference 2 1) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 992) := by
    have ha : (tripleCharges (sourceA1520 + difference 1 2) (sourceB1520 + difference 2 1) sourceC1520) = raw23102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23102; decide +kernel
    rw [ha]
    exact (canonical23102 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1520 + difference 1 3) (sourceB1520 + difference 3 1) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 992) := by
    have ha : (tripleCharges (sourceA1520 + difference 1 3) (sourceB1520 + difference 3 1) sourceC1520) = raw23103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23103; decide +kernel
    rw [ha]
    exact (canonical23103 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1520 + difference 1 4) (sourceB1520 + difference 4 1) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA1520 + difference 1 4) (sourceB1520 + difference 4 1) sourceC1520) = raw23104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23104; decide +kernel
    rw [ha]
    exact (canonical23104 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1520 + difference 1 5) (sourceB1520 + difference 5 1) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1062) := by
    have ha : (tripleCharges (sourceA1520 + difference 1 5) (sourceB1520 + difference 5 1) sourceC1520) = raw23105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23105; decide +kernel
    rw [ha]
    exact (canonical23105 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1520 + difference 2 0) (sourceB1520 + difference 0 2) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA1520 + difference 2 0) (sourceB1520 + difference 0 2) sourceC1520) = raw23106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23106; decide +kernel
    rw [ha]
    exact (canonical23106 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1520 + difference 2 1) (sourceB1520 + difference 1 2) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1520 + difference 2 1) (sourceB1520 + difference 1 2) sourceC1520) = raw23107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23107; decide +kernel
    rw [ha]
    exact (canonical23107 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1520 + difference 2 3) (sourceB1520 + difference 3 2) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 973) := by
    have ha : (tripleCharges (sourceA1520 + difference 2 3) (sourceB1520 + difference 3 2) sourceC1520) = raw23108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23108; decide +kernel
    rw [ha]
    exact (canonical23108 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1520 + difference 2 4) (sourceB1520 + difference 4 2) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1520 + difference 2 4) (sourceB1520 + difference 4 2) sourceC1520) = raw23109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23109; decide +kernel
    rw [ha]
    exact (canonical23109 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1520 + difference 2 5) (sourceB1520 + difference 5 2) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1025) := by
    have ha : (tripleCharges (sourceA1520 + difference 2 5) (sourceB1520 + difference 5 2) sourceC1520) = raw23110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23110; decide +kernel
    rw [ha]
    exact (canonical23110 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1520 + difference 3 0) (sourceB1520 + difference 0 3) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA1520 + difference 3 0) (sourceB1520 + difference 0 3) sourceC1520) = raw23111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23111; decide +kernel
    rw [ha]
    exact (canonical23111 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1520 + difference 3 1) (sourceB1520 + difference 1 3) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1520 + difference 3 1) (sourceB1520 + difference 1 3) sourceC1520) = raw23112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23112; decide +kernel
    rw [ha]
    exact (canonical23112 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1520 + difference 3 2) (sourceB1520 + difference 2 3) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 973) := by
    have ha : (tripleCharges (sourceA1520 + difference 3 2) (sourceB1520 + difference 2 3) sourceC1520) = raw23113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23113; decide +kernel
    rw [ha]
    exact (canonical23113 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1520 + difference 3 4) (sourceB1520 + difference 4 3) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1520 + difference 3 4) (sourceB1520 + difference 4 3) sourceC1520) = raw23114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23114; decide +kernel
    rw [ha]
    exact (canonical23114 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1520 + difference 3 5) (sourceB1520 + difference 5 3) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1025) := by
    have ha : (tripleCharges (sourceA1520 + difference 3 5) (sourceB1520 + difference 5 3) sourceC1520) = raw23115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23115; decide +kernel
    rw [ha]
    exact (canonical23115 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1520 + difference 4 0) (sourceB1520 + difference 0 4) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1520 + difference 4 0) (sourceB1520 + difference 0 4) sourceC1520) = raw23116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23116; decide +kernel
    rw [ha]
    exact (canonical23116 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1520 + difference 4 1) (sourceB1520 + difference 1 4) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1520 + difference 4 1) (sourceB1520 + difference 1 4) sourceC1520) = raw23117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23117; decide +kernel
    rw [ha]
    exact (canonical23117 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1520 + difference 4 2) (sourceB1520 + difference 2 4) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1520 + difference 4 2) (sourceB1520 + difference 2 4) sourceC1520) = raw23118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23118; decide +kernel
    rw [ha]
    exact (canonical23118 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1520 + difference 4 3) (sourceB1520 + difference 3 4) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1520 + difference 4 3) (sourceB1520 + difference 3 4) sourceC1520) = raw23119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23119; decide +kernel
    rw [ha]
    exact (canonical23119 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1520 + difference 4 5) (sourceB1520 + difference 5 4) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1048) := by
    have ha : (tripleCharges (sourceA1520 + difference 4 5) (sourceB1520 + difference 5 4) sourceC1520) = raw23120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23120; decide +kernel
    rw [ha]
    exact (canonical23120 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1520 + difference 5 0) (sourceB1520 + difference 0 5) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1520 + difference 5 0) (sourceB1520 + difference 0 5) sourceC1520) = raw23121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23121; decide +kernel
    rw [ha]
    exact (canonical23121 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1520 + difference 5 1) (sourceB1520 + difference 1 5) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1520 + difference 5 1) (sourceB1520 + difference 1 5) sourceC1520) = raw22645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw22645; decide +kernel
    rw [ha]
    exact (canonical22645 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1520 + difference 5 2) (sourceB1520 + difference 2 5) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1520 + difference 5 2) (sourceB1520 + difference 2 5) sourceC1520) = raw23122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw23122; decide +kernel
    rw [ha]
    exact (canonical23122 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1520 + difference 5 3) (sourceB1520 + difference 3 5) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1520 + difference 5 3) (sourceB1520 + difference 3 5) sourceC1520) = raw22796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw22796; decide +kernel
    rw [ha]
    exact (canonical22796 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1520 + difference 5 4) (sourceB1520 + difference 4 5) sourceC1520) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1520 + difference 5 4) (sourceB1520 + difference 4 5) sourceC1520) = raw22633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1520 sourceB1520 sourceC1520 difference raw22633; decide +kernel
    rw [ha]
    exact (canonical22633 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1520 sourceB1520 sourceC1520
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1520, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1521 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1521 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC1521 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1521 : Integer.Sparse Master := [(Sum.inr 1219, 2), (Sum.inr 1245, 1), (Sum.inr 1246, 1), (Sum.inr 1311, 1), (Sum.inr 1362, 2), (Sum.inr 1374, 1), (Sum.inr 1375, 1), (Sum.inr 1380, 2), (Sum.inr 1390, 2), (Sum.inr 1391, 2), (Sum.inr 1400, 2), (Sum.inr 1401, 2), (Sum.inr 1418, 1), (Sum.inr 1419, 2), (Sum.inr 1420, 1), (Sum.inr 1454, 1), (Sum.inr 1455, 1), (Sum.inr 1470, 2), (Sum.inr 1471, 1), (Sum.inr 1472, 1), (Sum.inr 1486, 1)]

theorem sourceEq1521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1521 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1521 + difference 0 1) (sourceB1521 + difference 1 0) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1521 + difference 0 1) (sourceB1521 + difference 1 0) sourceC1521) = raw22832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw22832; decide +kernel
    rw [ha]
    exact (canonical22832 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1521 + difference 0 2) (sourceB1521 + difference 2 0) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1521 + difference 0 2) (sourceB1521 + difference 2 0) sourceC1521) = raw23123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23123; decide +kernel
    rw [ha]
    exact (canonical23123 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1521 + difference 0 3) (sourceB1521 + difference 3 0) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1521 + difference 0 3) (sourceB1521 + difference 3 0) sourceC1521) = raw22822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw22822; decide +kernel
    rw [ha]
    exact (canonical22822 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1521 + difference 0 4) (sourceB1521 + difference 4 0) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1521 + difference 0 4) (sourceB1521 + difference 4 0) sourceC1521) = raw23124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23124; decide +kernel
    rw [ha]
    exact (canonical23124 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1521 + difference 0 5) (sourceB1521 + difference 5 0) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1521 + difference 0 5) (sourceB1521 + difference 5 0) sourceC1521) = raw23125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23125; decide +kernel
    rw [ha]
    exact (canonical23125 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1521 + difference 1 0) (sourceB1521 + difference 0 1) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1472) := by
    have ha : (tripleCharges (sourceA1521 + difference 1 0) (sourceB1521 + difference 0 1) sourceC1521) = raw23126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23126; decide +kernel
    rw [ha]
    exact (canonical23126 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1521 + difference 1 2) (sourceB1521 + difference 2 1) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1362) := by
    have ha : (tripleCharges (sourceA1521 + difference 1 2) (sourceB1521 + difference 2 1) sourceC1521) = raw23127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23127; decide +kernel
    rw [ha]
    exact (canonical23127 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1521 + difference 1 3) (sourceB1521 + difference 3 1) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1362) := by
    have ha : (tripleCharges (sourceA1521 + difference 1 3) (sourceB1521 + difference 3 1) sourceC1521) = raw23128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23128; decide +kernel
    rw [ha]
    exact (canonical23128 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1521 + difference 1 4) (sourceB1521 + difference 4 1) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA1521 + difference 1 4) (sourceB1521 + difference 4 1) sourceC1521) = raw23129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23129; decide +kernel
    rw [ha]
    exact (canonical23129 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1521 + difference 1 5) (sourceB1521 + difference 5 1) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1374) := by
    have ha : (tripleCharges (sourceA1521 + difference 1 5) (sourceB1521 + difference 5 1) sourceC1521) = raw23130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23130; decide +kernel
    rw [ha]
    exact (canonical23130 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1521 + difference 2 0) (sourceB1521 + difference 0 2) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1470) := by
    have ha : (tripleCharges (sourceA1521 + difference 2 0) (sourceB1521 + difference 0 2) sourceC1521) = raw23131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23131; decide +kernel
    rw [ha]
    exact (canonical23131 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1521 + difference 2 1) (sourceB1521 + difference 1 2) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1521 + difference 2 1) (sourceB1521 + difference 1 2) sourceC1521) = raw23132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23132; decide +kernel
    rw [ha]
    exact (canonical23132 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1521 + difference 2 3) (sourceB1521 + difference 3 2) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1380) := by
    have ha : (tripleCharges (sourceA1521 + difference 2 3) (sourceB1521 + difference 3 2) sourceC1521) = raw23133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23133; decide +kernel
    rw [ha]
    exact (canonical23133 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1521 + difference 2 4) (sourceB1521 + difference 4 2) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1521 + difference 2 4) (sourceB1521 + difference 4 2) sourceC1521) = raw23134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23134; decide +kernel
    rw [ha]
    exact (canonical23134 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1521 + difference 2 5) (sourceB1521 + difference 5 2) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1390) := by
    have ha : (tripleCharges (sourceA1521 + difference 2 5) (sourceB1521 + difference 5 2) sourceC1521) = raw23135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23135; decide +kernel
    rw [ha]
    exact (canonical23135 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1521 + difference 3 0) (sourceB1521 + difference 0 3) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1470) := by
    have ha : (tripleCharges (sourceA1521 + difference 3 0) (sourceB1521 + difference 0 3) sourceC1521) = raw23136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23136; decide +kernel
    rw [ha]
    exact (canonical23136 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1521 + difference 3 1) (sourceB1521 + difference 1 3) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1521 + difference 3 1) (sourceB1521 + difference 1 3) sourceC1521) = raw23137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23137; decide +kernel
    rw [ha]
    exact (canonical23137 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1521 + difference 3 2) (sourceB1521 + difference 2 3) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1380) := by
    have ha : (tripleCharges (sourceA1521 + difference 3 2) (sourceB1521 + difference 2 3) sourceC1521) = raw23138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23138; decide +kernel
    rw [ha]
    exact (canonical23138 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1521 + difference 3 4) (sourceB1521 + difference 4 3) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1521 + difference 3 4) (sourceB1521 + difference 4 3) sourceC1521) = raw23139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23139; decide +kernel
    rw [ha]
    exact (canonical23139 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1521 + difference 3 5) (sourceB1521 + difference 5 3) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1390) := by
    have ha : (tripleCharges (sourceA1521 + difference 3 5) (sourceB1521 + difference 5 3) sourceC1521) = raw23140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23140; decide +kernel
    rw [ha]
    exact (canonical23140 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1521 + difference 4 0) (sourceB1521 + difference 0 4) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1471) := by
    have ha : (tripleCharges (sourceA1521 + difference 4 0) (sourceB1521 + difference 0 4) sourceC1521) = raw23141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23141; decide +kernel
    rw [ha]
    exact (canonical23141 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1521 + difference 4 1) (sourceB1521 + difference 1 4) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1454) := by
    have ha : (tripleCharges (sourceA1521 + difference 4 1) (sourceB1521 + difference 1 4) sourceC1521) = raw23142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23142; decide +kernel
    rw [ha]
    exact (canonical23142 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1521 + difference 4 2) (sourceB1521 + difference 2 4) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA1521 + difference 4 2) (sourceB1521 + difference 2 4) sourceC1521) = raw23143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23143; decide +kernel
    rw [ha]
    exact (canonical23143 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1521 + difference 4 3) (sourceB1521 + difference 3 4) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA1521 + difference 4 3) (sourceB1521 + difference 3 4) sourceC1521) = raw23144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23144; decide +kernel
    rw [ha]
    exact (canonical23144 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1521 + difference 4 5) (sourceB1521 + difference 5 4) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1418) := by
    have ha : (tripleCharges (sourceA1521 + difference 4 5) (sourceB1521 + difference 5 4) sourceC1521) = raw23145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23145; decide +kernel
    rw [ha]
    exact (canonical23145 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1521 + difference 5 0) (sourceB1521 + difference 0 5) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1486) := by
    have ha : (tripleCharges (sourceA1521 + difference 5 0) (sourceB1521 + difference 0 5) sourceC1521) = raw23146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23146; decide +kernel
    rw [ha]
    exact (canonical23146 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1521 + difference 5 1) (sourceB1521 + difference 1 5) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1455) := by
    have ha : (tripleCharges (sourceA1521 + difference 5 1) (sourceB1521 + difference 1 5) sourceC1521) = raw22828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw22828; decide +kernel
    rw [ha]
    exact (canonical22828 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1521 + difference 5 2) (sourceB1521 + difference 2 5) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1401) := by
    have ha : (tripleCharges (sourceA1521 + difference 5 2) (sourceB1521 + difference 2 5) sourceC1521) = raw23147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23147; decide +kernel
    rw [ha]
    exact (canonical23147 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1521 + difference 5 3) (sourceB1521 + difference 3 5) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1401) := by
    have ha : (tripleCharges (sourceA1521 + difference 5 3) (sourceB1521 + difference 3 5) sourceC1521) = raw22818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw22818; decide +kernel
    rw [ha]
    exact (canonical22818 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1521 + difference 5 4) (sourceB1521 + difference 4 5) sourceC1521) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA1521 + difference 5 4) (sourceB1521 + difference 4 5) sourceC1521) = raw23148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1521 sourceB1521 sourceC1521 difference raw23148; decide +kernel
    rw [ha]
    exact (canonical23148 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1521 sourceB1521 sourceC1521
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1521, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1522 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1522 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1522 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1522 : Integer.Sparse Master := [(Sum.inr 4155, 2), (Sum.inr 4161, 2), (Sum.inr 4186, 1), (Sum.inr 4329, 2), (Sum.inr 4335, 4), (Sum.inr 4355, 2), (Sum.inr 4369, 2), (Sum.inr 4374, 2), (Sum.inr 4458, 4), (Sum.inr 4463, 2), (Sum.inr 4502, 2), (Sum.inr 4811, 2), (Sum.inr 4875, 1), (Sum.inr 4895, 2)]

theorem sourceEq1522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1522 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 1) (sourceB1522 + difference 1 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 1) (sourceB1522 + difference 1 0) sourceC1522) = raw11419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11419; decide +kernel
    rw [ha]
    exact (canonical11419 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 2) (sourceB1522 + difference 2 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 2) (sourceB1522 + difference 2 0) sourceC1522) = raw11420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11420; decide +kernel
    rw [ha]
    exact (canonical11420 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 3) (sourceB1522 + difference 3 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 3) (sourceB1522 + difference 3 0) sourceC1522) = raw11421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11421; decide +kernel
    rw [ha]
    exact (canonical11421 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 4) (sourceB1522 + difference 4 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 4) (sourceB1522 + difference 4 0) sourceC1522) = raw21144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21144; decide +kernel
    rw [ha]
    exact (canonical21144 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 5) (sourceB1522 + difference 5 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 5) (sourceB1522 + difference 5 0) sourceC1522) = raw11422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11422; decide +kernel
    rw [ha]
    exact (canonical11422 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 0) (sourceB1522 + difference 0 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 0) (sourceB1522 + difference 0 1) sourceC1522) = raw23149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23149; decide +kernel
    rw [ha]
    exact (canonical23149 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 2) (sourceB1522 + difference 2 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 2) (sourceB1522 + difference 2 1) sourceC1522) = raw23150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23150; decide +kernel
    rw [ha]
    exact (canonical23150 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 3) (sourceB1522 + difference 3 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 3) (sourceB1522 + difference 3 1) sourceC1522) = raw23151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23151; decide +kernel
    rw [ha]
    exact (canonical23151 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 4) (sourceB1522 + difference 4 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 4) (sourceB1522 + difference 4 1) sourceC1522) = raw11403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11403; decide +kernel
    rw [ha]
    exact (canonical11403 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 5) (sourceB1522 + difference 5 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 5) (sourceB1522 + difference 5 1) sourceC1522) = raw23152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23152; decide +kernel
    rw [ha]
    exact (canonical23152 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 0) (sourceB1522 + difference 0 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4155) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 0) (sourceB1522 + difference 0 2) sourceC1522) = raw23153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23153; decide +kernel
    rw [ha]
    exact (canonical23153 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 1) (sourceB1522 + difference 1 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 1) (sourceB1522 + difference 1 2) sourceC1522) = raw23154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23154; decide +kernel
    rw [ha]
    exact (canonical23154 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 3) (sourceB1522 + difference 3 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4329) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 3) (sourceB1522 + difference 3 2) sourceC1522) = raw23155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23155; decide +kernel
    rw [ha]
    exact (canonical23155 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 4) (sourceB1522 + difference 4 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 4) (sourceB1522 + difference 4 2) sourceC1522) = raw11408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11408; decide +kernel
    rw [ha]
    exact (canonical11408 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 5) (sourceB1522 + difference 5 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 5) (sourceB1522 + difference 5 2) sourceC1522) = raw23156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23156; decide +kernel
    rw [ha]
    exact (canonical23156 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 0) (sourceB1522 + difference 0 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4155) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 0) (sourceB1522 + difference 0 3) sourceC1522) = raw23157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23157; decide +kernel
    rw [ha]
    exact (canonical23157 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 1) (sourceB1522 + difference 1 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 1) (sourceB1522 + difference 1 3) sourceC1522) = raw23158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23158; decide +kernel
    rw [ha]
    exact (canonical23158 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 2) (sourceB1522 + difference 2 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4329) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 2) (sourceB1522 + difference 2 3) sourceC1522) = raw23159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23159; decide +kernel
    rw [ha]
    exact (canonical23159 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 4) (sourceB1522 + difference 4 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 4) (sourceB1522 + difference 4 3) sourceC1522) = raw11413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11413; decide +kernel
    rw [ha]
    exact (canonical11413 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 5) (sourceB1522 + difference 5 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 5) (sourceB1522 + difference 5 3) sourceC1522) = raw23160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23160; decide +kernel
    rw [ha]
    exact (canonical23160 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 0) (sourceB1522 + difference 0 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 0) (sourceB1522 + difference 0 4) sourceC1522) = raw23161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23161; decide +kernel
    rw [ha]
    exact (canonical23161 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 1) (sourceB1522 + difference 1 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 1) (sourceB1522 + difference 1 4) sourceC1522) = raw23162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23162; decide +kernel
    rw [ha]
    exact (canonical23162 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 2) (sourceB1522 + difference 2 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 2) (sourceB1522 + difference 2 4) sourceC1522) = raw23163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23163; decide +kernel
    rw [ha]
    exact (canonical23163 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 3) (sourceB1522 + difference 3 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 3) (sourceB1522 + difference 3 4) sourceC1522) = raw23164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23164; decide +kernel
    rw [ha]
    exact (canonical23164 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 5) (sourceB1522 + difference 5 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 5) (sourceB1522 + difference 5 4) sourceC1522) = raw23165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23165; decide +kernel
    rw [ha]
    exact (canonical23165 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 0) (sourceB1522 + difference 0 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 0) (sourceB1522 + difference 0 5) sourceC1522) = raw21157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21157; decide +kernel
    rw [ha]
    exact (canonical21157 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 1) (sourceB1522 + difference 1 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 1) (sourceB1522 + difference 1 5) sourceC1522) = raw21158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21158; decide +kernel
    rw [ha]
    exact (canonical21158 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 2) (sourceB1522 + difference 2 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 2) (sourceB1522 + difference 2 5) sourceC1522) = raw21159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21159; decide +kernel
    rw [ha]
    exact (canonical21159 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 3) (sourceB1522 + difference 3 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 3) (sourceB1522 + difference 3 5) sourceC1522) = raw21160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21160; decide +kernel
    rw [ha]
    exact (canonical21160 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 4) (sourceB1522 + difference 4 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 4) (sourceB1522 + difference 4 5) sourceC1522) = raw11423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11423; decide +kernel
    rw [ha]
    exact (canonical11423 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1522 sourceB1522 sourceC1522
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1522, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1523 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1523 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1523 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1523 : Integer.Sparse Master := [(Sum.inr 632, 2), (Sum.inr 635, 2), (Sum.inr 649, 1), (Sum.inr 1322, 2), (Sum.inr 1324, 2), (Sum.inr 1331, 2), (Sum.inr 1333, 4), (Sum.inr 1344, 2), (Sum.inr 1411, 4), (Sum.inr 1413, 2), (Sum.inr 1447, 2), (Sum.inr 3188, 1), (Sum.inr 3207, 2), (Sum.inr 3229, 2)]

theorem sourceEq1523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1523 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1523 + difference 0 1) (sourceB1523 + difference 1 0) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3188) := by
    have ha : (tripleCharges (sourceA1523 + difference 0 1) (sourceB1523 + difference 1 0) sourceC1523) = raw23166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23166; decide +kernel
    rw [ha]
    exact (canonical23166 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1523 + difference 0 2) (sourceB1523 + difference 2 0) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3207) := by
    have ha : (tripleCharges (sourceA1523 + difference 0 2) (sourceB1523 + difference 2 0) sourceC1523) = raw23167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23167; decide +kernel
    rw [ha]
    exact (canonical23167 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1523 + difference 0 3) (sourceB1523 + difference 3 0) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3207) := by
    have ha : (tripleCharges (sourceA1523 + difference 0 3) (sourceB1523 + difference 3 0) sourceC1523) = raw23168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23168; decide +kernel
    rw [ha]
    exact (canonical23168 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1523 + difference 0 4) (sourceB1523 + difference 4 0) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA1523 + difference 0 4) (sourceB1523 + difference 4 0) sourceC1523) = raw21170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw21170; decide +kernel
    rw [ha]
    exact (canonical21170 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1523 + difference 0 5) (sourceB1523 + difference 5 0) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA1523 + difference 0 5) (sourceB1523 + difference 5 0) sourceC1523) = raw23169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23169; decide +kernel
    rw [ha]
    exact (canonical23169 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1523 + difference 1 0) (sourceB1523 + difference 0 1) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 649) := by
    have ha : (tripleCharges (sourceA1523 + difference 1 0) (sourceB1523 + difference 0 1) sourceC1523) = raw23170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23170; decide +kernel
    rw [ha]
    exact (canonical23170 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1523 + difference 1 2) (sourceB1523 + difference 2 1) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1344) := by
    have ha : (tripleCharges (sourceA1523 + difference 1 2) (sourceB1523 + difference 2 1) sourceC1523) = raw23171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23171; decide +kernel
    rw [ha]
    exact (canonical23171 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1523 + difference 1 3) (sourceB1523 + difference 3 1) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1344) := by
    have ha : (tripleCharges (sourceA1523 + difference 1 3) (sourceB1523 + difference 3 1) sourceC1523) = raw23172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23172; decide +kernel
    rw [ha]
    exact (canonical23172 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1523 + difference 1 4) (sourceB1523 + difference 4 1) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1447) := by
    have ha : (tripleCharges (sourceA1523 + difference 1 4) (sourceB1523 + difference 4 1) sourceC1523) = raw21175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw21175; decide +kernel
    rw [ha]
    exact (canonical21175 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1523 + difference 1 5) (sourceB1523 + difference 5 1) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1447) := by
    have ha : (tripleCharges (sourceA1523 + difference 1 5) (sourceB1523 + difference 5 1) sourceC1523) = raw23173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23173; decide +kernel
    rw [ha]
    exact (canonical23173 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1523 + difference 2 0) (sourceB1523 + difference 0 2) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 632) := by
    have ha : (tripleCharges (sourceA1523 + difference 2 0) (sourceB1523 + difference 0 2) sourceC1523) = raw23174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23174; decide +kernel
    rw [ha]
    exact (canonical23174 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1523 + difference 2 1) (sourceB1523 + difference 1 2) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA1523 + difference 2 1) (sourceB1523 + difference 1 2) sourceC1523) = raw23175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23175; decide +kernel
    rw [ha]
    exact (canonical23175 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1523 + difference 2 3) (sourceB1523 + difference 3 2) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1331) := by
    have ha : (tripleCharges (sourceA1523 + difference 2 3) (sourceB1523 + difference 3 2) sourceC1523) = raw23176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23176; decide +kernel
    rw [ha]
    exact (canonical23176 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1523 + difference 2 4) (sourceB1523 + difference 4 2) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1523 + difference 2 4) (sourceB1523 + difference 4 2) sourceC1523) = raw21180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw21180; decide +kernel
    rw [ha]
    exact (canonical21180 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1523 + difference 2 5) (sourceB1523 + difference 5 2) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1523 + difference 2 5) (sourceB1523 + difference 5 2) sourceC1523) = raw23177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23177; decide +kernel
    rw [ha]
    exact (canonical23177 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1523 + difference 3 0) (sourceB1523 + difference 0 3) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 632) := by
    have ha : (tripleCharges (sourceA1523 + difference 3 0) (sourceB1523 + difference 0 3) sourceC1523) = raw23178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23178; decide +kernel
    rw [ha]
    exact (canonical23178 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1523 + difference 3 1) (sourceB1523 + difference 1 3) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA1523 + difference 3 1) (sourceB1523 + difference 1 3) sourceC1523) = raw23179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23179; decide +kernel
    rw [ha]
    exact (canonical23179 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1523 + difference 3 2) (sourceB1523 + difference 2 3) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1331) := by
    have ha : (tripleCharges (sourceA1523 + difference 3 2) (sourceB1523 + difference 2 3) sourceC1523) = raw23180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23180; decide +kernel
    rw [ha]
    exact (canonical23180 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1523 + difference 3 4) (sourceB1523 + difference 4 3) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1523 + difference 3 4) (sourceB1523 + difference 4 3) sourceC1523) = raw21185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw21185; decide +kernel
    rw [ha]
    exact (canonical21185 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1523 + difference 3 5) (sourceB1523 + difference 5 3) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1523 + difference 3 5) (sourceB1523 + difference 5 3) sourceC1523) = raw23181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23181; decide +kernel
    rw [ha]
    exact (canonical23181 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1523 + difference 4 0) (sourceB1523 + difference 0 4) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 635) := by
    have ha : (tripleCharges (sourceA1523 + difference 4 0) (sourceB1523 + difference 0 4) sourceC1523) = raw23182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23182; decide +kernel
    rw [ha]
    exact (canonical23182 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1523 + difference 4 1) (sourceB1523 + difference 1 4) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1324) := by
    have ha : (tripleCharges (sourceA1523 + difference 4 1) (sourceB1523 + difference 1 4) sourceC1523) = raw23183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23183; decide +kernel
    rw [ha]
    exact (canonical23183 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1523 + difference 4 2) (sourceB1523 + difference 2 4) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1523 + difference 4 2) (sourceB1523 + difference 2 4) sourceC1523) = raw23184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23184; decide +kernel
    rw [ha]
    exact (canonical23184 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1523 + difference 4 3) (sourceB1523 + difference 3 4) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1523 + difference 4 3) (sourceB1523 + difference 3 4) sourceC1523) = raw23185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23185; decide +kernel
    rw [ha]
    exact (canonical23185 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1523 + difference 4 5) (sourceB1523 + difference 5 4) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1523 + difference 4 5) (sourceB1523 + difference 5 4) sourceC1523) = raw23186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23186; decide +kernel
    rw [ha]
    exact (canonical23186 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1523 + difference 5 0) (sourceB1523 + difference 0 5) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 635) := by
    have ha : (tripleCharges (sourceA1523 + difference 5 0) (sourceB1523 + difference 0 5) sourceC1523) = raw21186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw21186; decide +kernel
    rw [ha]
    exact (canonical21186 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1523 + difference 5 1) (sourceB1523 + difference 1 5) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1324) := by
    have ha : (tripleCharges (sourceA1523 + difference 5 1) (sourceB1523 + difference 1 5) sourceC1523) = raw21187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw21187; decide +kernel
    rw [ha]
    exact (canonical21187 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1523 + difference 5 2) (sourceB1523 + difference 2 5) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1523 + difference 5 2) (sourceB1523 + difference 2 5) sourceC1523) = raw21188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw21188; decide +kernel
    rw [ha]
    exact (canonical21188 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1523 + difference 5 3) (sourceB1523 + difference 3 5) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1523 + difference 5 3) (sourceB1523 + difference 3 5) sourceC1523) = raw21189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw21189; decide +kernel
    rw [ha]
    exact (canonical21189 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1523 + difference 5 4) (sourceB1523 + difference 4 5) sourceC1523) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1523 + difference 5 4) (sourceB1523 + difference 4 5) sourceC1523) = raw23187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1523 sourceB1523 sourceC1523 difference raw23187; decide +kernel
    rw [ha]
    exact (canonical23187 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1523 sourceB1523 sourceC1523
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1523, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1524 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1524 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1524 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1524 : Integer.Sparse Master := [(Sum.inr 1515, 2), (Sum.inr 1533, 2), (Sum.inr 1536, 1), (Sum.inr 1671, 2), (Sum.inr 1689, 4), (Sum.inr 1691, 2), (Sum.inr 1721, 2), (Sum.inr 1724, 4), (Sum.inr 1748, 2), (Sum.inr 1750, 2), (Sum.inr 1753, 2), (Sum.inr 2225, 2), (Sum.inr 2288, 1), (Sum.inr 2291, 2)]

theorem sourceEq1524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1524 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 1) (sourceB1524 + difference 1 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 1) (sourceB1524 + difference 1 0) sourceC1524) = raw11449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11449; decide +kernel
    rw [ha]
    exact (canonical11449 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 2) (sourceB1524 + difference 2 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 2) (sourceB1524 + difference 2 0) sourceC1524) = raw11450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11450; decide +kernel
    rw [ha]
    exact (canonical11450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 3) (sourceB1524 + difference 3 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 3) (sourceB1524 + difference 3 0) sourceC1524) = raw11451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11451; decide +kernel
    rw [ha]
    exact (canonical11451 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 4) (sourceB1524 + difference 4 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 4) (sourceB1524 + difference 4 0) sourceC1524) = raw21196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21196; decide +kernel
    rw [ha]
    exact (canonical21196 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 5) (sourceB1524 + difference 5 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 5) (sourceB1524 + difference 5 0) sourceC1524) = raw11452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11452; decide +kernel
    rw [ha]
    exact (canonical11452 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 0) (sourceB1524 + difference 0 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 0) (sourceB1524 + difference 0 1) sourceC1524) = raw23188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23188; decide +kernel
    rw [ha]
    exact (canonical23188 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 2) (sourceB1524 + difference 2 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1691) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 2) (sourceB1524 + difference 2 1) sourceC1524) = raw23189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23189; decide +kernel
    rw [ha]
    exact (canonical23189 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 3) (sourceB1524 + difference 3 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1691) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 3) (sourceB1524 + difference 3 1) sourceC1524) = raw23190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23190; decide +kernel
    rw [ha]
    exact (canonical23190 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 4) (sourceB1524 + difference 4 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 4) (sourceB1524 + difference 4 1) sourceC1524) = raw11433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11433; decide +kernel
    rw [ha]
    exact (canonical11433 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 5) (sourceB1524 + difference 5 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 5) (sourceB1524 + difference 5 1) sourceC1524) = raw23191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23191; decide +kernel
    rw [ha]
    exact (canonical23191 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 0) (sourceB1524 + difference 0 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 0) (sourceB1524 + difference 0 2) sourceC1524) = raw23192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23192; decide +kernel
    rw [ha]
    exact (canonical23192 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 1) (sourceB1524 + difference 1 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 1) (sourceB1524 + difference 1 2) sourceC1524) = raw23193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23193; decide +kernel
    rw [ha]
    exact (canonical23193 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 3) (sourceB1524 + difference 3 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 3) (sourceB1524 + difference 3 2) sourceC1524) = raw23194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23194; decide +kernel
    rw [ha]
    exact (canonical23194 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 4) (sourceB1524 + difference 4 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 4) (sourceB1524 + difference 4 2) sourceC1524) = raw11438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11438; decide +kernel
    rw [ha]
    exact (canonical11438 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 5) (sourceB1524 + difference 5 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 5) (sourceB1524 + difference 5 2) sourceC1524) = raw23195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23195; decide +kernel
    rw [ha]
    exact (canonical23195 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 0) (sourceB1524 + difference 0 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 0) (sourceB1524 + difference 0 3) sourceC1524) = raw23196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23196; decide +kernel
    rw [ha]
    exact (canonical23196 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 1) (sourceB1524 + difference 1 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 1) (sourceB1524 + difference 1 3) sourceC1524) = raw23197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23197; decide +kernel
    rw [ha]
    exact (canonical23197 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 2) (sourceB1524 + difference 2 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 2) (sourceB1524 + difference 2 3) sourceC1524) = raw23198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23198; decide +kernel
    rw [ha]
    exact (canonical23198 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 4) (sourceB1524 + difference 4 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 4) (sourceB1524 + difference 4 3) sourceC1524) = raw11443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11443; decide +kernel
    rw [ha]
    exact (canonical11443 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 5) (sourceB1524 + difference 5 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 5) (sourceB1524 + difference 5 3) sourceC1524) = raw23199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23199; decide +kernel
    rw [ha]
    exact (canonical23199 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 0) (sourceB1524 + difference 0 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 0) (sourceB1524 + difference 0 4) sourceC1524) = raw23200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23200; decide +kernel
    rw [ha]
    exact (canonical23200 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 1) (sourceB1524 + difference 1 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 1) (sourceB1524 + difference 1 4) sourceC1524) = raw23201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23201; decide +kernel
    rw [ha]
    exact (canonical23201 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 2) (sourceB1524 + difference 2 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 2) (sourceB1524 + difference 2 4) sourceC1524) = raw23202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23202; decide +kernel
    rw [ha]
    exact (canonical23202 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 3) (sourceB1524 + difference 3 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 3) (sourceB1524 + difference 3 4) sourceC1524) = raw23203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23203; decide +kernel
    rw [ha]
    exact (canonical23203 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 5) (sourceB1524 + difference 5 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 5) (sourceB1524 + difference 5 4) sourceC1524) = raw23204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23204; decide +kernel
    rw [ha]
    exact (canonical23204 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 0) (sourceB1524 + difference 0 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 0) (sourceB1524 + difference 0 5) sourceC1524) = raw21209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21209; decide +kernel
    rw [ha]
    exact (canonical21209 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 1) (sourceB1524 + difference 1 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 1) (sourceB1524 + difference 1 5) sourceC1524) = raw21210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21210; decide +kernel
    rw [ha]
    exact (canonical21210 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 2) (sourceB1524 + difference 2 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 2) (sourceB1524 + difference 2 5) sourceC1524) = raw21211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21211; decide +kernel
    rw [ha]
    exact (canonical21211 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 3) (sourceB1524 + difference 3 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 3) (sourceB1524 + difference 3 5) sourceC1524) = raw21212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21212; decide +kernel
    rw [ha]
    exact (canonical21212 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 4) (sourceB1524 + difference 4 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 4) (sourceB1524 + difference 4 5) sourceC1524) = raw11453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11453; decide +kernel
    rw [ha]
    exact (canonical11453 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1524 sourceB1524 sourceC1524
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1524, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1525 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1525 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1525 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1525 : Integer.Sparse Master := [(Sum.inr 583, 2), (Sum.inr 589, 2), (Sum.inr 614, 1), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

theorem sourceEq1525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1525 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1525 + difference 0 0) (sourceB1525 + difference 0 0) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1525 + difference 0 0) (sourceB1525 + difference 0 0) sourceC1525) = raw23205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23205; decide +kernel
    rw [ha]
    exact (canonical23205 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1525 + difference 1 0) (sourceB1525 + difference 0 1) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 614) := by
    have ha : (tripleCharges (sourceA1525 + difference 1 0) (sourceB1525 + difference 0 1) sourceC1525) = raw23206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23206; decide +kernel
    rw [ha]
    exact (canonical23206 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1525 + difference 2 0) (sourceB1525 + difference 0 2) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1525 + difference 2 0) (sourceB1525 + difference 0 2) sourceC1525) = raw23207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23207; decide +kernel
    rw [ha]
    exact (canonical23207 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1525 + difference 3 0) (sourceB1525 + difference 0 3) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1525 + difference 3 0) (sourceB1525 + difference 0 3) sourceC1525) = raw23208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23208; decide +kernel
    rw [ha]
    exact (canonical23208 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1525 + difference 4 0) (sourceB1525 + difference 0 4) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 589) := by
    have ha : (tripleCharges (sourceA1525 + difference 4 0) (sourceB1525 + difference 0 4) sourceC1525) = raw23209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23209; decide +kernel
    rw [ha]
    exact (canonical23209 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1525 + difference 5 0) (sourceB1525 + difference 0 5) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 589) := by
    have ha : (tripleCharges (sourceA1525 + difference 5 0) (sourceB1525 + difference 0 5) sourceC1525) = raw21222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw21222; decide +kernel
    rw [ha]
    exact (canonical21222 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1525 + sourceB1525) sourceC1525) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1525 + sourceB1525) sourceC1525) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1525 sourceB1525 sourceC1525 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1525 sourceB1525 sourceC1525
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1525, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1526 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1526 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1526 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1526 : Integer.Sparse Master := [(Sum.inr 614, 1), (Sum.inr 933, 2), (Sum.inr 1050, 1), (Sum.inr 1086, 2), (Sum.inr 4083, -1)]

theorem sourceEq1526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1526 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 0) (sourceB1526 + difference 0 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 614) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 0) (sourceB1526 + difference 0 1) sourceC1526) = raw23206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23206; decide +kernel
    rw [ha]
    exact (canonical23206 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 1) (sourceB1526 + difference 1 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 1) (sourceB1526 + difference 1 1) sourceC1526) = raw23205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23205; decide +kernel
    rw [ha]
    exact (canonical23205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 2) (sourceB1526 + difference 2 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 2) (sourceB1526 + difference 2 1) sourceC1526) = raw23210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23210; decide +kernel
    rw [ha]
    exact (canonical23210 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 3) (sourceB1526 + difference 3 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 3) (sourceB1526 + difference 3 1) sourceC1526) = raw23211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23211; decide +kernel
    rw [ha]
    exact (canonical23211 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 4) (sourceB1526 + difference 4 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 4) (sourceB1526 + difference 4 1) sourceC1526) = raw21227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw21227; decide +kernel
    rw [ha]
    exact (canonical21227 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 5) (sourceB1526 + difference 5 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 5) (sourceB1526 + difference 5 1) sourceC1526) = raw23212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23212; decide +kernel
    rw [ha]
    exact (canonical23212 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1526 + sourceB1526) sourceC1526) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1526 + sourceB1526) sourceC1526) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1526 sourceB1526 sourceC1526 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1526 sourceB1526 sourceC1526
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1526, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1527 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1527 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1527 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1527 : Integer.Sparse Master := [(Sum.inr 947, 2), (Sum.inr 953, 2), (Sum.inr 1050, 1), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

theorem sourceEq1527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1527 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1527 + difference 0 1) (sourceB1527 + difference 1 0) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA1527 + difference 0 1) (sourceB1527 + difference 1 0) sourceC1527) = raw11462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw11462; decide +kernel
    rw [ha]
    exact (canonical11462 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1527 + difference 1 1) (sourceB1527 + difference 1 1) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1527 + difference 1 1) (sourceB1527 + difference 1 1) sourceC1527) = raw23205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw23205; decide +kernel
    rw [ha]
    exact (canonical23205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1527 + difference 2 1) (sourceB1527 + difference 1 2) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA1527 + difference 2 1) (sourceB1527 + difference 1 2) sourceC1527) = raw23213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw23213; decide +kernel
    rw [ha]
    exact (canonical23213 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1527 + difference 3 1) (sourceB1527 + difference 1 3) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA1527 + difference 3 1) (sourceB1527 + difference 1 3) sourceC1527) = raw23214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw23214; decide +kernel
    rw [ha]
    exact (canonical23214 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1527 + difference 4 1) (sourceB1527 + difference 1 4) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 953) := by
    have ha : (tripleCharges (sourceA1527 + difference 4 1) (sourceB1527 + difference 1 4) sourceC1527) = raw23215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw23215; decide +kernel
    rw [ha]
    exact (canonical23215 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1527 + difference 5 1) (sourceB1527 + difference 1 5) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 953) := by
    have ha : (tripleCharges (sourceA1527 + difference 5 1) (sourceB1527 + difference 1 5) sourceC1527) = raw21230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw21230; decide +kernel
    rw [ha]
    exact (canonical21230 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1527 + sourceB1527) sourceC1527) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1527 + sourceB1527) sourceC1527) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1527 sourceB1527 sourceC1527 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1527 sourceB1527 sourceC1527
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1527, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1528 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1528 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1528 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm1528 : Integer.Sparse Master := [(Sum.inr 583, 1), (Sum.inr 907, 1), (Sum.inr 947, 1), (Sum.inr 1041, 2), (Sum.inr 1050, 1), (Sum.inr 4083, -1)]

theorem sourceEq1528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1528 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 0) (sourceB1528 + difference 0 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 0) (sourceB1528 + difference 0 2) sourceC1528) = raw23207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23207; decide +kernel
    rw [ha]
    exact (canonical23207 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 1) (sourceB1528 + difference 1 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 1) (sourceB1528 + difference 1 2) sourceC1528) = raw23213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23213; decide +kernel
    rw [ha]
    exact (canonical23213 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 2) (sourceB1528 + difference 2 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 2) (sourceB1528 + difference 2 2) sourceC1528) = raw23205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23205; decide +kernel
    rw [ha]
    exact (canonical23205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 3) (sourceB1528 + difference 3 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 907) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 3) (sourceB1528 + difference 3 2) sourceC1528) = raw23216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23216; decide +kernel
    rw [ha]
    exact (canonical23216 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 4) (sourceB1528 + difference 4 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 4) (sourceB1528 + difference 4 2) sourceC1528) = raw23217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23217; decide +kernel
    rw [ha]
    exact (canonical23217 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 5) (sourceB1528 + difference 5 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 5) (sourceB1528 + difference 5 2) sourceC1528) = raw23218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23218; decide +kernel
    rw [ha]
    exact (canonical23218 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1528 + sourceB1528) sourceC1528) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1528 + sourceB1528) sourceC1528) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1528 sourceB1528 sourceC1528 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1528 sourceB1528 sourceC1528
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1528, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1529 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1529 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1529 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1529 : Integer.Sparse Master := [(Sum.inr 4107, 2), (Sum.inr 4110, 2), (Sum.inr 4133, 1), (Sum.inr 4292, 2), (Sum.inr 4295, 4), (Sum.inr 4314, 2), (Sum.inr 4355, 2), (Sum.inr 4360, 2), (Sum.inr 4458, 4), (Sum.inr 4460, 2), (Sum.inr 4499, 2), (Sum.inr 5081, 2), (Sum.inr 5177, 1), (Sum.inr 5293, 2)]

theorem sourceEq1529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1529 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 1) (sourceB1529 + difference 1 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 1) (sourceB1529 + difference 1 0) sourceC1529) = raw17675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw17675; decide +kernel
    rw [ha]
    exact (canonical17675 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 2) (sourceB1529 + difference 2 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 2) (sourceB1529 + difference 2 0) sourceC1529) = raw23219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23219; decide +kernel
    rw [ha]
    exact (canonical23219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 3) (sourceB1529 + difference 3 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 3) (sourceB1529 + difference 3 0) sourceC1529) = raw23220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23220; decide +kernel
    rw [ha]
    exact (canonical23220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 4) (sourceB1529 + difference 4 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 4) (sourceB1529 + difference 4 0) sourceC1529) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 5) (sourceB1529 + difference 5 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 5) (sourceB1529 + difference 5 0) sourceC1529) = raw23221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23221; decide +kernel
    rw [ha]
    exact (canonical23221 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 0) (sourceB1529 + difference 0 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4133) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 0) (sourceB1529 + difference 0 1) sourceC1529) = raw23222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23222; decide +kernel
    rw [ha]
    exact (canonical23222 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 2) (sourceB1529 + difference 2 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4314) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 2) (sourceB1529 + difference 2 1) sourceC1529) = raw23223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23223; decide +kernel
    rw [ha]
    exact (canonical23223 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 3) (sourceB1529 + difference 3 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4314) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 3) (sourceB1529 + difference 3 1) sourceC1529) = raw23224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23224; decide +kernel
    rw [ha]
    exact (canonical23224 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 4) (sourceB1529 + difference 4 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 4) (sourceB1529 + difference 4 1) sourceC1529) = raw21481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21481; decide +kernel
    rw [ha]
    exact (canonical21481 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 5) (sourceB1529 + difference 5 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 5) (sourceB1529 + difference 5 1) sourceC1529) = raw23225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23225; decide +kernel
    rw [ha]
    exact (canonical23225 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 0) (sourceB1529 + difference 0 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 0) (sourceB1529 + difference 0 2) sourceC1529) = raw23226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23226; decide +kernel
    rw [ha]
    exact (canonical23226 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 1) (sourceB1529 + difference 1 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 1) (sourceB1529 + difference 1 2) sourceC1529) = raw23227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23227; decide +kernel
    rw [ha]
    exact (canonical23227 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 3) (sourceB1529 + difference 3 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4292) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 3) (sourceB1529 + difference 3 2) sourceC1529) = raw23228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23228; decide +kernel
    rw [ha]
    exact (canonical23228 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 4) (sourceB1529 + difference 4 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 4) (sourceB1529 + difference 4 2) sourceC1529) = raw21485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21485; decide +kernel
    rw [ha]
    exact (canonical21485 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 5) (sourceB1529 + difference 5 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 5) (sourceB1529 + difference 5 2) sourceC1529) = raw23229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23229; decide +kernel
    rw [ha]
    exact (canonical23229 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 0) (sourceB1529 + difference 0 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 0) (sourceB1529 + difference 0 3) sourceC1529) = raw23230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23230; decide +kernel
    rw [ha]
    exact (canonical23230 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 1) (sourceB1529 + difference 1 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 1) (sourceB1529 + difference 1 3) sourceC1529) = raw23231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23231; decide +kernel
    rw [ha]
    exact (canonical23231 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 2) (sourceB1529 + difference 2 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4292) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 2) (sourceB1529 + difference 2 3) sourceC1529) = raw23232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23232; decide +kernel
    rw [ha]
    exact (canonical23232 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 4) (sourceB1529 + difference 4 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 4) (sourceB1529 + difference 4 3) sourceC1529) = raw21489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21489; decide +kernel
    rw [ha]
    exact (canonical21489 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 5) (sourceB1529 + difference 5 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 5) (sourceB1529 + difference 5 3) sourceC1529) = raw23233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23233; decide +kernel
    rw [ha]
    exact (canonical23233 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 0) (sourceB1529 + difference 0 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4110) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 0) (sourceB1529 + difference 0 4) sourceC1529) = raw23234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23234; decide +kernel
    rw [ha]
    exact (canonical23234 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 1) (sourceB1529 + difference 1 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 1) (sourceB1529 + difference 1 4) sourceC1529) = raw23235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23235; decide +kernel
    rw [ha]
    exact (canonical23235 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 2) (sourceB1529 + difference 2 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 2) (sourceB1529 + difference 2 4) sourceC1529) = raw23236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23236; decide +kernel
    rw [ha]
    exact (canonical23236 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 3) (sourceB1529 + difference 3 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 3) (sourceB1529 + difference 3 4) sourceC1529) = raw23237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23237; decide +kernel
    rw [ha]
    exact (canonical23237 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 5) (sourceB1529 + difference 5 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 5) (sourceB1529 + difference 5 4) sourceC1529) = raw23238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23238; decide +kernel
    rw [ha]
    exact (canonical23238 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 0) (sourceB1529 + difference 0 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4110) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 0) (sourceB1529 + difference 0 5) sourceC1529) = raw21490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21490; decide +kernel
    rw [ha]
    exact (canonical21490 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 1) (sourceB1529 + difference 1 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 1) (sourceB1529 + difference 1 5) sourceC1529) = raw21491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21491; decide +kernel
    rw [ha]
    exact (canonical21491 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 2) (sourceB1529 + difference 2 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 2) (sourceB1529 + difference 2 5) sourceC1529) = raw21492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21492; decide +kernel
    rw [ha]
    exact (canonical21492 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 3) (sourceB1529 + difference 3 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 3) (sourceB1529 + difference 3 5) sourceC1529) = raw21493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21493; decide +kernel
    rw [ha]
    exact (canonical21493 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 4) (sourceB1529 + difference 4 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 4) (sourceB1529 + difference 4 5) sourceC1529) = raw4935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw4935; decide +kernel
    rw [ha]
    exact (canonical4935 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1529 sourceB1529 sourceC1529
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1529, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1530 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1530 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1530 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1530 : Integer.Sparse Master := [(Sum.inr 544, 2), (Sum.inr 547, 2), (Sum.inr 563, 1), (Sum.inr 870, 2), (Sum.inr 873, 4), (Sum.inr 892, 2), (Sum.inr 933, 2), (Sum.inr 938, 2), (Sum.inr 1041, 4), (Sum.inr 1043, 2), (Sum.inr 1083, 2), (Sum.inr 2489, 2), (Sum.inr 2605, 1), (Sum.inr 2767, 2)]

theorem sourceEq1530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1530 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1530 + difference 0 1) (sourceB1530 + difference 1 0) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA1530 + difference 0 1) (sourceB1530 + difference 1 0) sourceC1530) = raw23239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23239; decide +kernel
    rw [ha]
    exact (canonical23239 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1530 + difference 0 2) (sourceB1530 + difference 2 0) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA1530 + difference 0 2) (sourceB1530 + difference 2 0) sourceC1530) = raw23240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23240; decide +kernel
    rw [ha]
    exact (canonical23240 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1530 + difference 0 3) (sourceB1530 + difference 3 0) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA1530 + difference 0 3) (sourceB1530 + difference 3 0) sourceC1530) = raw23241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23241; decide +kernel
    rw [ha]
    exact (canonical23241 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1530 + difference 0 4) (sourceB1530 + difference 4 0) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA1530 + difference 0 4) (sourceB1530 + difference 4 0) sourceC1530) = raw2801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw2801; decide +kernel
    rw [ha]
    exact (canonical2801 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1530 + difference 0 5) (sourceB1530 + difference 5 0) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA1530 + difference 0 5) (sourceB1530 + difference 5 0) sourceC1530) = raw23242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23242; decide +kernel
    rw [ha]
    exact (canonical23242 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1530 + difference 1 0) (sourceB1530 + difference 0 1) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 563) := by
    have ha : (tripleCharges (sourceA1530 + difference 1 0) (sourceB1530 + difference 0 1) sourceC1530) = raw23243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23243; decide +kernel
    rw [ha]
    exact (canonical23243 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1530 + difference 1 2) (sourceB1530 + difference 2 1) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 892) := by
    have ha : (tripleCharges (sourceA1530 + difference 1 2) (sourceB1530 + difference 2 1) sourceC1530) = raw23244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23244; decide +kernel
    rw [ha]
    exact (canonical23244 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1530 + difference 1 3) (sourceB1530 + difference 3 1) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 892) := by
    have ha : (tripleCharges (sourceA1530 + difference 1 3) (sourceB1530 + difference 3 1) sourceC1530) = raw23245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23245; decide +kernel
    rw [ha]
    exact (canonical23245 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1530 + difference 1 4) (sourceB1530 + difference 4 1) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1530 + difference 1 4) (sourceB1530 + difference 4 1) sourceC1530) = raw21502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw21502; decide +kernel
    rw [ha]
    exact (canonical21502 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1530 + difference 1 5) (sourceB1530 + difference 5 1) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1530 + difference 1 5) (sourceB1530 + difference 5 1) sourceC1530) = raw23246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23246; decide +kernel
    rw [ha]
    exact (canonical23246 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1530 + difference 2 0) (sourceB1530 + difference 0 2) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 544) := by
    have ha : (tripleCharges (sourceA1530 + difference 2 0) (sourceB1530 + difference 0 2) sourceC1530) = raw23247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23247; decide +kernel
    rw [ha]
    exact (canonical23247 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1530 + difference 2 1) (sourceB1530 + difference 1 2) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA1530 + difference 2 1) (sourceB1530 + difference 1 2) sourceC1530) = raw23248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23248; decide +kernel
    rw [ha]
    exact (canonical23248 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1530 + difference 2 3) (sourceB1530 + difference 3 2) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 870) := by
    have ha : (tripleCharges (sourceA1530 + difference 2 3) (sourceB1530 + difference 3 2) sourceC1530) = raw23249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23249; decide +kernel
    rw [ha]
    exact (canonical23249 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1530 + difference 2 4) (sourceB1530 + difference 4 2) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1530 + difference 2 4) (sourceB1530 + difference 4 2) sourceC1530) = raw21506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw21506; decide +kernel
    rw [ha]
    exact (canonical21506 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1530 + difference 2 5) (sourceB1530 + difference 5 2) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1530 + difference 2 5) (sourceB1530 + difference 5 2) sourceC1530) = raw23250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23250; decide +kernel
    rw [ha]
    exact (canonical23250 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1530 + difference 3 0) (sourceB1530 + difference 0 3) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 544) := by
    have ha : (tripleCharges (sourceA1530 + difference 3 0) (sourceB1530 + difference 0 3) sourceC1530) = raw23251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23251; decide +kernel
    rw [ha]
    exact (canonical23251 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1530 + difference 3 1) (sourceB1530 + difference 1 3) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA1530 + difference 3 1) (sourceB1530 + difference 1 3) sourceC1530) = raw23252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23252; decide +kernel
    rw [ha]
    exact (canonical23252 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1530 + difference 3 2) (sourceB1530 + difference 2 3) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 870) := by
    have ha : (tripleCharges (sourceA1530 + difference 3 2) (sourceB1530 + difference 2 3) sourceC1530) = raw23253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23253; decide +kernel
    rw [ha]
    exact (canonical23253 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1530 + difference 3 4) (sourceB1530 + difference 4 3) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1530 + difference 3 4) (sourceB1530 + difference 4 3) sourceC1530) = raw21510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw21510; decide +kernel
    rw [ha]
    exact (canonical21510 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1530 + difference 3 5) (sourceB1530 + difference 5 3) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1530 + difference 3 5) (sourceB1530 + difference 5 3) sourceC1530) = raw23254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23254; decide +kernel
    rw [ha]
    exact (canonical23254 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1530 + difference 4 0) (sourceB1530 + difference 0 4) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 547) := by
    have ha : (tripleCharges (sourceA1530 + difference 4 0) (sourceB1530 + difference 0 4) sourceC1530) = raw23255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23255; decide +kernel
    rw [ha]
    exact (canonical23255 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1530 + difference 4 1) (sourceB1530 + difference 1 4) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 938) := by
    have ha : (tripleCharges (sourceA1530 + difference 4 1) (sourceB1530 + difference 1 4) sourceC1530) = raw23256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23256; decide +kernel
    rw [ha]
    exact (canonical23256 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1530 + difference 4 2) (sourceB1530 + difference 2 4) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA1530 + difference 4 2) (sourceB1530 + difference 2 4) sourceC1530) = raw23257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23257; decide +kernel
    rw [ha]
    exact (canonical23257 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1530 + difference 4 3) (sourceB1530 + difference 3 4) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA1530 + difference 4 3) (sourceB1530 + difference 3 4) sourceC1530) = raw23258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23258; decide +kernel
    rw [ha]
    exact (canonical23258 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1530 + difference 4 5) (sourceB1530 + difference 5 4) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1530 + difference 4 5) (sourceB1530 + difference 5 4) sourceC1530) = raw23259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw23259; decide +kernel
    rw [ha]
    exact (canonical23259 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1530 + difference 5 0) (sourceB1530 + difference 0 5) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 547) := by
    have ha : (tripleCharges (sourceA1530 + difference 5 0) (sourceB1530 + difference 0 5) sourceC1530) = raw21511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw21511; decide +kernel
    rw [ha]
    exact (canonical21511 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1530 + difference 5 1) (sourceB1530 + difference 1 5) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 938) := by
    have ha : (tripleCharges (sourceA1530 + difference 5 1) (sourceB1530 + difference 1 5) sourceC1530) = raw21512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw21512; decide +kernel
    rw [ha]
    exact (canonical21512 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1530 + difference 5 2) (sourceB1530 + difference 2 5) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA1530 + difference 5 2) (sourceB1530 + difference 2 5) sourceC1530) = raw21513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw21513; decide +kernel
    rw [ha]
    exact (canonical21513 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1530 + difference 5 3) (sourceB1530 + difference 3 5) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA1530 + difference 5 3) (sourceB1530 + difference 3 5) sourceC1530) = raw21514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw21514; decide +kernel
    rw [ha]
    exact (canonical21514 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1530 + difference 5 4) (sourceB1530 + difference 4 5) sourceC1530) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1530 + difference 5 4) (sourceB1530 + difference 4 5) sourceC1530) = raw4957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1530 sourceB1530 sourceC1530 difference raw4957; decide +kernel
    rw [ha]
    exact (canonical4957 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1530 sourceB1530 sourceC1530
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1530, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1531 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1531 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1531 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1531 : Integer.Sparse Master := [(Sum.inr 4256, 2), (Sum.inr 4273, 2), (Sum.inr 4279, 1), (Sum.inr 4393, 2), (Sum.inr 4404, 4), (Sum.inr 4412, 2), (Sum.inr 4444, 4), (Sum.inr 4466, 2), (Sum.inr 4467, 2), (Sum.inr 4480, 2), (Sum.inr 4511, 2), (Sum.inr 4593, 2), (Sum.inr 4612, 2), (Sum.inr 4628, 1)]

theorem sourceEq1531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1531 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1531 + difference 0 1) (sourceB1531 + difference 1 0) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA1531 + difference 0 1) (sourceB1531 + difference 1 0) sourceC1531) = raw22530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22530; decide +kernel
    rw [ha]
    exact (canonical22530 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1531 + difference 0 2) (sourceB1531 + difference 2 0) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1531 + difference 0 2) (sourceB1531 + difference 2 0) sourceC1531) = raw22612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22612; decide +kernel
    rw [ha]
    exact (canonical22612 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1531 + difference 0 3) (sourceB1531 + difference 3 0) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1531 + difference 0 3) (sourceB1531 + difference 3 0) sourceC1531) = raw22613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22613; decide +kernel
    rw [ha]
    exact (canonical22613 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1531 + difference 0 4) (sourceB1531 + difference 4 0) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1531 + difference 0 4) (sourceB1531 + difference 4 0) sourceC1531) = raw22515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22515; decide +kernel
    rw [ha]
    exact (canonical22515 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1531 + difference 0 5) (sourceB1531 + difference 5 0) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1531 + difference 0 5) (sourceB1531 + difference 5 0) sourceC1531) = raw22614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22614; decide +kernel
    rw [ha]
    exact (canonical22614 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1531 + difference 1 0) (sourceB1531 + difference 0 1) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4279) := by
    have ha : (tripleCharges (sourceA1531 + difference 1 0) (sourceB1531 + difference 0 1) sourceC1531) = raw23260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23260; decide +kernel
    rw [ha]
    exact (canonical23260 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1531 + difference 1 2) (sourceB1531 + difference 2 1) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4412) := by
    have ha : (tripleCharges (sourceA1531 + difference 1 2) (sourceB1531 + difference 2 1) sourceC1531) = raw23261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23261; decide +kernel
    rw [ha]
    exact (canonical23261 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1531 + difference 1 3) (sourceB1531 + difference 3 1) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4412) := by
    have ha : (tripleCharges (sourceA1531 + difference 1 3) (sourceB1531 + difference 3 1) sourceC1531) = raw23262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23262; decide +kernel
    rw [ha]
    exact (canonical23262 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1531 + difference 1 4) (sourceB1531 + difference 4 1) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA1531 + difference 1 4) (sourceB1531 + difference 4 1) sourceC1531) = raw23263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23263; decide +kernel
    rw [ha]
    exact (canonical23263 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1531 + difference 1 5) (sourceB1531 + difference 5 1) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA1531 + difference 1 5) (sourceB1531 + difference 5 1) sourceC1531) = raw23080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23080; decide +kernel
    rw [ha]
    exact (canonical23080 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1531 + difference 2 0) (sourceB1531 + difference 0 2) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1531 + difference 2 0) (sourceB1531 + difference 0 2) sourceC1531) = raw23264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23264; decide +kernel
    rw [ha]
    exact (canonical23264 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1531 + difference 2 1) (sourceB1531 + difference 1 2) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1531 + difference 2 1) (sourceB1531 + difference 1 2) sourceC1531) = raw22615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22615; decide +kernel
    rw [ha]
    exact (canonical22615 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1531 + difference 2 3) (sourceB1531 + difference 3 2) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4393) := by
    have ha : (tripleCharges (sourceA1531 + difference 2 3) (sourceB1531 + difference 3 2) sourceC1531) = raw23265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23265; decide +kernel
    rw [ha]
    exact (canonical23265 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1531 + difference 2 4) (sourceB1531 + difference 4 2) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1531 + difference 2 4) (sourceB1531 + difference 4 2) sourceC1531) = raw23266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23266; decide +kernel
    rw [ha]
    exact (canonical23266 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1531 + difference 2 5) (sourceB1531 + difference 5 2) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1531 + difference 2 5) (sourceB1531 + difference 5 2) sourceC1531) = raw23085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23085; decide +kernel
    rw [ha]
    exact (canonical23085 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1531 + difference 3 0) (sourceB1531 + difference 0 3) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1531 + difference 3 0) (sourceB1531 + difference 0 3) sourceC1531) = raw23267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23267; decide +kernel
    rw [ha]
    exact (canonical23267 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1531 + difference 3 1) (sourceB1531 + difference 1 3) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1531 + difference 3 1) (sourceB1531 + difference 1 3) sourceC1531) = raw22619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22619; decide +kernel
    rw [ha]
    exact (canonical22619 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1531 + difference 3 2) (sourceB1531 + difference 2 3) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4393) := by
    have ha : (tripleCharges (sourceA1531 + difference 3 2) (sourceB1531 + difference 2 3) sourceC1531) = raw23268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23268; decide +kernel
    rw [ha]
    exact (canonical23268 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1531 + difference 3 4) (sourceB1531 + difference 4 3) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1531 + difference 3 4) (sourceB1531 + difference 4 3) sourceC1531) = raw23269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23269; decide +kernel
    rw [ha]
    exact (canonical23269 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1531 + difference 3 5) (sourceB1531 + difference 5 3) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1531 + difference 3 5) (sourceB1531 + difference 5 3) sourceC1531) = raw23090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23090; decide +kernel
    rw [ha]
    exact (canonical23090 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1531 + difference 4 0) (sourceB1531 + difference 0 4) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1531 + difference 4 0) (sourceB1531 + difference 0 4) sourceC1531) = raw23097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23097; decide +kernel
    rw [ha]
    exact (canonical23097 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1531 + difference 4 1) (sourceB1531 + difference 1 4) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1531 + difference 4 1) (sourceB1531 + difference 1 4) sourceC1531) = raw22623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22623; decide +kernel
    rw [ha]
    exact (canonical22623 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1531 + difference 4 2) (sourceB1531 + difference 2 4) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1531 + difference 4 2) (sourceB1531 + difference 2 4) sourceC1531) = raw23098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23098; decide +kernel
    rw [ha]
    exact (canonical23098 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1531 + difference 4 3) (sourceB1531 + difference 3 4) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1531 + difference 4 3) (sourceB1531 + difference 3 4) sourceC1531) = raw22775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22775; decide +kernel
    rw [ha]
    exact (canonical22775 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1531 + difference 4 5) (sourceB1531 + difference 5 4) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1531 + difference 4 5) (sourceB1531 + difference 5 4) sourceC1531) = raw23270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23270; decide +kernel
    rw [ha]
    exact (canonical23270 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1531 + difference 5 0) (sourceB1531 + difference 0 5) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1531 + difference 5 0) (sourceB1531 + difference 0 5) sourceC1531) = raw23271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23271; decide +kernel
    rw [ha]
    exact (canonical23271 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1531 + difference 5 1) (sourceB1531 + difference 1 5) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1531 + difference 5 1) (sourceB1531 + difference 1 5) sourceC1531) = raw22526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22526; decide +kernel
    rw [ha]
    exact (canonical22526 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1531 + difference 5 2) (sourceB1531 + difference 2 5) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1531 + difference 5 2) (sourceB1531 + difference 2 5) sourceC1531) = raw23272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23272; decide +kernel
    rw [ha]
    exact (canonical23272 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1531 + difference 5 3) (sourceB1531 + difference 3 5) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1531 + difference 5 3) (sourceB1531 + difference 3 5) sourceC1531) = raw23273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw23273; decide +kernel
    rw [ha]
    exact (canonical23273 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1531 + difference 5 4) (sourceB1531 + difference 4 5) sourceC1531) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1531 + difference 5 4) (sourceB1531 + difference 4 5) sourceC1531) = raw22511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1531 sourceB1531 sourceC1531 difference raw22511; decide +kernel
    rw [ha]
    exact (canonical22511 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1531 sourceB1531 sourceC1531
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1531, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1532 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1532 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1532 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1532 : Integer.Sparse Master := [(Sum.inr 790, 2), (Sum.inr 816, 2), (Sum.inr 831, 1), (Sum.inr 974, 2), (Sum.inr 985, 4), (Sum.inr 993, 2), (Sum.inr 1026, 4), (Sum.inr 1049, 2), (Sum.inr 1050, 2), (Sum.inr 1063, 2), (Sum.inr 1095, 2), (Sum.inr 1220, 2), (Sum.inr 1274, 2), (Sum.inr 1312, 1)]

theorem sourceEq1532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1532 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1532 + difference 0 1) (sourceB1532 + difference 1 0) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1312) := by
    have ha : (tripleCharges (sourceA1532 + difference 0 1) (sourceB1532 + difference 1 0) sourceC1532) = raw22560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22560; decide +kernel
    rw [ha]
    exact (canonical22560 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1532 + difference 0 2) (sourceB1532 + difference 2 0) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1532 + difference 0 2) (sourceB1532 + difference 2 0) sourceC1532) = raw22634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22634; decide +kernel
    rw [ha]
    exact (canonical22634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1532 + difference 0 3) (sourceB1532 + difference 3 0) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1532 + difference 0 3) (sourceB1532 + difference 3 0) sourceC1532) = raw22635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22635; decide +kernel
    rw [ha]
    exact (canonical22635 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1532 + difference 0 4) (sourceB1532 + difference 4 0) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1532 + difference 0 4) (sourceB1532 + difference 4 0) sourceC1532) = raw22545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22545; decide +kernel
    rw [ha]
    exact (canonical22545 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1532 + difference 0 5) (sourceB1532 + difference 5 0) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1532 + difference 0 5) (sourceB1532 + difference 5 0) sourceC1532) = raw22636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22636; decide +kernel
    rw [ha]
    exact (canonical22636 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1532 + difference 1 0) (sourceB1532 + difference 0 1) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 831) := by
    have ha : (tripleCharges (sourceA1532 + difference 1 0) (sourceB1532 + difference 0 1) sourceC1532) = raw23274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23274; decide +kernel
    rw [ha]
    exact (canonical23274 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1532 + difference 1 2) (sourceB1532 + difference 2 1) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 993) := by
    have ha : (tripleCharges (sourceA1532 + difference 1 2) (sourceB1532 + difference 2 1) sourceC1532) = raw23275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23275; decide +kernel
    rw [ha]
    exact (canonical23275 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1532 + difference 1 3) (sourceB1532 + difference 3 1) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 993) := by
    have ha : (tripleCharges (sourceA1532 + difference 1 3) (sourceB1532 + difference 3 1) sourceC1532) = raw23276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23276; decide +kernel
    rw [ha]
    exact (canonical23276 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1532 + difference 1 4) (sourceB1532 + difference 4 1) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA1532 + difference 1 4) (sourceB1532 + difference 4 1) sourceC1532) = raw23277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23277; decide +kernel
    rw [ha]
    exact (canonical23277 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1532 + difference 1 5) (sourceB1532 + difference 5 1) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA1532 + difference 1 5) (sourceB1532 + difference 5 1) sourceC1532) = raw23104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23104; decide +kernel
    rw [ha]
    exact (canonical23104 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1532 + difference 2 0) (sourceB1532 + difference 0 2) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA1532 + difference 2 0) (sourceB1532 + difference 0 2) sourceC1532) = raw23278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23278; decide +kernel
    rw [ha]
    exact (canonical23278 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1532 + difference 2 1) (sourceB1532 + difference 1 2) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1532 + difference 2 1) (sourceB1532 + difference 1 2) sourceC1532) = raw22637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22637; decide +kernel
    rw [ha]
    exact (canonical22637 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1532 + difference 2 3) (sourceB1532 + difference 3 2) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 974) := by
    have ha : (tripleCharges (sourceA1532 + difference 2 3) (sourceB1532 + difference 3 2) sourceC1532) = raw23279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23279; decide +kernel
    rw [ha]
    exact (canonical23279 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1532 + difference 2 4) (sourceB1532 + difference 4 2) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1532 + difference 2 4) (sourceB1532 + difference 4 2) sourceC1532) = raw23280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23280; decide +kernel
    rw [ha]
    exact (canonical23280 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1532 + difference 2 5) (sourceB1532 + difference 5 2) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1532 + difference 2 5) (sourceB1532 + difference 5 2) sourceC1532) = raw23109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23109; decide +kernel
    rw [ha]
    exact (canonical23109 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1532 + difference 3 0) (sourceB1532 + difference 0 3) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA1532 + difference 3 0) (sourceB1532 + difference 0 3) sourceC1532) = raw23281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23281; decide +kernel
    rw [ha]
    exact (canonical23281 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1532 + difference 3 1) (sourceB1532 + difference 1 3) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1532 + difference 3 1) (sourceB1532 + difference 1 3) sourceC1532) = raw22641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22641; decide +kernel
    rw [ha]
    exact (canonical22641 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1532 + difference 3 2) (sourceB1532 + difference 2 3) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 974) := by
    have ha : (tripleCharges (sourceA1532 + difference 3 2) (sourceB1532 + difference 2 3) sourceC1532) = raw23282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23282; decide +kernel
    rw [ha]
    exact (canonical23282 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1532 + difference 3 4) (sourceB1532 + difference 4 3) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1532 + difference 3 4) (sourceB1532 + difference 4 3) sourceC1532) = raw23283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23283; decide +kernel
    rw [ha]
    exact (canonical23283 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1532 + difference 3 5) (sourceB1532 + difference 5 3) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1532 + difference 3 5) (sourceB1532 + difference 5 3) sourceC1532) = raw23114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23114; decide +kernel
    rw [ha]
    exact (canonical23114 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1532 + difference 4 0) (sourceB1532 + difference 0 4) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1532 + difference 4 0) (sourceB1532 + difference 0 4) sourceC1532) = raw23121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23121; decide +kernel
    rw [ha]
    exact (canonical23121 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1532 + difference 4 1) (sourceB1532 + difference 1 4) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1532 + difference 4 1) (sourceB1532 + difference 1 4) sourceC1532) = raw22645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22645; decide +kernel
    rw [ha]
    exact (canonical22645 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1532 + difference 4 2) (sourceB1532 + difference 2 4) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1532 + difference 4 2) (sourceB1532 + difference 2 4) sourceC1532) = raw23122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23122; decide +kernel
    rw [ha]
    exact (canonical23122 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1532 + difference 4 3) (sourceB1532 + difference 3 4) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1532 + difference 4 3) (sourceB1532 + difference 3 4) sourceC1532) = raw22796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22796; decide +kernel
    rw [ha]
    exact (canonical22796 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1532 + difference 4 5) (sourceB1532 + difference 5 4) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1532 + difference 4 5) (sourceB1532 + difference 5 4) sourceC1532) = raw23284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23284; decide +kernel
    rw [ha]
    exact (canonical23284 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1532 + difference 5 0) (sourceB1532 + difference 0 5) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1532 + difference 5 0) (sourceB1532 + difference 0 5) sourceC1532) = raw23285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23285; decide +kernel
    rw [ha]
    exact (canonical23285 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1532 + difference 5 1) (sourceB1532 + difference 1 5) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1532 + difference 5 1) (sourceB1532 + difference 1 5) sourceC1532) = raw22556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22556; decide +kernel
    rw [ha]
    exact (canonical22556 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1532 + difference 5 2) (sourceB1532 + difference 2 5) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1532 + difference 5 2) (sourceB1532 + difference 2 5) sourceC1532) = raw23286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23286; decide +kernel
    rw [ha]
    exact (canonical23286 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1532 + difference 5 3) (sourceB1532 + difference 3 5) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1532 + difference 5 3) (sourceB1532 + difference 3 5) sourceC1532) = raw23287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw23287; decide +kernel
    rw [ha]
    exact (canonical23287 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1532 + difference 5 4) (sourceB1532 + difference 4 5) sourceC1532) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1532 + difference 5 4) (sourceB1532 + difference 4 5) sourceC1532) = raw22541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1532 sourceB1532 sourceC1532 difference raw22541; decide +kernel
    rw [ha]
    exact (canonical22541 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1532 sourceB1532 sourceC1532
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1532, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1533 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1533 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1533 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1533 : Integer.Sparse Master := [(Sum.inr 1220, 2), (Sum.inr 1246, 2), (Sum.inr 1312, 1), (Sum.inr 1363, 2), (Sum.inr 1375, 2), (Sum.inr 1381, 2), (Sum.inr 1391, 4), (Sum.inr 1401, 4), (Sum.inr 1419, 2), (Sum.inr 1420, 2), (Sum.inr 1455, 2), (Sum.inr 1473, 1), (Sum.inr 1479, 2), (Sum.inr 1486, 2)]

theorem sourceEq1533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1533 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1533 + difference 0 1) (sourceB1533 + difference 1 0) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1312) := by
    have ha : (tripleCharges (sourceA1533 + difference 0 1) (sourceB1533 + difference 1 0) sourceC1533) = raw22831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw22831; decide +kernel
    rw [ha]
    exact (canonical22831 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1533 + difference 0 2) (sourceB1533 + difference 2 0) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1533 + difference 0 2) (sourceB1533 + difference 2 0) sourceC1533) = raw23288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23288; decide +kernel
    rw [ha]
    exact (canonical23288 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1533 + difference 0 3) (sourceB1533 + difference 3 0) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1533 + difference 0 3) (sourceB1533 + difference 3 0) sourceC1533) = raw22821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw22821; decide +kernel
    rw [ha]
    exact (canonical22821 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1533 + difference 0 4) (sourceB1533 + difference 4 0) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1533 + difference 0 4) (sourceB1533 + difference 4 0) sourceC1533) = raw23289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23289; decide +kernel
    rw [ha]
    exact (canonical23289 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1533 + difference 0 5) (sourceB1533 + difference 5 0) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1533 + difference 0 5) (sourceB1533 + difference 5 0) sourceC1533) = raw23124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23124; decide +kernel
    rw [ha]
    exact (canonical23124 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1533 + difference 1 0) (sourceB1533 + difference 0 1) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1473) := by
    have ha : (tripleCharges (sourceA1533 + difference 1 0) (sourceB1533 + difference 0 1) sourceC1533) = raw23290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23290; decide +kernel
    rw [ha]
    exact (canonical23290 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1533 + difference 1 2) (sourceB1533 + difference 2 1) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1363) := by
    have ha : (tripleCharges (sourceA1533 + difference 1 2) (sourceB1533 + difference 2 1) sourceC1533) = raw23291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23291; decide +kernel
    rw [ha]
    exact (canonical23291 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1533 + difference 1 3) (sourceB1533 + difference 3 1) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1363) := by
    have ha : (tripleCharges (sourceA1533 + difference 1 3) (sourceB1533 + difference 3 1) sourceC1533) = raw23292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23292; decide +kernel
    rw [ha]
    exact (canonical23292 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1533 + difference 1 4) (sourceB1533 + difference 4 1) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA1533 + difference 1 4) (sourceB1533 + difference 4 1) sourceC1533) = raw23293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23293; decide +kernel
    rw [ha]
    exact (canonical23293 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1533 + difference 1 5) (sourceB1533 + difference 5 1) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA1533 + difference 1 5) (sourceB1533 + difference 5 1) sourceC1533) = raw23129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23129; decide +kernel
    rw [ha]
    exact (canonical23129 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1533 + difference 2 0) (sourceB1533 + difference 0 2) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1479) := by
    have ha : (tripleCharges (sourceA1533 + difference 2 0) (sourceB1533 + difference 0 2) sourceC1533) = raw23294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23294; decide +kernel
    rw [ha]
    exact (canonical23294 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1533 + difference 2 1) (sourceB1533 + difference 1 2) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA1533 + difference 2 1) (sourceB1533 + difference 1 2) sourceC1533) = raw23295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23295; decide +kernel
    rw [ha]
    exact (canonical23295 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1533 + difference 2 3) (sourceB1533 + difference 3 2) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1381) := by
    have ha : (tripleCharges (sourceA1533 + difference 2 3) (sourceB1533 + difference 3 2) sourceC1533) = raw23296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23296; decide +kernel
    rw [ha]
    exact (canonical23296 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1533 + difference 2 4) (sourceB1533 + difference 4 2) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1533 + difference 2 4) (sourceB1533 + difference 4 2) sourceC1533) = raw23297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23297; decide +kernel
    rw [ha]
    exact (canonical23297 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1533 + difference 2 5) (sourceB1533 + difference 5 2) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1533 + difference 2 5) (sourceB1533 + difference 5 2) sourceC1533) = raw23134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23134; decide +kernel
    rw [ha]
    exact (canonical23134 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1533 + difference 3 0) (sourceB1533 + difference 0 3) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1479) := by
    have ha : (tripleCharges (sourceA1533 + difference 3 0) (sourceB1533 + difference 0 3) sourceC1533) = raw23298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23298; decide +kernel
    rw [ha]
    exact (canonical23298 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1533 + difference 3 1) (sourceB1533 + difference 1 3) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA1533 + difference 3 1) (sourceB1533 + difference 1 3) sourceC1533) = raw23299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23299; decide +kernel
    rw [ha]
    exact (canonical23299 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1533 + difference 3 2) (sourceB1533 + difference 2 3) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1381) := by
    have ha : (tripleCharges (sourceA1533 + difference 3 2) (sourceB1533 + difference 2 3) sourceC1533) = raw23300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23300; decide +kernel
    rw [ha]
    exact (canonical23300 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1533 + difference 3 4) (sourceB1533 + difference 4 3) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1533 + difference 3 4) (sourceB1533 + difference 4 3) sourceC1533) = raw23301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23301; decide +kernel
    rw [ha]
    exact (canonical23301 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1533 + difference 3 5) (sourceB1533 + difference 5 3) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1533 + difference 3 5) (sourceB1533 + difference 5 3) sourceC1533) = raw23139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23139; decide +kernel
    rw [ha]
    exact (canonical23139 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1533 + difference 4 0) (sourceB1533 + difference 0 4) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1486) := by
    have ha : (tripleCharges (sourceA1533 + difference 4 0) (sourceB1533 + difference 0 4) sourceC1533) = raw23146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23146; decide +kernel
    rw [ha]
    exact (canonical23146 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1533 + difference 4 1) (sourceB1533 + difference 1 4) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1455) := by
    have ha : (tripleCharges (sourceA1533 + difference 4 1) (sourceB1533 + difference 1 4) sourceC1533) = raw22828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw22828; decide +kernel
    rw [ha]
    exact (canonical22828 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1533 + difference 4 2) (sourceB1533 + difference 2 4) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1401) := by
    have ha : (tripleCharges (sourceA1533 + difference 4 2) (sourceB1533 + difference 2 4) sourceC1533) = raw23147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23147; decide +kernel
    rw [ha]
    exact (canonical23147 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1533 + difference 4 3) (sourceB1533 + difference 3 4) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1401) := by
    have ha : (tripleCharges (sourceA1533 + difference 4 3) (sourceB1533 + difference 3 4) sourceC1533) = raw22818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw22818; decide +kernel
    rw [ha]
    exact (canonical22818 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1533 + difference 4 5) (sourceB1533 + difference 5 4) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1533 + difference 4 5) (sourceB1533 + difference 5 4) sourceC1533) = raw23302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23302; decide +kernel
    rw [ha]
    exact (canonical23302 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1533 + difference 5 0) (sourceB1533 + difference 0 5) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1486) := by
    have ha : (tripleCharges (sourceA1533 + difference 5 0) (sourceB1533 + difference 0 5) sourceC1533) = raw23303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23303; decide +kernel
    rw [ha]
    exact (canonical23303 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1533 + difference 5 1) (sourceB1533 + difference 1 5) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1455) := by
    have ha : (tripleCharges (sourceA1533 + difference 5 1) (sourceB1533 + difference 1 5) sourceC1533) = raw23304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23304; decide +kernel
    rw [ha]
    exact (canonical23304 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1533 + difference 5 2) (sourceB1533 + difference 2 5) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1401) := by
    have ha : (tripleCharges (sourceA1533 + difference 5 2) (sourceB1533 + difference 2 5) sourceC1533) = raw23305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23305; decide +kernel
    rw [ha]
    exact (canonical23305 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1533 + difference 5 3) (sourceB1533 + difference 3 5) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1401) := by
    have ha : (tripleCharges (sourceA1533 + difference 5 3) (sourceB1533 + difference 3 5) sourceC1533) = raw23306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23306; decide +kernel
    rw [ha]
    exact (canonical23306 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1533 + difference 5 4) (sourceB1533 + difference 4 5) sourceC1533) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1533 + difference 5 4) (sourceB1533 + difference 4 5) sourceC1533) = raw23307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1533 sourceB1533 sourceC1533 difference raw23307; decide +kernel
    rw [ha]
    exact (canonical23307 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1533 sourceB1533 sourceC1533
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1533, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1534 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1534 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC1534 : Charge := ![3, -1, 0, 1, -3, 0]
def sourceForm1534 : Integer.Sparse Master := [(Sum.inr 984, 1), (Sum.inr 1917, 1), (Sum.inr 1989, 1), (Sum.inr 2081, 1), (Sum.inr 2203, 1), (Sum.inr 2207, 1), (Sum.inr 4081, -1)]

theorem sourceEq1534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1534 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 0) (sourceB1534 + difference 0 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 0) (sourceB1534 + difference 0 0) sourceC1534) = raw23308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23308; decide +kernel
    rw [ha]
    exact (canonical23308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 1) (sourceB1534 + difference 1 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2081) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 1) (sourceB1534 + difference 1 0) sourceC1534) = raw23309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23309; decide +kernel
    rw [ha]
    exact (canonical23309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 2) (sourceB1534 + difference 2 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1989) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 2) (sourceB1534 + difference 2 0) sourceC1534) = raw23310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23310; decide +kernel
    rw [ha]
    exact (canonical23310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 3) (sourceB1534 + difference 3 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 3) (sourceB1534 + difference 3 0) sourceC1534) = raw23311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23311; decide +kernel
    rw [ha]
    exact (canonical23311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 4) (sourceB1534 + difference 4 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 4) (sourceB1534 + difference 4 0) sourceC1534) = raw23312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23312; decide +kernel
    rw [ha]
    exact (canonical23312 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1534 + difference 0 5) (sourceB1534 + difference 5 0) sourceC1534) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1534 + difference 0 5) (sourceB1534 + difference 5 0) sourceC1534) = raw23313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1534 sourceB1534 sourceC1534 difference raw23313; decide +kernel
    rw [ha]
    exact (canonical23313 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1534 + sourceB1534) sourceC1534) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1534 + sourceB1534) sourceC1534) = raw23314 := by
      apply Matrix.ext; unfold doubleCharges sourceA1534 sourceB1534 sourceC1534 raw23314; decide +kernel
    rw [ha]
    exact (canonical23314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1534 sourceB1534 sourceC1534
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1534, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1535 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1535 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1535 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceForm1535 : Integer.Sparse Master := [(Sum.inr 985, 1), (Sum.inr 1918, 1), (Sum.inr 1990, 1), (Sum.inr 2082, 1), (Sum.inr 2205, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

theorem sourceEq1535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1535 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 0) (sourceB1535 + difference 0 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 0) (sourceB1535 + difference 0 0) sourceC1535) = raw21590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw21590; decide +kernel
    rw [ha]
    exact (canonical21590 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 1) (sourceB1535 + difference 1 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 1) (sourceB1535 + difference 1 0) sourceC1535) = raw23315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw23315; decide +kernel
    rw [ha]
    exact (canonical23315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 2) (sourceB1535 + difference 2 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1990) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 2) (sourceB1535 + difference 2 0) sourceC1535) = raw23316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw23316; decide +kernel
    rw [ha]
    exact (canonical23316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 3) (sourceB1535 + difference 3 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 3) (sourceB1535 + difference 3 0) sourceC1535) = raw23317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw23317; decide +kernel
    rw [ha]
    exact (canonical23317 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 4) (sourceB1535 + difference 4 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 4) (sourceB1535 + difference 4 0) sourceC1535) = raw21585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw21585; decide +kernel
    rw [ha]
    exact (canonical21585 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1535 + difference 0 5) (sourceB1535 + difference 5 0) sourceC1535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1535 + difference 0 5) (sourceB1535 + difference 5 0) sourceC1535) = raw23318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1535 sourceB1535 sourceC1535 difference raw23318; decide +kernel
    rw [ha]
    exact (canonical23318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1535 + sourceB1535) sourceC1535) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1535 + sourceB1535) sourceC1535) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA1535 sourceB1535 sourceC1535 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1535 sourceB1535 sourceC1535
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1535, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
