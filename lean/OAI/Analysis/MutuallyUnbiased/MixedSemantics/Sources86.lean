import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical294
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical295

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2752 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceB2752 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2752 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2752 : Integer.Sparse Master := [(Sum.inr 1889, 1), (Sum.inr 1893, 1), (Sum.inr 1895, 1), (Sum.inr 1939, 1), (Sum.inr 2186, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

theorem sourceEq2752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2752 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2752 + difference 0 5) (sourceB2752 + difference 5 0) sourceC2752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1895) := by
    have ha : (tripleCharges (sourceA2752 + difference 0 5) (sourceB2752 + difference 5 0) sourceC2752) = raw37760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2752 sourceB2752 sourceC2752 difference raw37760; decide +kernel
    rw [ha]
    exact (canonical37760 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2752 + difference 1 5) (sourceB2752 + difference 5 1) sourceC2752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1893) := by
    have ha : (tripleCharges (sourceA2752 + difference 1 5) (sourceB2752 + difference 5 1) sourceC2752) = raw37761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2752 sourceB2752 sourceC2752 difference raw37761; decide +kernel
    rw [ha]
    exact (canonical37761 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2752 + difference 2 5) (sourceB2752 + difference 5 2) sourceC2752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1889) := by
    have ha : (tripleCharges (sourceA2752 + difference 2 5) (sourceB2752 + difference 5 2) sourceC2752) = raw37762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2752 sourceB2752 sourceC2752 difference raw37762; decide +kernel
    rw [ha]
    exact (canonical37762 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2752 + difference 3 5) (sourceB2752 + difference 5 3) sourceC2752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2752 + difference 3 5) (sourceB2752 + difference 5 3) sourceC2752) = raw37721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2752 sourceB2752 sourceC2752 difference raw37721; decide +kernel
    rw [ha]
    exact (canonical37721 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2752 + difference 4 5) (sourceB2752 + difference 5 4) sourceC2752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1939) := by
    have ha : (tripleCharges (sourceA2752 + difference 4 5) (sourceB2752 + difference 5 4) sourceC2752) = raw37763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2752 sourceB2752 sourceC2752 difference raw37763; decide +kernel
    rw [ha]
    exact (canonical37763 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2752 + difference 5 5) (sourceB2752 + difference 5 5) sourceC2752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2752 + difference 5 5) (sourceB2752 + difference 5 5) sourceC2752) = raw37714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2752 sourceB2752 sourceC2752 difference raw37714; decide +kernel
    rw [ha]
    exact (canonical37714 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2752 + sourceB2752) sourceC2752) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2752 + sourceB2752) sourceC2752) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2752 sourceB2752 sourceC2752 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2752 sourceB2752 sourceC2752
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2752, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2753 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceB2753 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2753 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2753 : Integer.Sparse Master := [(Sum.inr 970, 1), (Sum.inr 1895, 2), (Sum.inr 1985, 1), (Sum.inr 2185, 1), (Sum.inr 2186, 1), (Sum.inr 4074, -1)]

theorem sourceEq2753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2753 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2753 + difference 0 0) (sourceB2753 + difference 0 0) sourceC2753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2753 + difference 0 0) (sourceB2753 + difference 0 0) sourceC2753) = raw37721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2753 sourceB2753 sourceC2753 difference raw37721; decide +kernel
    rw [ha]
    exact (canonical37721 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2753 + difference 0 1) (sourceB2753 + difference 1 0) sourceC2753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2753 + difference 0 1) (sourceB2753 + difference 1 0) sourceC2753) = raw37736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2753 sourceB2753 sourceC2753 difference raw37736; decide +kernel
    rw [ha]
    exact (canonical37736 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2753 + difference 0 2) (sourceB2753 + difference 2 0) sourceC2753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1985) := by
    have ha : (tripleCharges (sourceA2753 + difference 0 2) (sourceB2753 + difference 2 0) sourceC2753) = raw37764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2753 sourceB2753 sourceC2753 difference raw37764; decide +kernel
    rw [ha]
    exact (canonical37764 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2753 + difference 0 3) (sourceB2753 + difference 3 0) sourceC2753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1895) := by
    have ha : (tripleCharges (sourceA2753 + difference 0 3) (sourceB2753 + difference 3 0) sourceC2753) = raw37760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2753 sourceB2753 sourceC2753 difference raw37760; decide +kernel
    rw [ha]
    exact (canonical37760 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2753 + difference 0 4) (sourceB2753 + difference 4 0) sourceC2753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1895) := by
    have ha : (tripleCharges (sourceA2753 + difference 0 4) (sourceB2753 + difference 4 0) sourceC2753) = raw37765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2753 sourceB2753 sourceC2753 difference raw37765; decide +kernel
    rw [ha]
    exact (canonical37765 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2753 + difference 0 5) (sourceB2753 + difference 5 0) sourceC2753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 970) := by
    have ha : (tripleCharges (sourceA2753 + difference 0 5) (sourceB2753 + difference 5 0) sourceC2753) = raw37766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2753 sourceB2753 sourceC2753 difference raw37766; decide +kernel
    rw [ha]
    exact (canonical37766 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2753 + sourceB2753) sourceC2753) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2753 + sourceB2753) sourceC2753) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2753 sourceB2753 sourceC2753 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2753 sourceB2753 sourceC2753
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2753, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2754 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2754 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC2754 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2754 : Integer.Sparse Master := [(Sum.inr 1852, 1), (Sum.inr 3327, 1), (Sum.inr 3399, 1), (Sum.inr 3411, 2), (Sum.inr 3420, 1), (Sum.inr 4074, -1)]

theorem sourceEq2754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2754 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2754 + difference 5 0) (sourceB2754 + difference 0 5) sourceC2754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1852) := by
    have ha : (tripleCharges (sourceA2754 + difference 5 0) (sourceB2754 + difference 0 5) sourceC2754) = raw37767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2754 sourceB2754 sourceC2754 difference raw37767; decide +kernel
    rw [ha]
    exact (canonical37767 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2754 + difference 5 1) (sourceB2754 + difference 1 5) sourceC2754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3327) := by
    have ha : (tripleCharges (sourceA2754 + difference 5 1) (sourceB2754 + difference 1 5) sourceC2754) = raw37768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2754 sourceB2754 sourceC2754 difference raw37768; decide +kernel
    rw [ha]
    exact (canonical37768 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2754 + difference 5 2) (sourceB2754 + difference 2 5) sourceC2754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3399) := by
    have ha : (tripleCharges (sourceA2754 + difference 5 2) (sourceB2754 + difference 2 5) sourceC2754) = raw37769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2754 sourceB2754 sourceC2754 difference raw37769; decide +kernel
    rw [ha]
    exact (canonical37769 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2754 + difference 5 3) (sourceB2754 + difference 3 5) sourceC2754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2754 + difference 5 3) (sourceB2754 + difference 3 5) sourceC2754) = raw37735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2754 sourceB2754 sourceC2754 difference raw37735; decide +kernel
    rw [ha]
    exact (canonical37735 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2754 + difference 5 4) (sourceB2754 + difference 4 5) sourceC2754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2754 + difference 5 4) (sourceB2754 + difference 4 5) sourceC2754) = raw37742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2754 sourceB2754 sourceC2754 difference raw37742; decide +kernel
    rw [ha]
    exact (canonical37742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2754 + difference 5 5) (sourceB2754 + difference 5 5) sourceC2754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2754 + difference 5 5) (sourceB2754 + difference 5 5) sourceC2754) = raw37733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2754 sourceB2754 sourceC2754 difference raw37733; decide +kernel
    rw [ha]
    exact (canonical37733 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2754 + sourceB2754) sourceC2754) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2754 + sourceB2754) sourceC2754) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2754 sourceB2754 sourceC2754 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2754 sourceB2754 sourceC2754
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2754, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2755 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2755 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2755 : Charge := ![-3, -2, 0, 1, 1, 3]
def sourceForm2755 : Integer.Sparse Master := [(Sum.inr 1839, 1), (Sum.inr 1888, 1), (Sum.inr 1895, 1), (Sum.inr 1938, 1), (Sum.inr 2185, 1), (Sum.inr 3411, 1), (Sum.inr 4074, -1)]

theorem sourceEq2755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2755 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2755 + difference 5 0) (sourceB2755 + difference 0 5) sourceC2755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1839) := by
    have ha : (tripleCharges (sourceA2755 + difference 5 0) (sourceB2755 + difference 0 5) sourceC2755) = raw37770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2755 sourceB2755 sourceC2755 difference raw37770; decide +kernel
    rw [ha]
    exact (canonical37770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2755 + difference 5 1) (sourceB2755 + difference 1 5) sourceC2755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1895) := by
    have ha : (tripleCharges (sourceA2755 + difference 5 1) (sourceB2755 + difference 1 5) sourceC2755) = raw37771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2755 sourceB2755 sourceC2755 difference raw37771; decide +kernel
    rw [ha]
    exact (canonical37771 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2755 + difference 5 2) (sourceB2755 + difference 2 5) sourceC2755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1888) := by
    have ha : (tripleCharges (sourceA2755 + difference 5 2) (sourceB2755 + difference 2 5) sourceC2755) = raw37772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2755 sourceB2755 sourceC2755 difference raw37772; decide +kernel
    rw [ha]
    exact (canonical37772 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2755 + difference 5 3) (sourceB2755 + difference 3 5) sourceC2755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2755 + difference 5 3) (sourceB2755 + difference 3 5) sourceC2755) = raw37743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2755 sourceB2755 sourceC2755 difference raw37743; decide +kernel
    rw [ha]
    exact (canonical37743 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2755 + difference 5 4) (sourceB2755 + difference 4 5) sourceC2755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1938) := by
    have ha : (tripleCharges (sourceA2755 + difference 5 4) (sourceB2755 + difference 4 5) sourceC2755) = raw37773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2755 sourceB2755 sourceC2755 difference raw37773; decide +kernel
    rw [ha]
    exact (canonical37773 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2755 + difference 5 5) (sourceB2755 + difference 5 5) sourceC2755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2755 + difference 5 5) (sourceB2755 + difference 5 5) sourceC2755) = raw37742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2755 sourceB2755 sourceC2755 difference raw37742; decide +kernel
    rw [ha]
    exact (canonical37742 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2755 + sourceB2755) sourceC2755) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2755 + sourceB2755) sourceC2755) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2755 sourceB2755 sourceC2755 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2755 sourceB2755 sourceC2755
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2755, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2756 : Charge := ![0, 2, 0, -1, -2, 1]
def sourceB2756 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2756 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2756 : Integer.Sparse Master := [(Sum.inr 2144, 1), (Sum.inr 2146, 1), (Sum.inr 2152, 1), (Sum.inr 2157, 1), (Sum.inr 2249, 1), (Sum.inr 3591, 1), (Sum.inr 4075, -1)]

theorem sourceEq2756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2756 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2756 + difference 0 5) (sourceB2756 + difference 5 0) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2756 + difference 0 5) (sourceB2756 + difference 5 0) sourceC2756) = raw37774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37774; decide +kernel
    rw [ha]
    exact (canonical37774 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2756 + difference 1 5) (sourceB2756 + difference 5 1) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2756 + difference 1 5) (sourceB2756 + difference 5 1) sourceC2756) = raw37775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37775; decide +kernel
    rw [ha]
    exact (canonical37775 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2756 + difference 2 5) (sourceB2756 + difference 5 2) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2756 + difference 2 5) (sourceB2756 + difference 5 2) sourceC2756) = raw37776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37776; decide +kernel
    rw [ha]
    exact (canonical37776 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2756 + difference 3 5) (sourceB2756 + difference 5 3) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2756 + difference 3 5) (sourceB2756 + difference 5 3) sourceC2756) = raw37777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37777; decide +kernel
    rw [ha]
    exact (canonical37777 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2756 + difference 4 5) (sourceB2756 + difference 5 4) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2756 + difference 4 5) (sourceB2756 + difference 5 4) sourceC2756) = raw37778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37778; decide +kernel
    rw [ha]
    exact (canonical37778 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2756 + difference 5 5) (sourceB2756 + difference 5 5) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2756 + difference 5 5) (sourceB2756 + difference 5 5) sourceC2756) = raw37779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37779; decide +kernel
    rw [ha]
    exact (canonical37779 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2756 + sourceB2756) sourceC2756) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2756 + sourceB2756) sourceC2756) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2756 sourceB2756 sourceC2756 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2756 sourceB2756 sourceC2756
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2756, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2757 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2757 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2757 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2757 : Integer.Sparse Master := [(Sum.inr 2154, 1), (Sum.inr 2157, 1), (Sum.inr 2158, 1), (Sum.inr 2166, 1), (Sum.inr 2272, 1), (Sum.inr 3595, 1), (Sum.inr 4075, -1)]

theorem sourceEq2757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2757 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2757 + difference 0 3) (sourceB2757 + difference 3 0) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2757 + difference 0 3) (sourceB2757 + difference 3 0) sourceC2757) = raw37781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37781; decide +kernel
    rw [ha]
    exact (canonical37781 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2757 + difference 1 3) (sourceB2757 + difference 3 1) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2757 + difference 1 3) (sourceB2757 + difference 3 1) sourceC2757) = raw37782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37782; decide +kernel
    rw [ha]
    exact (canonical37782 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2757 + difference 2 3) (sourceB2757 + difference 3 2) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2757 + difference 2 3) (sourceB2757 + difference 3 2) sourceC2757) = raw37783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37783; decide +kernel
    rw [ha]
    exact (canonical37783 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2757 + difference 3 3) (sourceB2757 + difference 3 3) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2757 + difference 3 3) (sourceB2757 + difference 3 3) sourceC2757) = raw37784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37784; decide +kernel
    rw [ha]
    exact (canonical37784 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2757 + difference 4 3) (sourceB2757 + difference 3 4) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2757 + difference 4 3) (sourceB2757 + difference 3 4) sourceC2757) = raw37785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37785; decide +kernel
    rw [ha]
    exact (canonical37785 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2757 + difference 5 3) (sourceB2757 + difference 3 5) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2757 + difference 5 3) (sourceB2757 + difference 3 5) sourceC2757) = raw37777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37777; decide +kernel
    rw [ha]
    exact (canonical37777 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2757 + sourceB2757) sourceC2757) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2757 + sourceB2757) sourceC2757) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2757 sourceB2757 sourceC2757 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2757 sourceB2757 sourceC2757
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2757, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2758 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB2758 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2758 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2758 : Integer.Sparse Master := [(Sum.inr 2148, 1), (Sum.inr 2152, 2), (Sum.inr 2166, 1), (Sum.inr 2257, 1), (Sum.inr 3592, 1), (Sum.inr 4075, -1)]

theorem sourceEq2758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2758 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2758 + difference 0 2) (sourceB2758 + difference 2 0) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2758 + difference 0 2) (sourceB2758 + difference 2 0) sourceC2758) = raw37786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37786; decide +kernel
    rw [ha]
    exact (canonical37786 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2758 + difference 1 2) (sourceB2758 + difference 2 1) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2758 + difference 1 2) (sourceB2758 + difference 2 1) sourceC2758) = raw37787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37787; decide +kernel
    rw [ha]
    exact (canonical37787 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2758 + difference 2 2) (sourceB2758 + difference 2 2) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2758 + difference 2 2) (sourceB2758 + difference 2 2) sourceC2758) = raw37788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37788; decide +kernel
    rw [ha]
    exact (canonical37788 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2758 + difference 3 2) (sourceB2758 + difference 2 3) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2758 + difference 3 2) (sourceB2758 + difference 2 3) sourceC2758) = raw37785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37785; decide +kernel
    rw [ha]
    exact (canonical37785 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2758 + difference 4 2) (sourceB2758 + difference 2 4) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2758 + difference 4 2) (sourceB2758 + difference 2 4) sourceC2758) = raw37789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37789; decide +kernel
    rw [ha]
    exact (canonical37789 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2758 + difference 5 2) (sourceB2758 + difference 2 5) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2758 + difference 5 2) (sourceB2758 + difference 2 5) sourceC2758) = raw37778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37778; decide +kernel
    rw [ha]
    exact (canonical37778 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2758 + sourceB2758) sourceC2758) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2758 + sourceB2758) sourceC2758) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2758 sourceB2758 sourceC2758 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2758 sourceB2758 sourceC2758
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2758, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2759 : Charge := ![1, 1, 0, -1, -2, 1]
def sourceB2759 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2759 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2759 : Integer.Sparse Master := [(Sum.inr 2658, 1), (Sum.inr 3406, 1), (Sum.inr 3412, 1), (Sum.inr 3417, 2), (Sum.inr 3591, 1), (Sum.inr 4075, -1)]

theorem sourceEq2759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2759 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2759 + difference 0 5) (sourceB2759 + difference 5 0) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2759 + difference 0 5) (sourceB2759 + difference 5 0) sourceC2759) = raw37790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37790; decide +kernel
    rw [ha]
    exact (canonical37790 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2759 + difference 1 5) (sourceB2759 + difference 5 1) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2759 + difference 1 5) (sourceB2759 + difference 5 1) sourceC2759) = raw37774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37774; decide +kernel
    rw [ha]
    exact (canonical37774 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2759 + difference 2 5) (sourceB2759 + difference 5 2) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2759 + difference 2 5) (sourceB2759 + difference 5 2) sourceC2759) = raw37791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37791; decide +kernel
    rw [ha]
    exact (canonical37791 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2759 + difference 3 5) (sourceB2759 + difference 5 3) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2759 + difference 3 5) (sourceB2759 + difference 5 3) sourceC2759) = raw37792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37792; decide +kernel
    rw [ha]
    exact (canonical37792 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2759 + difference 4 5) (sourceB2759 + difference 5 4) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2759 + difference 4 5) (sourceB2759 + difference 5 4) sourceC2759) = raw37793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37793; decide +kernel
    rw [ha]
    exact (canonical37793 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2759 + difference 5 5) (sourceB2759 + difference 5 5) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2759 + difference 5 5) (sourceB2759 + difference 5 5) sourceC2759) = raw37794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37794; decide +kernel
    rw [ha]
    exact (canonical37794 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2759 + sourceB2759) sourceC2759) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2759 + sourceB2759) sourceC2759) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2759 sourceB2759 sourceC2759 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2759 sourceB2759 sourceC2759
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2759, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2760 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB2760 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC2760 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2760 : Integer.Sparse Master := [(Sum.inr 1848, 1), (Sum.inr 3324, 1), (Sum.inr 3409, 1), (Sum.inr 3414, 2), (Sum.inr 3421, 1), (Sum.inr 4075, -1)]

theorem sourceEq2760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2760 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2760 + difference 3 0) (sourceB2760 + difference 0 3) sourceC2760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1848) := by
    have ha : (tripleCharges (sourceA2760 + difference 3 0) (sourceB2760 + difference 0 3) sourceC2760) = raw37795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2760 sourceB2760 sourceC2760 difference raw37795; decide +kernel
    rw [ha]
    exact (canonical37795 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2760 + difference 3 1) (sourceB2760 + difference 1 3) sourceC2760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3324) := by
    have ha : (tripleCharges (sourceA2760 + difference 3 1) (sourceB2760 + difference 1 3) sourceC2760) = raw37796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2760 sourceB2760 sourceC2760 difference raw37796; decide +kernel
    rw [ha]
    exact (canonical37796 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2760 + difference 3 2) (sourceB2760 + difference 2 3) sourceC2760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3421) := by
    have ha : (tripleCharges (sourceA2760 + difference 3 2) (sourceB2760 + difference 2 3) sourceC2760) = raw37797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2760 sourceB2760 sourceC2760 difference raw37797; decide +kernel
    rw [ha]
    exact (canonical37797 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2760 + difference 3 3) (sourceB2760 + difference 3 3) sourceC2760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3409) := by
    have ha : (tripleCharges (sourceA2760 + difference 3 3) (sourceB2760 + difference 3 3) sourceC2760) = raw37798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2760 sourceB2760 sourceC2760 difference raw37798; decide +kernel
    rw [ha]
    exact (canonical37798 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2760 + difference 3 4) (sourceB2760 + difference 4 3) sourceC2760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2760 + difference 3 4) (sourceB2760 + difference 4 3) sourceC2760) = raw37799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2760 sourceB2760 sourceC2760 difference raw37799; decide +kernel
    rw [ha]
    exact (canonical37799 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2760 + difference 3 5) (sourceB2760 + difference 5 3) sourceC2760) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2760 + difference 3 5) (sourceB2760 + difference 5 3) sourceC2760) = raw37800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2760 sourceB2760 sourceC2760 difference raw37800; decide +kernel
    rw [ha]
    exact (canonical37800 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2760 + sourceB2760) sourceC2760) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2760 + sourceB2760) sourceC2760) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2760 sourceB2760 sourceC2760 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2760 sourceB2760 sourceC2760
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2760, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2761 : Charge := ![1, 2, 0, -1, -2, 0]
def sourceB2761 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2761 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2761 : Integer.Sparse Master := [(Sum.inr 2447, 1), (Sum.inr 3320, 1), (Sum.inr 3322, 1), (Sum.inr 3328, 1), (Sum.inr 3417, 1), (Sum.inr 3591, 1), (Sum.inr 4075, -1)]

theorem sourceEq2761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2761 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2761 + difference 0 0) (sourceB2761 + difference 0 0) sourceC2761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2761 + difference 0 0) (sourceB2761 + difference 0 0) sourceC2761) = raw37774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2761 sourceB2761 sourceC2761 difference raw37774; decide +kernel
    rw [ha]
    exact (canonical37774 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2761 + difference 0 1) (sourceB2761 + difference 1 0) sourceC2761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2761 + difference 0 1) (sourceB2761 + difference 1 0) sourceC2761) = raw37790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2761 sourceB2761 sourceC2761 difference raw37790; decide +kernel
    rw [ha]
    exact (canonical37790 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2761 + difference 0 2) (sourceB2761 + difference 2 0) sourceC2761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3320) := by
    have ha : (tripleCharges (sourceA2761 + difference 0 2) (sourceB2761 + difference 2 0) sourceC2761) = raw37801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2761 sourceB2761 sourceC2761 difference raw37801; decide +kernel
    rw [ha]
    exact (canonical37801 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2761 + difference 0 3) (sourceB2761 + difference 3 0) sourceC2761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3322) := by
    have ha : (tripleCharges (sourceA2761 + difference 0 3) (sourceB2761 + difference 3 0) sourceC2761) = raw37802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2761 sourceB2761 sourceC2761 difference raw37802; decide +kernel
    rw [ha]
    exact (canonical37802 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2761 + difference 0 4) (sourceB2761 + difference 4 0) sourceC2761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2447) := by
    have ha : (tripleCharges (sourceA2761 + difference 0 4) (sourceB2761 + difference 4 0) sourceC2761) = raw37803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2761 sourceB2761 sourceC2761 difference raw37803; decide +kernel
    rw [ha]
    exact (canonical37803 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2761 + difference 0 5) (sourceB2761 + difference 5 0) sourceC2761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3328) := by
    have ha : (tripleCharges (sourceA2761 + difference 0 5) (sourceB2761 + difference 5 0) sourceC2761) = raw37804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2761 sourceB2761 sourceC2761 difference raw37804; decide +kernel
    rw [ha]
    exact (canonical37804 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2761 + sourceB2761) sourceC2761) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2761 + sourceB2761) sourceC2761) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2761 sourceB2761 sourceC2761 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2761 sourceB2761 sourceC2761
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2761, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2762 : Charge := ![1, 2, 0, -1, -2, 0]
def sourceB2762 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2762 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2762 : Integer.Sparse Master := [(Sum.inr 2368, 1), (Sum.inr 3328, 1), (Sum.inr 3589, 1), (Sum.inr 3591, 1), (Sum.inr 3592, 1), (Sum.inr 3595, 1), (Sum.inr 4075, -1)]

theorem sourceEq2762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2762 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2762 + difference 0 5) (sourceB2762 + difference 5 0) sourceC2762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3328) := by
    have ha : (tripleCharges (sourceA2762 + difference 0 5) (sourceB2762 + difference 5 0) sourceC2762) = raw37804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2762 sourceB2762 sourceC2762 difference raw37804; decide +kernel
    rw [ha]
    exact (canonical37804 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2762 + difference 1 5) (sourceB2762 + difference 5 1) sourceC2762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2368) := by
    have ha : (tripleCharges (sourceA2762 + difference 1 5) (sourceB2762 + difference 5 1) sourceC2762) = raw37805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2762 sourceB2762 sourceC2762 difference raw37805; decide +kernel
    rw [ha]
    exact (canonical37805 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2762 + difference 2 5) (sourceB2762 + difference 5 2) sourceC2762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3589) := by
    have ha : (tripleCharges (sourceA2762 + difference 2 5) (sourceB2762 + difference 5 2) sourceC2762) = raw37806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2762 sourceB2762 sourceC2762 difference raw37806; decide +kernel
    rw [ha]
    exact (canonical37806 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2762 + difference 3 5) (sourceB2762 + difference 5 3) sourceC2762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2762 + difference 3 5) (sourceB2762 + difference 5 3) sourceC2762) = raw37781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2762 sourceB2762 sourceC2762 difference raw37781; decide +kernel
    rw [ha]
    exact (canonical37781 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2762 + difference 4 5) (sourceB2762 + difference 5 4) sourceC2762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2762 + difference 4 5) (sourceB2762 + difference 5 4) sourceC2762) = raw37786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2762 sourceB2762 sourceC2762 difference raw37786; decide +kernel
    rw [ha]
    exact (canonical37786 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2762 + difference 5 5) (sourceB2762 + difference 5 5) sourceC2762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2762 + difference 5 5) (sourceB2762 + difference 5 5) sourceC2762) = raw37774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2762 sourceB2762 sourceC2762 difference raw37774; decide +kernel
    rw [ha]
    exact (canonical37774 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2762 + sourceB2762) sourceC2762) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2762 + sourceB2762) sourceC2762) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2762 sourceB2762 sourceC2762 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2762 sourceB2762 sourceC2762
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2762, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2763 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceB2763 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2763 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2763 : Integer.Sparse Master := [(Sum.inr 3324, 1), (Sum.inr 3328, 2), (Sum.inr 3330, 1), (Sum.inr 3421, 1), (Sum.inr 3592, 1), (Sum.inr 4075, -1)]

theorem sourceEq2763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2763 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2763 + difference 0 0) (sourceB2763 + difference 0 0) sourceC2763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2763 + difference 0 0) (sourceB2763 + difference 0 0) sourceC2763) = raw37786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2763 sourceB2763 sourceC2763 difference raw37786; decide +kernel
    rw [ha]
    exact (canonical37786 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2763 + difference 0 1) (sourceB2763 + difference 1 0) sourceC2763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3421) := by
    have ha : (tripleCharges (sourceA2763 + difference 0 1) (sourceB2763 + difference 1 0) sourceC2763) = raw37807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2763 sourceB2763 sourceC2763 difference raw37807; decide +kernel
    rw [ha]
    exact (canonical37807 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2763 + difference 0 2) (sourceB2763 + difference 2 0) sourceC2763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3324) := by
    have ha : (tripleCharges (sourceA2763 + difference 0 2) (sourceB2763 + difference 2 0) sourceC2763) = raw37808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2763 sourceB2763 sourceC2763 difference raw37808; decide +kernel
    rw [ha]
    exact (canonical37808 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2763 + difference 0 3) (sourceB2763 + difference 3 0) sourceC2763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3330) := by
    have ha : (tripleCharges (sourceA2763 + difference 0 3) (sourceB2763 + difference 3 0) sourceC2763) = raw37809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2763 sourceB2763 sourceC2763 difference raw37809; decide +kernel
    rw [ha]
    exact (canonical37809 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2763 + difference 0 4) (sourceB2763 + difference 4 0) sourceC2763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3328) := by
    have ha : (tripleCharges (sourceA2763 + difference 0 4) (sourceB2763 + difference 4 0) sourceC2763) = raw37804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2763 sourceB2763 sourceC2763 difference raw37804; decide +kernel
    rw [ha]
    exact (canonical37804 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2763 + difference 0 5) (sourceB2763 + difference 5 0) sourceC2763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3328) := by
    have ha : (tripleCharges (sourceA2763 + difference 0 5) (sourceB2763 + difference 5 0) sourceC2763) = raw37810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2763 sourceB2763 sourceC2763 difference raw37810; decide +kernel
    rw [ha]
    exact (canonical37810 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2763 + sourceB2763) sourceC2763) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2763 + sourceB2763) sourceC2763) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2763 sourceB2763 sourceC2763 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2763 sourceB2763 sourceC2763
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2763, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2764 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB2764 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2764 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2764 : Integer.Sparse Master := [(Sum.inr 2376, 1), (Sum.inr 3316, 1), (Sum.inr 3319, 1), (Sum.inr 3328, 1), (Sum.inr 3412, 1), (Sum.inr 3595, 1), (Sum.inr 4075, -1)]

theorem sourceEq2764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2764 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2764 + difference 0 0) (sourceB2764 + difference 0 0) sourceC2764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2764 + difference 0 0) (sourceB2764 + difference 0 0) sourceC2764) = raw37781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2764 sourceB2764 sourceC2764 difference raw37781; decide +kernel
    rw [ha]
    exact (canonical37781 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2764 + difference 0 1) (sourceB2764 + difference 1 0) sourceC2764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2764 + difference 0 1) (sourceB2764 + difference 1 0) sourceC2764) = raw37811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2764 sourceB2764 sourceC2764 difference raw37811; decide +kernel
    rw [ha]
    exact (canonical37811 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2764 + difference 0 2) (sourceB2764 + difference 2 0) sourceC2764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3316) := by
    have ha : (tripleCharges (sourceA2764 + difference 0 2) (sourceB2764 + difference 2 0) sourceC2764) = raw37812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2764 sourceB2764 sourceC2764 difference raw37812; decide +kernel
    rw [ha]
    exact (canonical37812 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2764 + difference 0 3) (sourceB2764 + difference 3 0) sourceC2764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3328) := by
    have ha : (tripleCharges (sourceA2764 + difference 0 3) (sourceB2764 + difference 3 0) sourceC2764) = raw37804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2764 sourceB2764 sourceC2764 difference raw37804; decide +kernel
    rw [ha]
    exact (canonical37804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2764 + difference 0 4) (sourceB2764 + difference 4 0) sourceC2764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2376) := by
    have ha : (tripleCharges (sourceA2764 + difference 0 4) (sourceB2764 + difference 4 0) sourceC2764) = raw37813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2764 sourceB2764 sourceC2764 difference raw37813; decide +kernel
    rw [ha]
    exact (canonical37813 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2764 + difference 0 5) (sourceB2764 + difference 5 0) sourceC2764) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3319) := by
    have ha : (tripleCharges (sourceA2764 + difference 0 5) (sourceB2764 + difference 5 0) sourceC2764) = raw37814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2764 sourceB2764 sourceC2764 difference raw37814; decide +kernel
    rw [ha]
    exact (canonical37814 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2764 + sourceB2764) sourceC2764) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2764 + sourceB2764) sourceC2764) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2764 sourceB2764 sourceC2764 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2764 sourceB2764 sourceC2764
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2764, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2765 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB2765 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2765 : Charge := ![-3, -2, 0, 1, 2, 2]
def sourceForm2765 : Integer.Sparse Master := [(Sum.inr 2365, 1), (Sum.inr 3319, 1), (Sum.inr 3593, 1), (Sum.inr 3594, 1), (Sum.inr 3595, 2), (Sum.inr 4075, -1)]

theorem sourceEq2765 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2765 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2765 + difference 0 5) (sourceB2765 + difference 5 0) sourceC2765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3319) := by
    have ha : (tripleCharges (sourceA2765 + difference 0 5) (sourceB2765 + difference 5 0) sourceC2765) = raw37814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2765 sourceB2765 sourceC2765 difference raw37814; decide +kernel
    rw [ha]
    exact (canonical37814 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2765 + difference 1 5) (sourceB2765 + difference 5 1) sourceC2765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2365) := by
    have ha : (tripleCharges (sourceA2765 + difference 1 5) (sourceB2765 + difference 5 1) sourceC2765) = raw37815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2765 sourceB2765 sourceC2765 difference raw37815; decide +kernel
    rw [ha]
    exact (canonical37815 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2765 + difference 2 5) (sourceB2765 + difference 5 2) sourceC2765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3593) := by
    have ha : (tripleCharges (sourceA2765 + difference 2 5) (sourceB2765 + difference 5 2) sourceC2765) = raw37816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2765 sourceB2765 sourceC2765 difference raw37816; decide +kernel
    rw [ha]
    exact (canonical37816 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2765 + difference 3 5) (sourceB2765 + difference 5 3) sourceC2765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3594) := by
    have ha : (tripleCharges (sourceA2765 + difference 3 5) (sourceB2765 + difference 5 3) sourceC2765) = raw37817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2765 sourceB2765 sourceC2765 difference raw37817; decide +kernel
    rw [ha]
    exact (canonical37817 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2765 + difference 4 5) (sourceB2765 + difference 5 4) sourceC2765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2765 + difference 4 5) (sourceB2765 + difference 5 4) sourceC2765) = raw37818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2765 sourceB2765 sourceC2765 difference raw37818; decide +kernel
    rw [ha]
    exact (canonical37818 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2765 + difference 5 5) (sourceB2765 + difference 5 5) sourceC2765) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2765 + difference 5 5) (sourceB2765 + difference 5 5) sourceC2765) = raw37781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2765 sourceB2765 sourceC2765 difference raw37781; decide +kernel
    rw [ha]
    exact (canonical37781 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2765 + sourceB2765) sourceC2765) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2765 + sourceB2765) sourceC2765) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2765 sourceB2765 sourceC2765 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2765 sourceB2765 sourceC2765
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2765, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2766 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB2766 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2766 : Charge := ![-3, -1, -1, 1, 1, 3]
def sourceForm2766 : Integer.Sparse Master := [(Sum.inr 2182, 2), (Sum.inr 3455, 4), (Sum.inr 4077, -1)]

theorem sourceEq2766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2766 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 0) (sourceB2766 + difference 0 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2182) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 0) (sourceB2766 + difference 0 3) sourceC2766) = raw37819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37819; decide +kernel
    rw [ha]
    exact (canonical37819 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 1) (sourceB2766 + difference 1 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 1) (sourceB2766 + difference 1 3) sourceC2766) = raw37820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37820; decide +kernel
    rw [ha]
    exact (canonical37820 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 2) (sourceB2766 + difference 2 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 2) (sourceB2766 + difference 2 3) sourceC2766) = raw37821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37821; decide +kernel
    rw [ha]
    exact (canonical37821 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 3) (sourceB2766 + difference 3 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 3) (sourceB2766 + difference 3 3) sourceC2766) = raw37822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37822; decide +kernel
    rw [ha]
    exact (canonical37822 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 4) (sourceB2766 + difference 4 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 4) (sourceB2766 + difference 4 3) sourceC2766) = raw37823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37823; decide +kernel
    rw [ha]
    exact (canonical37823 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 5) (sourceB2766 + difference 5 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2182) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 5) (sourceB2766 + difference 5 3) sourceC2766) = raw37824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37824; decide +kernel
    rw [ha]
    exact (canonical37824 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2766 + sourceB2766) sourceC2766) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4077) := by
    have ha : (doubleCharges (sourceA2766 + sourceB2766) sourceC2766) = raw37825 := by
      apply Matrix.ext; unfold doubleCharges sourceA2766 sourceB2766 sourceC2766 raw37825; decide +kernel
    rw [ha]
    exact (canonical37825 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2766 sourceB2766 sourceC2766
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2766, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
