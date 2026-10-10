import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical91
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical92
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical93
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical96

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA704 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB704 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC704 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceForm704 : Integer.Sparse Master := [(Sum.inr 1276, 1), (Sum.inr 2645, 1), (Sum.inr 2730, 1), (Sum.inr 2757, 1), (Sum.inr 2773, 2), (Sum.inr 4092, -1)]

theorem sourceEq704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm704 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA704 + difference 1 0) (sourceB704 + difference 0 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1276) := by
    have ha : (tripleCharges (sourceA704 + difference 1 0) (sourceB704 + difference 0 1) sourceC704) = raw11869 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11869; decide +kernel
    rw [ha]
    exact (canonical11869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA704 + difference 1 1) (sourceB704 + difference 1 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA704 + difference 1 1) (sourceB704 + difference 1 1) sourceC704) = raw11862 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11862; decide +kernel
    rw [ha]
    exact (canonical11862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA704 + difference 1 2) (sourceB704 + difference 2 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2645) := by
    have ha : (tripleCharges (sourceA704 + difference 1 2) (sourceB704 + difference 2 1) sourceC704) = raw11874 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11874; decide +kernel
    rw [ha]
    exact (canonical11874 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA704 + difference 1 3) (sourceB704 + difference 3 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA704 + difference 1 3) (sourceB704 + difference 3 1) sourceC704) = raw11875 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11875; decide +kernel
    rw [ha]
    exact (canonical11875 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA704 + difference 1 4) (sourceB704 + difference 4 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA704 + difference 1 4) (sourceB704 + difference 4 1) sourceC704) = raw11876 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11876; decide +kernel
    rw [ha]
    exact (canonical11876 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA704 + difference 1 5) (sourceB704 + difference 5 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA704 + difference 1 5) (sourceB704 + difference 5 1) sourceC704) = raw11877 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11877; decide +kernel
    rw [ha]
    exact (canonical11877 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA704 + sourceB704) sourceC704) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA704 + sourceB704) sourceC704) = raw11868 := by
      apply Matrix.ext; unfold doubleCharges sourceA704 sourceB704 sourceC704 raw11868; decide +kernel
    rw [ha]
    exact (canonical11868 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA704 sourceB704 sourceC704
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm704, Integer.Sparse.eval]
  linarith only [hs]

def sourceA705 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB705 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC705 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceForm705 : Integer.Sparse Master := [(Sum.inr 2493, 1), (Sum.inr 2494, 2), (Sum.inr 2508, 1), (Sum.inr 2730, 1), (Sum.inr 3812, 1), (Sum.inr 4092, -1)]

theorem sourceEq705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm705 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA705 + difference 0 1) (sourceB705 + difference 1 0) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA705 + difference 0 1) (sourceB705 + difference 1 0) sourceC705) = raw11863 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11863; decide +kernel
    rw [ha]
    exact (canonical11863 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA705 + difference 1 1) (sourceB705 + difference 1 1) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA705 + difference 1 1) (sourceB705 + difference 1 1) sourceC705) = raw11862 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11862; decide +kernel
    rw [ha]
    exact (canonical11862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA705 + difference 2 1) (sourceB705 + difference 1 2) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA705 + difference 2 1) (sourceB705 + difference 1 2) sourceC705) = raw11878 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11878; decide +kernel
    rw [ha]
    exact (canonical11878 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA705 + difference 3 1) (sourceB705 + difference 1 3) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA705 + difference 3 1) (sourceB705 + difference 1 3) sourceC705) = raw11879 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11879; decide +kernel
    rw [ha]
    exact (canonical11879 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA705 + difference 4 1) (sourceB705 + difference 1 4) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA705 + difference 4 1) (sourceB705 + difference 1 4) sourceC705) = raw11880 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11880; decide +kernel
    rw [ha]
    exact (canonical11880 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA705 + difference 5 1) (sourceB705 + difference 1 5) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA705 + difference 5 1) (sourceB705 + difference 1 5) sourceC705) = raw11881 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11881; decide +kernel
    rw [ha]
    exact (canonical11881 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA705 + sourceB705) sourceC705) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA705 + sourceB705) sourceC705) = raw11868 := by
      apply Matrix.ext; unfold doubleCharges sourceA705 sourceB705 sourceC705 raw11868; decide +kernel
    rw [ha]
    exact (canonical11868 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA705 sourceB705 sourceC705
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm705, Integer.Sparse.eval]
  linarith only [hs]

def sourceA706 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB706 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC706 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceForm706 : Integer.Sparse Master := [(Sum.inr 4406, 1), (Sum.inr 4407, 2), (Sum.inr 4414, 1), (Sum.inr 4473, 1), (Sum.inr 5004, 1), (Sum.inr 5005, 2), (Sum.inr 5011, 1), (Sum.inr 5150, 2), (Sum.inr 5184, 1), (Sum.inr 5185, 2), (Sum.inr 5202, 1), (Sum.inr 5243, 2), (Sum.inr 5244, 2), (Sum.inr 5265, 2), (Sum.inr 5266, 2), (Sum.inr 5270, 1), (Sum.inr 5301, 1), (Sum.inr 5429, 1), (Sum.inr 5431, 2), (Sum.inr 5450, 1), (Sum.inr 5472, 1)]

theorem sourceEq706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm706 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA706 + difference 0 1) (sourceB706 + difference 1 0) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA706 + difference 0 1) (sourceB706 + difference 1 0) sourceC706) = raw11882 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11882; decide +kernel
    rw [ha]
    exact (canonical11882 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA706 + difference 0 2) (sourceB706 + difference 2 0) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA706 + difference 0 2) (sourceB706 + difference 2 0) sourceC706) = raw11883 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11883; decide +kernel
    rw [ha]
    exact (canonical11883 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA706 + difference 0 3) (sourceB706 + difference 3 0) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA706 + difference 0 3) (sourceB706 + difference 3 0) sourceC706) = raw11884 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11884; decide +kernel
    rw [ha]
    exact (canonical11884 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA706 + difference 0 4) (sourceB706 + difference 4 0) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA706 + difference 0 4) (sourceB706 + difference 4 0) sourceC706) = raw11885 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11885; decide +kernel
    rw [ha]
    exact (canonical11885 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA706 + difference 0 5) (sourceB706 + difference 5 0) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA706 + difference 0 5) (sourceB706 + difference 5 0) sourceC706) = raw11886 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11886; decide +kernel
    rw [ha]
    exact (canonical11886 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA706 + difference 1 0) (sourceB706 + difference 0 1) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4473) := by
    have ha : (tripleCharges (sourceA706 + difference 1 0) (sourceB706 + difference 0 1) sourceC706) = raw11887 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11887; decide +kernel
    rw [ha]
    exact (canonical11887 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA706 + difference 1 2) (sourceB706 + difference 2 1) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA706 + difference 1 2) (sourceB706 + difference 2 1) sourceC706) = raw11888 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11888; decide +kernel
    rw [ha]
    exact (canonical11888 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA706 + difference 1 3) (sourceB706 + difference 3 1) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA706 + difference 1 3) (sourceB706 + difference 3 1) sourceC706) = raw11889 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11889; decide +kernel
    rw [ha]
    exact (canonical11889 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA706 + difference 1 4) (sourceB706 + difference 4 1) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA706 + difference 1 4) (sourceB706 + difference 4 1) sourceC706) = raw11890 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11890; decide +kernel
    rw [ha]
    exact (canonical11890 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA706 + difference 1 5) (sourceB706 + difference 5 1) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA706 + difference 1 5) (sourceB706 + difference 5 1) sourceC706) = raw11891 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11891; decide +kernel
    rw [ha]
    exact (canonical11891 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA706 + difference 2 0) (sourceB706 + difference 0 2) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4414) := by
    have ha : (tripleCharges (sourceA706 + difference 2 0) (sourceB706 + difference 0 2) sourceC706) = raw11892 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11892; decide +kernel
    rw [ha]
    exact (canonical11892 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA706 + difference 2 1) (sourceB706 + difference 1 2) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5011) := by
    have ha : (tripleCharges (sourceA706 + difference 2 1) (sourceB706 + difference 1 2) sourceC706) = raw11893 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11893; decide +kernel
    rw [ha]
    exact (canonical11893 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA706 + difference 2 3) (sourceB706 + difference 3 2) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA706 + difference 2 3) (sourceB706 + difference 3 2) sourceC706) = raw11894 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11894; decide +kernel
    rw [ha]
    exact (canonical11894 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA706 + difference 2 4) (sourceB706 + difference 4 2) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA706 + difference 2 4) (sourceB706 + difference 4 2) sourceC706) = raw11895 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11895; decide +kernel
    rw [ha]
    exact (canonical11895 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA706 + difference 2 5) (sourceB706 + difference 5 2) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA706 + difference 2 5) (sourceB706 + difference 5 2) sourceC706) = raw11896 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11896; decide +kernel
    rw [ha]
    exact (canonical11896 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA706 + difference 3 0) (sourceB706 + difference 0 3) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4407) := by
    have ha : (tripleCharges (sourceA706 + difference 3 0) (sourceB706 + difference 0 3) sourceC706) = raw11897 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11897; decide +kernel
    rw [ha]
    exact (canonical11897 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA706 + difference 3 1) (sourceB706 + difference 1 3) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5005) := by
    have ha : (tripleCharges (sourceA706 + difference 3 1) (sourceB706 + difference 1 3) sourceC706) = raw11898 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11898; decide +kernel
    rw [ha]
    exact (canonical11898 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA706 + difference 3 2) (sourceB706 + difference 2 3) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA706 + difference 3 2) (sourceB706 + difference 2 3) sourceC706) = raw11899 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11899; decide +kernel
    rw [ha]
    exact (canonical11899 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA706 + difference 3 4) (sourceB706 + difference 4 3) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA706 + difference 3 4) (sourceB706 + difference 4 3) sourceC706) = raw11900 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11900; decide +kernel
    rw [ha]
    exact (canonical11900 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA706 + difference 3 5) (sourceB706 + difference 5 3) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA706 + difference 3 5) (sourceB706 + difference 5 3) sourceC706) = raw11901 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11901; decide +kernel
    rw [ha]
    exact (canonical11901 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA706 + difference 4 0) (sourceB706 + difference 0 4) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4407) := by
    have ha : (tripleCharges (sourceA706 + difference 4 0) (sourceB706 + difference 0 4) sourceC706) = raw11902 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11902; decide +kernel
    rw [ha]
    exact (canonical11902 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA706 + difference 4 1) (sourceB706 + difference 1 4) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5005) := by
    have ha : (tripleCharges (sourceA706 + difference 4 1) (sourceB706 + difference 1 4) sourceC706) = raw11903 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11903; decide +kernel
    rw [ha]
    exact (canonical11903 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA706 + difference 4 2) (sourceB706 + difference 2 4) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA706 + difference 4 2) (sourceB706 + difference 2 4) sourceC706) = raw11904 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11904; decide +kernel
    rw [ha]
    exact (canonical11904 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA706 + difference 4 3) (sourceB706 + difference 3 4) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA706 + difference 4 3) (sourceB706 + difference 3 4) sourceC706) = raw11905 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11905; decide +kernel
    rw [ha]
    exact (canonical11905 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA706 + difference 4 5) (sourceB706 + difference 5 4) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA706 + difference 4 5) (sourceB706 + difference 5 4) sourceC706) = raw11906 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11906; decide +kernel
    rw [ha]
    exact (canonical11906 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA706 + difference 5 0) (sourceB706 + difference 0 5) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4406) := by
    have ha : (tripleCharges (sourceA706 + difference 5 0) (sourceB706 + difference 0 5) sourceC706) = raw11907 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11907; decide +kernel
    rw [ha]
    exact (canonical11907 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA706 + difference 5 1) (sourceB706 + difference 1 5) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5004) := by
    have ha : (tripleCharges (sourceA706 + difference 5 1) (sourceB706 + difference 1 5) sourceC706) = raw11908 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11908; decide +kernel
    rw [ha]
    exact (canonical11908 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA706 + difference 5 2) (sourceB706 + difference 2 5) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA706 + difference 5 2) (sourceB706 + difference 2 5) sourceC706) = raw11909 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11909; decide +kernel
    rw [ha]
    exact (canonical11909 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA706 + difference 5 3) (sourceB706 + difference 3 5) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA706 + difference 5 3) (sourceB706 + difference 3 5) sourceC706) = raw11910 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11910; decide +kernel
    rw [ha]
    exact (canonical11910 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA706 + difference 5 4) (sourceB706 + difference 4 5) sourceC706) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA706 + difference 5 4) (sourceB706 + difference 4 5) sourceC706) = raw11911 := by
      apply Matrix.ext; unfold tripleCharges sourceA706 sourceB706 sourceC706 difference raw11911; decide +kernel
    rw [ha]
    exact (canonical11911 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA706 sourceB706 sourceC706
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm706, Integer.Sparse.eval]
  linarith only [hs]

def sourceA707 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB707 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC707 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceForm707 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 988, 2), (Sum.inr 995, 1), (Sum.inr 1056, 1), (Sum.inr 2389, 1), (Sum.inr 2390, 2), (Sum.inr 2396, 1), (Sum.inr 2614, 1), (Sum.inr 2615, 2), (Sum.inr 2636, 1), (Sum.inr 2697, 2), (Sum.inr 2698, 2), (Sum.inr 2700, 2), (Sum.inr 2730, 2), (Sum.inr 2731, 2), (Sum.inr 2738, 1), (Sum.inr 2775, 1), (Sum.inr 3874, 1), (Sum.inr 3875, 2), (Sum.inr 3887, 1), (Sum.inr 4002, 1)]

theorem sourceEq707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm707 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA707 + difference 0 1) (sourceB707 + difference 1 0) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA707 + difference 0 1) (sourceB707 + difference 1 0) sourceC707) = raw11912 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11912; decide +kernel
    rw [ha]
    exact (canonical11912 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA707 + difference 0 2) (sourceB707 + difference 2 0) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4002) := by
    have ha : (tripleCharges (sourceA707 + difference 0 2) (sourceB707 + difference 2 0) sourceC707) = raw11913 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11913; decide +kernel
    rw [ha]
    exact (canonical11913 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA707 + difference 0 3) (sourceB707 + difference 3 0) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA707 + difference 0 3) (sourceB707 + difference 3 0) sourceC707) = raw11914 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11914; decide +kernel
    rw [ha]
    exact (canonical11914 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA707 + difference 0 4) (sourceB707 + difference 4 0) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA707 + difference 0 4) (sourceB707 + difference 4 0) sourceC707) = raw11915 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11915; decide +kernel
    rw [ha]
    exact (canonical11915 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA707 + difference 0 5) (sourceB707 + difference 5 0) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA707 + difference 0 5) (sourceB707 + difference 5 0) sourceC707) = raw11916 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11916; decide +kernel
    rw [ha]
    exact (canonical11916 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA707 + difference 1 0) (sourceB707 + difference 0 1) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1056) := by
    have ha : (tripleCharges (sourceA707 + difference 1 0) (sourceB707 + difference 0 1) sourceC707) = raw11917 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11917; decide +kernel
    rw [ha]
    exact (canonical11917 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA707 + difference 1 2) (sourceB707 + difference 2 1) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2636) := by
    have ha : (tripleCharges (sourceA707 + difference 1 2) (sourceB707 + difference 2 1) sourceC707) = raw11918 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11918; decide +kernel
    rw [ha]
    exact (canonical11918 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA707 + difference 1 3) (sourceB707 + difference 3 1) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA707 + difference 1 3) (sourceB707 + difference 3 1) sourceC707) = raw11919 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11919; decide +kernel
    rw [ha]
    exact (canonical11919 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA707 + difference 1 4) (sourceB707 + difference 4 1) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA707 + difference 1 4) (sourceB707 + difference 4 1) sourceC707) = raw11920 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11920; decide +kernel
    rw [ha]
    exact (canonical11920 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA707 + difference 1 5) (sourceB707 + difference 5 1) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2775) := by
    have ha : (tripleCharges (sourceA707 + difference 1 5) (sourceB707 + difference 5 1) sourceC707) = raw11921 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11921; decide +kernel
    rw [ha]
    exact (canonical11921 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA707 + difference 2 0) (sourceB707 + difference 0 2) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 995) := by
    have ha : (tripleCharges (sourceA707 + difference 2 0) (sourceB707 + difference 0 2) sourceC707) = raw11922 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11922; decide +kernel
    rw [ha]
    exact (canonical11922 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA707 + difference 2 1) (sourceB707 + difference 1 2) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2396) := by
    have ha : (tripleCharges (sourceA707 + difference 2 1) (sourceB707 + difference 1 2) sourceC707) = raw11923 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11923; decide +kernel
    rw [ha]
    exact (canonical11923 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA707 + difference 2 3) (sourceB707 + difference 3 2) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA707 + difference 2 3) (sourceB707 + difference 3 2) sourceC707) = raw11924 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11924; decide +kernel
    rw [ha]
    exact (canonical11924 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA707 + difference 2 4) (sourceB707 + difference 4 2) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA707 + difference 2 4) (sourceB707 + difference 4 2) sourceC707) = raw11925 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11925; decide +kernel
    rw [ha]
    exact (canonical11925 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA707 + difference 2 5) (sourceB707 + difference 5 2) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA707 + difference 2 5) (sourceB707 + difference 5 2) sourceC707) = raw11926 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11926; decide +kernel
    rw [ha]
    exact (canonical11926 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA707 + difference 3 0) (sourceB707 + difference 0 3) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA707 + difference 3 0) (sourceB707 + difference 0 3) sourceC707) = raw11927 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11927; decide +kernel
    rw [ha]
    exact (canonical11927 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA707 + difference 3 1) (sourceB707 + difference 1 3) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2390) := by
    have ha : (tripleCharges (sourceA707 + difference 3 1) (sourceB707 + difference 1 3) sourceC707) = raw11928 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11928; decide +kernel
    rw [ha]
    exact (canonical11928 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA707 + difference 3 2) (sourceB707 + difference 2 3) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA707 + difference 3 2) (sourceB707 + difference 2 3) sourceC707) = raw11929 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11929; decide +kernel
    rw [ha]
    exact (canonical11929 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA707 + difference 3 4) (sourceB707 + difference 4 3) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA707 + difference 3 4) (sourceB707 + difference 4 3) sourceC707) = raw11930 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11930; decide +kernel
    rw [ha]
    exact (canonical11930 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA707 + difference 3 5) (sourceB707 + difference 5 3) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA707 + difference 3 5) (sourceB707 + difference 5 3) sourceC707) = raw11931 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11931; decide +kernel
    rw [ha]
    exact (canonical11931 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA707 + difference 4 0) (sourceB707 + difference 0 4) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA707 + difference 4 0) (sourceB707 + difference 0 4) sourceC707) = raw11932 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11932; decide +kernel
    rw [ha]
    exact (canonical11932 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA707 + difference 4 1) (sourceB707 + difference 1 4) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2390) := by
    have ha : (tripleCharges (sourceA707 + difference 4 1) (sourceB707 + difference 1 4) sourceC707) = raw11933 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11933; decide +kernel
    rw [ha]
    exact (canonical11933 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA707 + difference 4 2) (sourceB707 + difference 2 4) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA707 + difference 4 2) (sourceB707 + difference 2 4) sourceC707) = raw11934 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11934; decide +kernel
    rw [ha]
    exact (canonical11934 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA707 + difference 4 3) (sourceB707 + difference 3 4) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA707 + difference 4 3) (sourceB707 + difference 3 4) sourceC707) = raw11935 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11935; decide +kernel
    rw [ha]
    exact (canonical11935 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA707 + difference 4 5) (sourceB707 + difference 5 4) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA707 + difference 4 5) (sourceB707 + difference 5 4) sourceC707) = raw11936 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11936; decide +kernel
    rw [ha]
    exact (canonical11936 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA707 + difference 5 0) (sourceB707 + difference 0 5) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 987) := by
    have ha : (tripleCharges (sourceA707 + difference 5 0) (sourceB707 + difference 0 5) sourceC707) = raw11937 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11937; decide +kernel
    rw [ha]
    exact (canonical11937 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA707 + difference 5 1) (sourceB707 + difference 1 5) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2389) := by
    have ha : (tripleCharges (sourceA707 + difference 5 1) (sourceB707 + difference 1 5) sourceC707) = raw11938 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11938; decide +kernel
    rw [ha]
    exact (canonical11938 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA707 + difference 5 2) (sourceB707 + difference 2 5) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA707 + difference 5 2) (sourceB707 + difference 2 5) sourceC707) = raw11939 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11939; decide +kernel
    rw [ha]
    exact (canonical11939 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA707 + difference 5 3) (sourceB707 + difference 3 5) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA707 + difference 5 3) (sourceB707 + difference 3 5) sourceC707) = raw11940 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11940; decide +kernel
    rw [ha]
    exact (canonical11940 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA707 + difference 5 4) (sourceB707 + difference 4 5) sourceC707) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA707 + difference 5 4) (sourceB707 + difference 4 5) sourceC707) = raw11941 := by
      apply Matrix.ext; unfold tripleCharges sourceA707 sourceB707 sourceC707 difference raw11941; decide +kernel
    rw [ha]
    exact (canonical11941 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA707 sourceB707 sourceC707
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm707, Integer.Sparse.eval]
  linarith only [hs]

def sourceA708 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB708 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC708 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceForm708 : Integer.Sparse Master := [(Sum.inr 1593, 1), (Sum.inr 1594, 1), (Sum.inr 1601, 2), (Sum.inr 1699, 1), (Sum.inr 2912, 1), (Sum.inr 2923, 2), (Sum.inr 3075, 1), (Sum.inr 3337, 1), (Sum.inr 3342, 2), (Sum.inr 3488, 2), (Sum.inr 3497, 2), (Sum.inr 3524, 1), (Sum.inr 3526, 2), (Sum.inr 3529, 2), (Sum.inr 3535, 2), (Sum.inr 3617, 1), (Sum.inr 3619, 1), (Sum.inr 3954, 1), (Sum.inr 3957, 1), (Sum.inr 4026, 2), (Sum.inr 4029, 1)]

theorem sourceEq708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm708 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA708 + difference 0 1) (sourceB708 + difference 1 0) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA708 + difference 0 1) (sourceB708 + difference 1 0) sourceC708) = raw11942 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11942; decide +kernel
    rw [ha]
    exact (canonical11942 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA708 + difference 0 2) (sourceB708 + difference 2 0) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA708 + difference 0 2) (sourceB708 + difference 2 0) sourceC708) = raw11943 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11943; decide +kernel
    rw [ha]
    exact (canonical11943 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA708 + difference 0 3) (sourceB708 + difference 3 0) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA708 + difference 0 3) (sourceB708 + difference 3 0) sourceC708) = raw11944 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11944; decide +kernel
    rw [ha]
    exact (canonical11944 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA708 + difference 0 4) (sourceB708 + difference 4 0) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA708 + difference 0 4) (sourceB708 + difference 4 0) sourceC708) = raw11945 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11945; decide +kernel
    rw [ha]
    exact (canonical11945 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA708 + difference 0 5) (sourceB708 + difference 5 0) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA708 + difference 0 5) (sourceB708 + difference 5 0) sourceC708) = raw11946 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11946; decide +kernel
    rw [ha]
    exact (canonical11946 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA708 + difference 1 0) (sourceB708 + difference 0 1) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA708 + difference 1 0) (sourceB708 + difference 0 1) sourceC708) = raw11947 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11947; decide +kernel
    rw [ha]
    exact (canonical11947 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA708 + difference 1 2) (sourceB708 + difference 2 1) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3617) := by
    have ha : (tripleCharges (sourceA708 + difference 1 2) (sourceB708 + difference 2 1) sourceC708) = raw11948 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11948; decide +kernel
    rw [ha]
    exact (canonical11948 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA708 + difference 1 3) (sourceB708 + difference 3 1) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA708 + difference 1 3) (sourceB708 + difference 3 1) sourceC708) = raw11949 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11949; decide +kernel
    rw [ha]
    exact (canonical11949 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA708 + difference 1 4) (sourceB708 + difference 4 1) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA708 + difference 1 4) (sourceB708 + difference 4 1) sourceC708) = raw11950 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11950; decide +kernel
    rw [ha]
    exact (canonical11950 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA708 + difference 1 5) (sourceB708 + difference 5 1) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA708 + difference 1 5) (sourceB708 + difference 5 1) sourceC708) = raw11951 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11951; decide +kernel
    rw [ha]
    exact (canonical11951 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA708 + difference 2 0) (sourceB708 + difference 0 2) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1593) := by
    have ha : (tripleCharges (sourceA708 + difference 2 0) (sourceB708 + difference 0 2) sourceC708) = raw11952 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11952; decide +kernel
    rw [ha]
    exact (canonical11952 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA708 + difference 2 1) (sourceB708 + difference 1 2) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2912) := by
    have ha : (tripleCharges (sourceA708 + difference 2 1) (sourceB708 + difference 1 2) sourceC708) = raw11953 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11953; decide +kernel
    rw [ha]
    exact (canonical11953 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA708 + difference 2 3) (sourceB708 + difference 3 2) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA708 + difference 2 3) (sourceB708 + difference 3 2) sourceC708) = raw11954 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11954; decide +kernel
    rw [ha]
    exact (canonical11954 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA708 + difference 2 4) (sourceB708 + difference 4 2) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA708 + difference 2 4) (sourceB708 + difference 4 2) sourceC708) = raw11955 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11955; decide +kernel
    rw [ha]
    exact (canonical11955 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA708 + difference 2 5) (sourceB708 + difference 5 2) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA708 + difference 2 5) (sourceB708 + difference 5 2) sourceC708) = raw11956 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11956; decide +kernel
    rw [ha]
    exact (canonical11956 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA708 + difference 3 0) (sourceB708 + difference 0 3) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1601) := by
    have ha : (tripleCharges (sourceA708 + difference 3 0) (sourceB708 + difference 0 3) sourceC708) = raw11957 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11957; decide +kernel
    rw [ha]
    exact (canonical11957 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA708 + difference 3 1) (sourceB708 + difference 1 3) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3342) := by
    have ha : (tripleCharges (sourceA708 + difference 3 1) (sourceB708 + difference 1 3) sourceC708) = raw11958 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11958; decide +kernel
    rw [ha]
    exact (canonical11958 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA708 + difference 3 2) (sourceB708 + difference 2 3) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA708 + difference 3 2) (sourceB708 + difference 2 3) sourceC708) = raw11959 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11959; decide +kernel
    rw [ha]
    exact (canonical11959 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA708 + difference 3 4) (sourceB708 + difference 4 3) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA708 + difference 3 4) (sourceB708 + difference 4 3) sourceC708) = raw11960 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11960; decide +kernel
    rw [ha]
    exact (canonical11960 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA708 + difference 3 5) (sourceB708 + difference 5 3) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA708 + difference 3 5) (sourceB708 + difference 5 3) sourceC708) = raw11961 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11961; decide +kernel
    rw [ha]
    exact (canonical11961 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA708 + difference 4 0) (sourceB708 + difference 0 4) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1601) := by
    have ha : (tripleCharges (sourceA708 + difference 4 0) (sourceB708 + difference 0 4) sourceC708) = raw11962 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11962; decide +kernel
    rw [ha]
    exact (canonical11962 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA708 + difference 4 1) (sourceB708 + difference 1 4) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3342) := by
    have ha : (tripleCharges (sourceA708 + difference 4 1) (sourceB708 + difference 1 4) sourceC708) = raw11963 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11963; decide +kernel
    rw [ha]
    exact (canonical11963 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA708 + difference 4 2) (sourceB708 + difference 2 4) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA708 + difference 4 2) (sourceB708 + difference 2 4) sourceC708) = raw11964 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11964; decide +kernel
    rw [ha]
    exact (canonical11964 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA708 + difference 4 3) (sourceB708 + difference 3 4) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA708 + difference 4 3) (sourceB708 + difference 3 4) sourceC708) = raw11965 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11965; decide +kernel
    rw [ha]
    exact (canonical11965 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA708 + difference 4 5) (sourceB708 + difference 5 4) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA708 + difference 4 5) (sourceB708 + difference 5 4) sourceC708) = raw11966 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11966; decide +kernel
    rw [ha]
    exact (canonical11966 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA708 + difference 5 0) (sourceB708 + difference 0 5) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1594) := by
    have ha : (tripleCharges (sourceA708 + difference 5 0) (sourceB708 + difference 0 5) sourceC708) = raw11967 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11967; decide +kernel
    rw [ha]
    exact (canonical11967 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA708 + difference 5 1) (sourceB708 + difference 1 5) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3337) := by
    have ha : (tripleCharges (sourceA708 + difference 5 1) (sourceB708 + difference 1 5) sourceC708) = raw11968 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11968; decide +kernel
    rw [ha]
    exact (canonical11968 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA708 + difference 5 2) (sourceB708 + difference 2 5) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA708 + difference 5 2) (sourceB708 + difference 2 5) sourceC708) = raw11969 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11969; decide +kernel
    rw [ha]
    exact (canonical11969 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA708 + difference 5 3) (sourceB708 + difference 3 5) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA708 + difference 5 3) (sourceB708 + difference 3 5) sourceC708) = raw11970 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11970; decide +kernel
    rw [ha]
    exact (canonical11970 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA708 + difference 5 4) (sourceB708 + difference 4 5) sourceC708) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA708 + difference 5 4) (sourceB708 + difference 4 5) sourceC708) = raw11971 := by
      apply Matrix.ext; unfold tripleCharges sourceA708 sourceB708 sourceC708 difference raw11971; decide +kernel
    rw [ha]
    exact (canonical11971 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA708 sourceB708 sourceC708
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm708, Integer.Sparse.eval]
  linarith only [hs]

def sourceA709 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB709 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC709 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceForm709 : Integer.Sparse Master := [(Sum.inr 3037, 1), (Sum.inr 3846, 1), (Sum.inr 3849, 2), (Sum.inr 3910, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

theorem sourceEq709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm709 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA709 + difference 0 0) (sourceB709 + difference 0 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA709 + difference 0 0) (sourceB709 + difference 0 0) sourceC709) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA709 + difference 0 1) (sourceB709 + difference 1 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA709 + difference 0 1) (sourceB709 + difference 1 0) sourceC709) = raw11973 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11973; decide +kernel
    rw [ha]
    exact (canonical11973 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA709 + difference 0 2) (sourceB709 + difference 2 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA709 + difference 0 2) (sourceB709 + difference 2 0) sourceC709) = raw11974 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11974; decide +kernel
    rw [ha]
    exact (canonical11974 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA709 + difference 0 3) (sourceB709 + difference 3 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA709 + difference 0 3) (sourceB709 + difference 3 0) sourceC709) = raw11975 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11975; decide +kernel
    rw [ha]
    exact (canonical11975 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA709 + difference 0 4) (sourceB709 + difference 4 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA709 + difference 0 4) (sourceB709 + difference 4 0) sourceC709) = raw11976 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11976; decide +kernel
    rw [ha]
    exact (canonical11976 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA709 + difference 0 5) (sourceB709 + difference 5 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA709 + difference 0 5) (sourceB709 + difference 5 0) sourceC709) = raw11977 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11977; decide +kernel
    rw [ha]
    exact (canonical11977 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA709 + sourceB709) sourceC709) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA709 + sourceB709) sourceC709) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA709 sourceB709 sourceC709 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA709 sourceB709 sourceC709
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm709, Integer.Sparse.eval]
  linarith only [hs]

def sourceA710 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB710 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC710 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceForm710 : Integer.Sparse Master := [(Sum.inr 1358, 2), (Sum.inr 1360, 1), (Sum.inr 1366, 1), (Sum.inr 1421, 1), (Sum.inr 3037, 1), (Sum.inr 4091, -1)]

theorem sourceEq710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm710 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA710 + difference 0 0) (sourceB710 + difference 0 0) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA710 + difference 0 0) (sourceB710 + difference 0 0) sourceC710) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA710 + difference 1 0) (sourceB710 + difference 0 1) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1366) := by
    have ha : (tripleCharges (sourceA710 + difference 1 0) (sourceB710 + difference 0 1) sourceC710) = raw11979 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11979; decide +kernel
    rw [ha]
    exact (canonical11979 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA710 + difference 2 0) (sourceB710 + difference 0 2) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1421) := by
    have ha : (tripleCharges (sourceA710 + difference 2 0) (sourceB710 + difference 0 2) sourceC710) = raw11980 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11980; decide +kernel
    rw [ha]
    exact (canonical11980 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA710 + difference 3 0) (sourceB710 + difference 0 3) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1358) := by
    have ha : (tripleCharges (sourceA710 + difference 3 0) (sourceB710 + difference 0 3) sourceC710) = raw11981 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11981; decide +kernel
    rw [ha]
    exact (canonical11981 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA710 + difference 4 0) (sourceB710 + difference 0 4) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1358) := by
    have ha : (tripleCharges (sourceA710 + difference 4 0) (sourceB710 + difference 0 4) sourceC710) = raw11982 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11982; decide +kernel
    rw [ha]
    exact (canonical11982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA710 + difference 5 0) (sourceB710 + difference 0 5) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1360) := by
    have ha : (tripleCharges (sourceA710 + difference 5 0) (sourceB710 + difference 0 5) sourceC710) = raw11983 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11983; decide +kernel
    rw [ha]
    exact (canonical11983 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA710 + sourceB710) sourceC710) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA710 + sourceB710) sourceC710) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA710 sourceB710 sourceC710 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA710 sourceB710 sourceC710
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm710, Integer.Sparse.eval]
  linarith only [hs]

def sourceA711 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB711 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC711 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceForm711 : Integer.Sparse Master := [(Sum.inr 1366, 1), (Sum.inr 2880, 1), (Sum.inr 3037, 3), (Sum.inr 3053, 1), (Sum.inr 4091, -1)]

theorem sourceEq711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm711 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA711 + difference 1 0) (sourceB711 + difference 0 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1366) := by
    have ha : (tripleCharges (sourceA711 + difference 1 0) (sourceB711 + difference 0 1) sourceC711) = raw11979 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11979; decide +kernel
    rw [ha]
    exact (canonical11979 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA711 + difference 1 1) (sourceB711 + difference 1 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA711 + difference 1 1) (sourceB711 + difference 1 1) sourceC711) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA711 + difference 1 2) (sourceB711 + difference 2 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA711 + difference 1 2) (sourceB711 + difference 2 1) sourceC711) = raw11984 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11984; decide +kernel
    rw [ha]
    exact (canonical11984 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA711 + difference 1 3) (sourceB711 + difference 3 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA711 + difference 1 3) (sourceB711 + difference 3 1) sourceC711) = raw11985 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11985; decide +kernel
    rw [ha]
    exact (canonical11985 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA711 + difference 1 4) (sourceB711 + difference 4 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA711 + difference 1 4) (sourceB711 + difference 4 1) sourceC711) = raw11986 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11986; decide +kernel
    rw [ha]
    exact (canonical11986 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA711 + difference 1 5) (sourceB711 + difference 5 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA711 + difference 1 5) (sourceB711 + difference 5 1) sourceC711) = raw11987 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11987; decide +kernel
    rw [ha]
    exact (canonical11987 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA711 + sourceB711) sourceC711) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA711 + sourceB711) sourceC711) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA711 sourceB711 sourceC711 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA711 sourceB711 sourceC711
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm711, Integer.Sparse.eval]
  linarith only [hs]

def sourceA712 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB712 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC712 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceForm712 : Integer.Sparse Master := [(Sum.inr 2564, 1), (Sum.inr 3008, 2), (Sum.inr 3009, 1), (Sum.inr 3037, 1), (Sum.inr 3846, 1), (Sum.inr 4091, -1)]

theorem sourceEq712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm712 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA712 + difference 0 1) (sourceB712 + difference 1 0) sourceC712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA712 + difference 0 1) (sourceB712 + difference 1 0) sourceC712) = raw11973 := by
      apply Matrix.ext; unfold tripleCharges sourceA712 sourceB712 sourceC712 difference raw11973; decide +kernel
    rw [ha]
    exact (canonical11973 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA712 + difference 1 1) (sourceB712 + difference 1 1) sourceC712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA712 + difference 1 1) (sourceB712 + difference 1 1) sourceC712) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA712 sourceB712 sourceC712 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA712 + difference 2 1) (sourceB712 + difference 1 2) sourceC712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2564) := by
    have ha : (tripleCharges (sourceA712 + difference 2 1) (sourceB712 + difference 1 2) sourceC712) = raw11988 := by
      apply Matrix.ext; unfold tripleCharges sourceA712 sourceB712 sourceC712 difference raw11988; decide +kernel
    rw [ha]
    exact (canonical11988 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA712 + difference 3 1) (sourceB712 + difference 1 3) sourceC712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3008) := by
    have ha : (tripleCharges (sourceA712 + difference 3 1) (sourceB712 + difference 1 3) sourceC712) = raw11989 := by
      apply Matrix.ext; unfold tripleCharges sourceA712 sourceB712 sourceC712 difference raw11989; decide +kernel
    rw [ha]
    exact (canonical11989 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA712 + difference 4 1) (sourceB712 + difference 1 4) sourceC712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3008) := by
    have ha : (tripleCharges (sourceA712 + difference 4 1) (sourceB712 + difference 1 4) sourceC712) = raw11990 := by
      apply Matrix.ext; unfold tripleCharges sourceA712 sourceB712 sourceC712 difference raw11990; decide +kernel
    rw [ha]
    exact (canonical11990 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA712 + difference 5 1) (sourceB712 + difference 1 5) sourceC712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3009) := by
    have ha : (tripleCharges (sourceA712 + difference 5 1) (sourceB712 + difference 1 5) sourceC712) = raw11991 := by
      apply Matrix.ext; unfold tripleCharges sourceA712 sourceB712 sourceC712 difference raw11991; decide +kernel
    rw [ha]
    exact (canonical11991 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA712 + sourceB712) sourceC712) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA712 + sourceB712) sourceC712) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA712 sourceB712 sourceC712 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA712 sourceB712 sourceC712
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm712, Integer.Sparse.eval]
  linarith only [hs]

def sourceA713 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB713 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC713 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceForm713 : Integer.Sparse Master := [(Sum.inr 2862, 2), (Sum.inr 2864, 1), (Sum.inr 2880, 1), (Sum.inr 3037, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

theorem sourceEq713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm713 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA713 + difference 0 2) (sourceB713 + difference 2 0) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA713 + difference 0 2) (sourceB713 + difference 2 0) sourceC713) = raw11974 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11974; decide +kernel
    rw [ha]
    exact (canonical11974 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA713 + difference 1 2) (sourceB713 + difference 2 1) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA713 + difference 1 2) (sourceB713 + difference 2 1) sourceC713) = raw11984 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11984; decide +kernel
    rw [ha]
    exact (canonical11984 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA713 + difference 2 2) (sourceB713 + difference 2 2) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA713 + difference 2 2) (sourceB713 + difference 2 2) sourceC713) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA713 + difference 3 2) (sourceB713 + difference 2 3) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA713 + difference 3 2) (sourceB713 + difference 2 3) sourceC713) = raw11992 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11992; decide +kernel
    rw [ha]
    exact (canonical11992 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA713 + difference 4 2) (sourceB713 + difference 2 4) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA713 + difference 4 2) (sourceB713 + difference 2 4) sourceC713) = raw11993 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11993; decide +kernel
    rw [ha]
    exact (canonical11993 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA713 + difference 5 2) (sourceB713 + difference 2 5) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA713 + difference 5 2) (sourceB713 + difference 2 5) sourceC713) = raw11994 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11994; decide +kernel
    rw [ha]
    exact (canonical11994 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA713 + sourceB713) sourceC713) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA713 + sourceB713) sourceC713) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA713 sourceB713 sourceC713 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA713 sourceB713 sourceC713
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm713, Integer.Sparse.eval]
  linarith only [hs]

def sourceA714 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB714 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC714 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceForm714 : Integer.Sparse Master := [(Sum.inr 2573, 1), (Sum.inr 3029, 1), (Sum.inr 3030, 1), (Sum.inr 3037, 2), (Sum.inr 3849, 1), (Sum.inr 4091, -1)]

theorem sourceEq714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm714 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA714 + difference 0 3) (sourceB714 + difference 3 0) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA714 + difference 0 3) (sourceB714 + difference 3 0) sourceC714) = raw11975 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11975; decide +kernel
    rw [ha]
    exact (canonical11975 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA714 + difference 1 3) (sourceB714 + difference 3 1) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA714 + difference 1 3) (sourceB714 + difference 3 1) sourceC714) = raw11985 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11985; decide +kernel
    rw [ha]
    exact (canonical11985 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA714 + difference 2 3) (sourceB714 + difference 3 2) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA714 + difference 2 3) (sourceB714 + difference 3 2) sourceC714) = raw11995 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11995; decide +kernel
    rw [ha]
    exact (canonical11995 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA714 + difference 3 3) (sourceB714 + difference 3 3) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA714 + difference 3 3) (sourceB714 + difference 3 3) sourceC714) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA714 + difference 4 3) (sourceB714 + difference 3 4) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA714 + difference 4 3) (sourceB714 + difference 3 4) sourceC714) = raw11996 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11996; decide +kernel
    rw [ha]
    exact (canonical11996 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA714 + difference 5 3) (sourceB714 + difference 3 5) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA714 + difference 5 3) (sourceB714 + difference 3 5) sourceC714) = raw11997 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11997; decide +kernel
    rw [ha]
    exact (canonical11997 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA714 + sourceB714) sourceC714) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA714 + sourceB714) sourceC714) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA714 sourceB714 sourceC714 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA714 sourceB714 sourceC714
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm714, Integer.Sparse.eval]
  linarith only [hs]

def sourceA715 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB715 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC715 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm715 : Integer.Sparse Master := [(Sum.inr 4793, 1), (Sum.inr 4794, 1), (Sum.inr 4795, 1), (Sum.inr 4805, 2), (Sum.inr 4806, 2), (Sum.inr 4878, 1), (Sum.inr 4889, 1), (Sum.inr 5226, 2), (Sum.inr 5227, 1), (Sum.inr 5230, 1), (Sum.inr 5231, 3), (Sum.inr 5256, 1), (Sum.inr 5257, 3), (Sum.inr 5262, 2), (Sum.inr 5263, 2), (Sum.inr 5265, 2), (Sum.inr 5292, 1), (Sum.inr 5299, 2), (Sum.inr 5301, 1)]

theorem sourceEq715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm715 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA715 + difference 0 1) (sourceB715 + difference 1 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA715 + difference 0 1) (sourceB715 + difference 1 0) sourceC715) = raw11998 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11998; decide +kernel
    rw [ha]
    exact (canonical11998 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA715 + difference 0 2) (sourceB715 + difference 2 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA715 + difference 0 2) (sourceB715 + difference 2 0) sourceC715) = raw11664 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11664; decide +kernel
    rw [ha]
    exact (canonical11664 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA715 + difference 0 3) (sourceB715 + difference 3 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA715 + difference 0 3) (sourceB715 + difference 3 0) sourceC715) = raw11999 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11999; decide +kernel
    rw [ha]
    exact (canonical11999 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA715 + difference 0 4) (sourceB715 + difference 4 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA715 + difference 0 4) (sourceB715 + difference 4 0) sourceC715) = raw12000 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12000; decide +kernel
    rw [ha]
    exact (canonical12000 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA715 + difference 0 5) (sourceB715 + difference 5 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA715 + difference 0 5) (sourceB715 + difference 5 0) sourceC715) = raw12001 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12001; decide +kernel
    rw [ha]
    exact (canonical12001 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA715 + difference 1 0) (sourceB715 + difference 0 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA715 + difference 1 0) (sourceB715 + difference 0 1) sourceC715) = raw12002 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12002; decide +kernel
    rw [ha]
    exact (canonical12002 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA715 + difference 1 2) (sourceB715 + difference 2 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA715 + difference 1 2) (sourceB715 + difference 2 1) sourceC715) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA715 + difference 1 3) (sourceB715 + difference 3 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA715 + difference 1 3) (sourceB715 + difference 3 1) sourceC715) = raw12003 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12003; decide +kernel
    rw [ha]
    exact (canonical12003 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA715 + difference 1 4) (sourceB715 + difference 4 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA715 + difference 1 4) (sourceB715 + difference 4 1) sourceC715) = raw12004 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12004; decide +kernel
    rw [ha]
    exact (canonical12004 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA715 + difference 1 5) (sourceB715 + difference 5 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA715 + difference 1 5) (sourceB715 + difference 5 1) sourceC715) = raw12005 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12005; decide +kernel
    rw [ha]
    exact (canonical12005 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA715 + difference 2 0) (sourceB715 + difference 0 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA715 + difference 2 0) (sourceB715 + difference 0 2) sourceC715) = raw12006 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12006; decide +kernel
    rw [ha]
    exact (canonical12006 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA715 + difference 2 1) (sourceB715 + difference 1 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4794) := by
    have ha : (tripleCharges (sourceA715 + difference 2 1) (sourceB715 + difference 1 2) sourceC715) = raw12007 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12007; decide +kernel
    rw [ha]
    exact (canonical12007 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA715 + difference 2 3) (sourceB715 + difference 3 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA715 + difference 2 3) (sourceB715 + difference 3 2) sourceC715) = raw12008 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12008; decide +kernel
    rw [ha]
    exact (canonical12008 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA715 + difference 2 4) (sourceB715 + difference 4 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA715 + difference 2 4) (sourceB715 + difference 4 2) sourceC715) = raw12009 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12009; decide +kernel
    rw [ha]
    exact (canonical12009 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA715 + difference 2 5) (sourceB715 + difference 5 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA715 + difference 2 5) (sourceB715 + difference 5 2) sourceC715) = raw12010 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12010; decide +kernel
    rw [ha]
    exact (canonical12010 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA715 + difference 3 0) (sourceB715 + difference 0 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA715 + difference 3 0) (sourceB715 + difference 0 3) sourceC715) = raw12011 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12011; decide +kernel
    rw [ha]
    exact (canonical12011 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA715 + difference 3 1) (sourceB715 + difference 1 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA715 + difference 3 1) (sourceB715 + difference 1 3) sourceC715) = raw12012 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12012; decide +kernel
    rw [ha]
    exact (canonical12012 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA715 + difference 3 2) (sourceB715 + difference 2 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA715 + difference 3 2) (sourceB715 + difference 2 3) sourceC715) = raw11679 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11679; decide +kernel
    rw [ha]
    exact (canonical11679 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA715 + difference 3 4) (sourceB715 + difference 4 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA715 + difference 3 4) (sourceB715 + difference 4 3) sourceC715) = raw12013 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12013; decide +kernel
    rw [ha]
    exact (canonical12013 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA715 + difference 3 5) (sourceB715 + difference 5 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA715 + difference 3 5) (sourceB715 + difference 5 3) sourceC715) = raw12014 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12014; decide +kernel
    rw [ha]
    exact (canonical12014 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA715 + difference 4 0) (sourceB715 + difference 0 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA715 + difference 4 0) (sourceB715 + difference 0 4) sourceC715) = raw12015 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12015; decide +kernel
    rw [ha]
    exact (canonical12015 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA715 + difference 4 1) (sourceB715 + difference 1 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA715 + difference 4 1) (sourceB715 + difference 1 4) sourceC715) = raw12016 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12016; decide +kernel
    rw [ha]
    exact (canonical12016 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA715 + difference 4 2) (sourceB715 + difference 2 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA715 + difference 4 2) (sourceB715 + difference 2 4) sourceC715) = raw11684 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11684; decide +kernel
    rw [ha]
    exact (canonical11684 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA715 + difference 4 3) (sourceB715 + difference 3 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA715 + difference 4 3) (sourceB715 + difference 3 4) sourceC715) = raw12017 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12017; decide +kernel
    rw [ha]
    exact (canonical12017 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA715 + difference 4 5) (sourceB715 + difference 5 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA715 + difference 4 5) (sourceB715 + difference 5 4) sourceC715) = raw12018 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12018; decide +kernel
    rw [ha]
    exact (canonical12018 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA715 + difference 5 0) (sourceB715 + difference 0 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA715 + difference 5 0) (sourceB715 + difference 0 5) sourceC715) = raw11670 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11670; decide +kernel
    rw [ha]
    exact (canonical11670 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA715 + difference 5 1) (sourceB715 + difference 1 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5230) := by
    have ha : (tripleCharges (sourceA715 + difference 5 1) (sourceB715 + difference 1 5) sourceC715) = raw11671 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11671; decide +kernel
    rw [ha]
    exact (canonical11671 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA715 + difference 5 2) (sourceB715 + difference 2 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA715 + difference 5 2) (sourceB715 + difference 2 5) sourceC715) = raw12019 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12019; decide +kernel
    rw [ha]
    exact (canonical12019 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA715 + difference 5 3) (sourceB715 + difference 3 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5262) := by
    have ha : (tripleCharges (sourceA715 + difference 5 3) (sourceB715 + difference 3 5) sourceC715) = raw11672 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11672; decide +kernel
    rw [ha]
    exact (canonical11672 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA715 + difference 5 4) (sourceB715 + difference 4 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5262) := by
    have ha : (tripleCharges (sourceA715 + difference 5 4) (sourceB715 + difference 4 5) sourceC715) = raw11673 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11673; decide +kernel
    rw [ha]
    exact (canonical11673 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA715 sourceB715 sourceC715
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm715, Integer.Sparse.eval]
  linarith only [hs]

def sourceA716 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB716 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC716 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm716 : Integer.Sparse Master := [(Sum.inr 2117, 1), (Sum.inr 2118, 2), (Sum.inr 2131, 1), (Sum.inr 2213, 1), (Sum.inr 2214, 2), (Sum.inr 2219, 1), (Sum.inr 2277, 1), (Sum.inr 2675, 1), (Sum.inr 2676, 2), (Sum.inr 2720, 1), (Sum.inr 2721, 2), (Sum.inr 2727, 2), (Sum.inr 2728, 2), (Sum.inr 2730, 2), (Sum.inr 2766, 1), (Sum.inr 2773, 2), (Sum.inr 2775, 1), (Sum.inr 3043, 1), (Sum.inr 3087, 1), (Sum.inr 3091, 2), (Sum.inr 3093, 1)]

theorem sourceEq716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm716 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA716 + difference 0 1) (sourceB716 + difference 1 0) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA716 + difference 0 1) (sourceB716 + difference 1 0) sourceC716) = raw12020 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12020; decide +kernel
    rw [ha]
    exact (canonical12020 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA716 + difference 0 2) (sourceB716 + difference 2 0) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA716 + difference 0 2) (sourceB716 + difference 2 0) sourceC716) = raw11694 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw11694; decide +kernel
    rw [ha]
    exact (canonical11694 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA716 + difference 0 3) (sourceB716 + difference 3 0) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA716 + difference 0 3) (sourceB716 + difference 3 0) sourceC716) = raw12021 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12021; decide +kernel
    rw [ha]
    exact (canonical12021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA716 + difference 0 4) (sourceB716 + difference 4 0) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA716 + difference 0 4) (sourceB716 + difference 4 0) sourceC716) = raw12022 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12022; decide +kernel
    rw [ha]
    exact (canonical12022 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA716 + difference 0 5) (sourceB716 + difference 5 0) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3093) := by
    have ha : (tripleCharges (sourceA716 + difference 0 5) (sourceB716 + difference 5 0) sourceC716) = raw12023 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12023; decide +kernel
    rw [ha]
    exact (canonical12023 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA716 + difference 1 0) (sourceB716 + difference 0 1) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA716 + difference 1 0) (sourceB716 + difference 0 1) sourceC716) = raw12024 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12024; decide +kernel
    rw [ha]
    exact (canonical12024 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA716 + difference 1 2) (sourceB716 + difference 2 1) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA716 + difference 1 2) (sourceB716 + difference 2 1) sourceC716) = raw11699 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw11699; decide +kernel
    rw [ha]
    exact (canonical11699 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA716 + difference 1 3) (sourceB716 + difference 3 1) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA716 + difference 1 3) (sourceB716 + difference 3 1) sourceC716) = raw12025 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12025; decide +kernel
    rw [ha]
    exact (canonical12025 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA716 + difference 1 4) (sourceB716 + difference 4 1) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA716 + difference 1 4) (sourceB716 + difference 4 1) sourceC716) = raw12026 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12026; decide +kernel
    rw [ha]
    exact (canonical12026 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA716 + difference 1 5) (sourceB716 + difference 5 1) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2775) := by
    have ha : (tripleCharges (sourceA716 + difference 1 5) (sourceB716 + difference 5 1) sourceC716) = raw12027 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12027; decide +kernel
    rw [ha]
    exact (canonical12027 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA716 + difference 2 0) (sourceB716 + difference 0 2) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA716 + difference 2 0) (sourceB716 + difference 0 2) sourceC716) = raw12028 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12028; decide +kernel
    rw [ha]
    exact (canonical12028 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA716 + difference 2 1) (sourceB716 + difference 1 2) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2117) := by
    have ha : (tripleCharges (sourceA716 + difference 2 1) (sourceB716 + difference 1 2) sourceC716) = raw12029 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12029; decide +kernel
    rw [ha]
    exact (canonical12029 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA716 + difference 2 3) (sourceB716 + difference 3 2) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2118) := by
    have ha : (tripleCharges (sourceA716 + difference 2 3) (sourceB716 + difference 3 2) sourceC716) = raw12030 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12030; decide +kernel
    rw [ha]
    exact (canonical12030 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA716 + difference 2 4) (sourceB716 + difference 4 2) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2118) := by
    have ha : (tripleCharges (sourceA716 + difference 2 4) (sourceB716 + difference 4 2) sourceC716) = raw12031 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12031; decide +kernel
    rw [ha]
    exact (canonical12031 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA716 + difference 2 5) (sourceB716 + difference 5 2) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2131) := by
    have ha : (tripleCharges (sourceA716 + difference 2 5) (sourceB716 + difference 5 2) sourceC716) = raw12032 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12032; decide +kernel
    rw [ha]
    exact (canonical12032 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA716 + difference 3 0) (sourceB716 + difference 0 3) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA716 + difference 3 0) (sourceB716 + difference 0 3) sourceC716) = raw12033 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12033; decide +kernel
    rw [ha]
    exact (canonical12033 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA716 + difference 3 1) (sourceB716 + difference 1 3) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA716 + difference 3 1) (sourceB716 + difference 1 3) sourceC716) = raw12034 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12034; decide +kernel
    rw [ha]
    exact (canonical12034 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA716 + difference 3 2) (sourceB716 + difference 2 3) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA716 + difference 3 2) (sourceB716 + difference 2 3) sourceC716) = raw11709 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw11709; decide +kernel
    rw [ha]
    exact (canonical11709 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA716 + difference 3 4) (sourceB716 + difference 4 3) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA716 + difference 3 4) (sourceB716 + difference 4 3) sourceC716) = raw12035 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12035; decide +kernel
    rw [ha]
    exact (canonical12035 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA716 + difference 3 5) (sourceB716 + difference 5 3) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA716 + difference 3 5) (sourceB716 + difference 5 3) sourceC716) = raw12036 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12036; decide +kernel
    rw [ha]
    exact (canonical12036 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA716 + difference 4 0) (sourceB716 + difference 0 4) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA716 + difference 4 0) (sourceB716 + difference 0 4) sourceC716) = raw12037 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12037; decide +kernel
    rw [ha]
    exact (canonical12037 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA716 + difference 4 1) (sourceB716 + difference 1 4) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA716 + difference 4 1) (sourceB716 + difference 1 4) sourceC716) = raw12038 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12038; decide +kernel
    rw [ha]
    exact (canonical12038 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA716 + difference 4 2) (sourceB716 + difference 2 4) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA716 + difference 4 2) (sourceB716 + difference 2 4) sourceC716) = raw11714 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw11714; decide +kernel
    rw [ha]
    exact (canonical11714 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA716 + difference 4 3) (sourceB716 + difference 3 4) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA716 + difference 4 3) (sourceB716 + difference 3 4) sourceC716) = raw12039 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12039; decide +kernel
    rw [ha]
    exact (canonical12039 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA716 + difference 4 5) (sourceB716 + difference 5 4) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA716 + difference 4 5) (sourceB716 + difference 5 4) sourceC716) = raw12040 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12040; decide +kernel
    rw [ha]
    exact (canonical12040 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA716 + difference 5 0) (sourceB716 + difference 0 5) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA716 + difference 5 0) (sourceB716 + difference 0 5) sourceC716) = raw11700 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw11700; decide +kernel
    rw [ha]
    exact (canonical11700 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA716 + difference 5 1) (sourceB716 + difference 1 5) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2675) := by
    have ha : (tripleCharges (sourceA716 + difference 5 1) (sourceB716 + difference 1 5) sourceC716) = raw11701 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw11701; decide +kernel
    rw [ha]
    exact (canonical11701 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA716 + difference 5 2) (sourceB716 + difference 2 5) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA716 + difference 5 2) (sourceB716 + difference 2 5) sourceC716) = raw12041 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw12041; decide +kernel
    rw [ha]
    exact (canonical12041 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA716 + difference 5 3) (sourceB716 + difference 3 5) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2727) := by
    have ha : (tripleCharges (sourceA716 + difference 5 3) (sourceB716 + difference 3 5) sourceC716) = raw11702 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw11702; decide +kernel
    rw [ha]
    exact (canonical11702 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA716 + difference 5 4) (sourceB716 + difference 4 5) sourceC716) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2727) := by
    have ha : (tripleCharges (sourceA716 + difference 5 4) (sourceB716 + difference 4 5) sourceC716) = raw11703 := by
      apply Matrix.ext; unfold tripleCharges sourceA716 sourceB716 sourceC716 difference raw11703; decide +kernel
    rw [ha]
    exact (canonical11703 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA716 sourceB716 sourceC716
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm716, Integer.Sparse.eval]
  linarith only [hs]

def sourceA717 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB717 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC717 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm717 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 2011, 1), (Sum.inr 2024, 2), (Sum.inr 2234, 1), (Sum.inr 2669, 2), (Sum.inr 2671, 1), (Sum.inr 2676, 1), (Sum.inr 2721, 1), (Sum.inr 3034, 2), (Sum.inr 3036, 2), (Sum.inr 3037, 2), (Sum.inr 3041, 1), (Sum.inr 3043, 2), (Sum.inr 3051, 2), (Sum.inr 3053, 1), (Sum.inr 3085, 1), (Sum.inr 3087, 2), (Sum.inr 3100, 1), (Sum.inr 3199, 1), (Sum.inr 3203, 2), (Sum.inr 3223, 1)]

theorem sourceEq717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm717 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA717 + difference 0 1) (sourceB717 + difference 1 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA717 + difference 0 1) (sourceB717 + difference 1 0) sourceC717) = raw12042 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12042; decide +kernel
    rw [ha]
    exact (canonical12042 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA717 + difference 0 2) (sourceB717 + difference 2 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA717 + difference 0 2) (sourceB717 + difference 2 0) sourceC717) = raw11724 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11724; decide +kernel
    rw [ha]
    exact (canonical11724 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA717 + difference 0 3) (sourceB717 + difference 3 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA717 + difference 0 3) (sourceB717 + difference 3 0) sourceC717) = raw12043 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12043; decide +kernel
    rw [ha]
    exact (canonical12043 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA717 + difference 0 4) (sourceB717 + difference 4 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA717 + difference 0 4) (sourceB717 + difference 4 0) sourceC717) = raw12044 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12044; decide +kernel
    rw [ha]
    exact (canonical12044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA717 + difference 0 5) (sourceB717 + difference 5 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA717 + difference 0 5) (sourceB717 + difference 5 0) sourceC717) = raw12045 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12045; decide +kernel
    rw [ha]
    exact (canonical12045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA717 + difference 1 0) (sourceB717 + difference 0 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA717 + difference 1 0) (sourceB717 + difference 0 1) sourceC717) = raw12046 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12046; decide +kernel
    rw [ha]
    exact (canonical12046 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA717 + difference 1 2) (sourceB717 + difference 2 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA717 + difference 1 2) (sourceB717 + difference 2 1) sourceC717) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA717 + difference 1 3) (sourceB717 + difference 3 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA717 + difference 1 3) (sourceB717 + difference 3 1) sourceC717) = raw12047 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12047; decide +kernel
    rw [ha]
    exact (canonical12047 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA717 + difference 1 4) (sourceB717 + difference 4 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA717 + difference 1 4) (sourceB717 + difference 4 1) sourceC717) = raw12048 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12048; decide +kernel
    rw [ha]
    exact (canonical12048 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA717 + difference 1 5) (sourceB717 + difference 5 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA717 + difference 1 5) (sourceB717 + difference 5 1) sourceC717) = raw12049 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12049; decide +kernel
    rw [ha]
    exact (canonical12049 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA717 + difference 2 0) (sourceB717 + difference 0 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA717 + difference 2 0) (sourceB717 + difference 0 2) sourceC717) = raw12050 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12050; decide +kernel
    rw [ha]
    exact (canonical12050 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA717 + difference 2 1) (sourceB717 + difference 1 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2011) := by
    have ha : (tripleCharges (sourceA717 + difference 2 1) (sourceB717 + difference 1 2) sourceC717) = raw12051 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12051; decide +kernel
    rw [ha]
    exact (canonical12051 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA717 + difference 2 3) (sourceB717 + difference 3 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2024) := by
    have ha : (tripleCharges (sourceA717 + difference 2 3) (sourceB717 + difference 3 2) sourceC717) = raw12052 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12052; decide +kernel
    rw [ha]
    exact (canonical12052 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA717 + difference 2 4) (sourceB717 + difference 4 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2024) := by
    have ha : (tripleCharges (sourceA717 + difference 2 4) (sourceB717 + difference 4 2) sourceC717) = raw12053 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12053; decide +kernel
    rw [ha]
    exact (canonical12053 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA717 + difference 2 5) (sourceB717 + difference 5 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA717 + difference 2 5) (sourceB717 + difference 5 2) sourceC717) = raw12054 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12054; decide +kernel
    rw [ha]
    exact (canonical12054 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA717 + difference 3 0) (sourceB717 + difference 0 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3203) := by
    have ha : (tripleCharges (sourceA717 + difference 3 0) (sourceB717 + difference 0 3) sourceC717) = raw12055 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12055; decide +kernel
    rw [ha]
    exact (canonical12055 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA717 + difference 3 1) (sourceB717 + difference 1 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA717 + difference 3 1) (sourceB717 + difference 1 3) sourceC717) = raw12056 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12056; decide +kernel
    rw [ha]
    exact (canonical12056 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA717 + difference 3 2) (sourceB717 + difference 2 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA717 + difference 3 2) (sourceB717 + difference 2 3) sourceC717) = raw11739 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11739; decide +kernel
    rw [ha]
    exact (canonical11739 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA717 + difference 3 4) (sourceB717 + difference 4 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA717 + difference 3 4) (sourceB717 + difference 4 3) sourceC717) = raw12057 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12057; decide +kernel
    rw [ha]
    exact (canonical12057 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA717 + difference 3 5) (sourceB717 + difference 5 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA717 + difference 3 5) (sourceB717 + difference 5 3) sourceC717) = raw12058 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12058; decide +kernel
    rw [ha]
    exact (canonical12058 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA717 + difference 4 0) (sourceB717 + difference 0 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3203) := by
    have ha : (tripleCharges (sourceA717 + difference 4 0) (sourceB717 + difference 0 4) sourceC717) = raw12059 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12059; decide +kernel
    rw [ha]
    exact (canonical12059 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA717 + difference 4 1) (sourceB717 + difference 1 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA717 + difference 4 1) (sourceB717 + difference 1 4) sourceC717) = raw12060 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12060; decide +kernel
    rw [ha]
    exact (canonical12060 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA717 + difference 4 2) (sourceB717 + difference 2 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA717 + difference 4 2) (sourceB717 + difference 2 4) sourceC717) = raw11744 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11744; decide +kernel
    rw [ha]
    exact (canonical11744 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA717 + difference 4 3) (sourceB717 + difference 3 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA717 + difference 4 3) (sourceB717 + difference 3 4) sourceC717) = raw12061 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12061; decide +kernel
    rw [ha]
    exact (canonical12061 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA717 + difference 4 5) (sourceB717 + difference 5 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA717 + difference 4 5) (sourceB717 + difference 5 4) sourceC717) = raw12062 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12062; decide +kernel
    rw [ha]
    exact (canonical12062 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA717 + difference 5 0) (sourceB717 + difference 0 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA717 + difference 5 0) (sourceB717 + difference 0 5) sourceC717) = raw11730 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11730; decide +kernel
    rw [ha]
    exact (canonical11730 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA717 + difference 5 1) (sourceB717 + difference 1 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3041) := by
    have ha : (tripleCharges (sourceA717 + difference 5 1) (sourceB717 + difference 1 5) sourceC717) = raw11731 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11731; decide +kernel
    rw [ha]
    exact (canonical11731 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA717 + difference 5 2) (sourceB717 + difference 2 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA717 + difference 5 2) (sourceB717 + difference 2 5) sourceC717) = raw12063 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12063; decide +kernel
    rw [ha]
    exact (canonical12063 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA717 + difference 5 3) (sourceB717 + difference 3 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA717 + difference 5 3) (sourceB717 + difference 3 5) sourceC717) = raw11732 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11732; decide +kernel
    rw [ha]
    exact (canonical11732 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA717 + difference 5 4) (sourceB717 + difference 4 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA717 + difference 5 4) (sourceB717 + difference 4 5) sourceC717) = raw11733 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11733; decide +kernel
    rw [ha]
    exact (canonical11733 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA717 sourceB717 sourceC717
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm717, Integer.Sparse.eval]
  linarith only [hs]

def sourceA718 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB718 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC718 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm718 : Integer.Sparse Master := [(Sum.inr 3376, 2), (Sum.inr 3378, 1), (Sum.inr 3390, 1), (Sum.inr 3526, 1), (Sum.inr 3532, 1), (Sum.inr 4083, -1)]

theorem sourceEq718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm718 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA718 + difference 0 0) (sourceB718 + difference 0 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA718 + difference 0 0) (sourceB718 + difference 0 0) sourceC718) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA718 + difference 0 1) (sourceB718 + difference 1 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA718 + difference 0 1) (sourceB718 + difference 1 0) sourceC718) = raw12064 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw12064; decide +kernel
    rw [ha]
    exact (canonical12064 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA718 + difference 0 2) (sourceB718 + difference 2 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA718 + difference 0 2) (sourceB718 + difference 2 0) sourceC718) = raw11755 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw11755; decide +kernel
    rw [ha]
    exact (canonical11755 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA718 + difference 0 3) (sourceB718 + difference 3 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA718 + difference 0 3) (sourceB718 + difference 3 0) sourceC718) = raw12065 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw12065; decide +kernel
    rw [ha]
    exact (canonical12065 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA718 + difference 0 4) (sourceB718 + difference 4 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA718 + difference 0 4) (sourceB718 + difference 4 0) sourceC718) = raw12066 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw12066; decide +kernel
    rw [ha]
    exact (canonical12066 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA718 + difference 0 5) (sourceB718 + difference 5 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3390) := by
    have ha : (tripleCharges (sourceA718 + difference 0 5) (sourceB718 + difference 5 0) sourceC718) = raw12067 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw12067; decide +kernel
    rw [ha]
    exact (canonical12067 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA718 + sourceB718) sourceC718) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA718 + sourceB718) sourceC718) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA718 sourceB718 sourceC718 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA718 sourceB718 sourceC718
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm718, Integer.Sparse.eval]
  linarith only [hs]

def sourceA719 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB719 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC719 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm719 : Integer.Sparse Master := [(Sum.inr 3150, 1), (Sum.inr 3373, 1), (Sum.inr 3378, 3), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

theorem sourceEq719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm719 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA719 + difference 0 1) (sourceB719 + difference 1 0) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA719 + difference 0 1) (sourceB719 + difference 1 0) sourceC719) = raw12064 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw12064; decide +kernel
    rw [ha]
    exact (canonical12064 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA719 + difference 1 1) (sourceB719 + difference 1 1) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA719 + difference 1 1) (sourceB719 + difference 1 1) sourceC719) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA719 + difference 2 1) (sourceB719 + difference 1 2) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3150) := by
    have ha : (tripleCharges (sourceA719 + difference 2 1) (sourceB719 + difference 1 2) sourceC719) = raw12068 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw12068; decide +kernel
    rw [ha]
    exact (canonical12068 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA719 + difference 3 1) (sourceB719 + difference 1 3) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA719 + difference 3 1) (sourceB719 + difference 1 3) sourceC719) = raw12069 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw12069; decide +kernel
    rw [ha]
    exact (canonical12069 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA719 + difference 4 1) (sourceB719 + difference 1 4) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA719 + difference 4 1) (sourceB719 + difference 1 4) sourceC719) = raw12070 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw12070; decide +kernel
    rw [ha]
    exact (canonical12070 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA719 + difference 5 1) (sourceB719 + difference 1 5) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3373) := by
    have ha : (tripleCharges (sourceA719 + difference 5 1) (sourceB719 + difference 1 5) sourceC719) = raw11757 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw11757; decide +kernel
    rw [ha]
    exact (canonical11757 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA719 + sourceB719) sourceC719) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA719 + sourceB719) sourceC719) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA719 sourceB719 sourceC719 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA719 sourceB719 sourceC719
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm719, Integer.Sparse.eval]
  linarith only [hs]

def sourceA720 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB720 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC720 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm720 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 3149, 2), (Sum.inr 3150, 1), (Sum.inr 3155, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

theorem sourceEq720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm720 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA720 + difference 2 0) (sourceB720 + difference 0 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA720 + difference 2 0) (sourceB720 + difference 0 2) sourceC720) = raw12071 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12071; decide +kernel
    rw [ha]
    exact (canonical12071 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA720 + difference 2 1) (sourceB720 + difference 1 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3150) := by
    have ha : (tripleCharges (sourceA720 + difference 2 1) (sourceB720 + difference 1 2) sourceC720) = raw12068 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12068; decide +kernel
    rw [ha]
    exact (canonical12068 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA720 + difference 2 2) (sourceB720 + difference 2 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA720 + difference 2 2) (sourceB720 + difference 2 2) sourceC720) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA720 + difference 2 3) (sourceB720 + difference 3 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3149) := by
    have ha : (tripleCharges (sourceA720 + difference 2 3) (sourceB720 + difference 3 2) sourceC720) = raw12072 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12072; decide +kernel
    rw [ha]
    exact (canonical12072 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA720 + difference 2 4) (sourceB720 + difference 4 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3149) := by
    have ha : (tripleCharges (sourceA720 + difference 2 4) (sourceB720 + difference 4 2) sourceC720) = raw12073 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12073; decide +kernel
    rw [ha]
    exact (canonical12073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA720 + difference 2 5) (sourceB720 + difference 5 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA720 + difference 2 5) (sourceB720 + difference 5 2) sourceC720) = raw12074 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12074; decide +kernel
    rw [ha]
    exact (canonical12074 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA720 + sourceB720) sourceC720) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA720 + sourceB720) sourceC720) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA720 sourceB720 sourceC720 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA720 sourceB720 sourceC720
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm720, Integer.Sparse.eval]
  linarith only [hs]

def sourceA721 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB721 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC721 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm721 : Integer.Sparse Master := [(Sum.inr 2023, 1), (Sum.inr 3378, 1), (Sum.inr 3505, 1), (Sum.inr 3526, 2), (Sum.inr 3532, 1), (Sum.inr 4083, -1)]

theorem sourceEq721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm721 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA721 + difference 3 0) (sourceB721 + difference 0 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA721 + difference 3 0) (sourceB721 + difference 0 3) sourceC721) = raw12075 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw12075; decide +kernel
    rw [ha]
    exact (canonical12075 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA721 + difference 3 1) (sourceB721 + difference 1 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA721 + difference 3 1) (sourceB721 + difference 1 3) sourceC721) = raw12069 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw12069; decide +kernel
    rw [ha]
    exact (canonical12069 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA721 + difference 3 2) (sourceB721 + difference 2 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA721 + difference 3 2) (sourceB721 + difference 2 3) sourceC721) = raw11768 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw11768; decide +kernel
    rw [ha]
    exact (canonical11768 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA721 + difference 3 3) (sourceB721 + difference 3 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA721 + difference 3 3) (sourceB721 + difference 3 3) sourceC721) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA721 + difference 3 4) (sourceB721 + difference 4 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA721 + difference 3 4) (sourceB721 + difference 4 3) sourceC721) = raw12076 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw12076; decide +kernel
    rw [ha]
    exact (canonical12076 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA721 + difference 3 5) (sourceB721 + difference 5 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA721 + difference 3 5) (sourceB721 + difference 5 3) sourceC721) = raw12077 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw12077; decide +kernel
    rw [ha]
    exact (canonical12077 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA721 + sourceB721) sourceC721) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA721 + sourceB721) sourceC721) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA721 sourceB721 sourceC721 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA721 sourceB721 sourceC721
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm721, Integer.Sparse.eval]
  linarith only [hs]

def sourceA722 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB722 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC722 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm722 : Integer.Sparse Master := [(Sum.inr 3149, 1), (Sum.inr 3376, 1), (Sum.inr 3500, 1), (Sum.inr 3505, 1), (Sum.inr 3526, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem sourceEq722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm722 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA722 + difference 0 3) (sourceB722 + difference 3 0) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA722 + difference 0 3) (sourceB722 + difference 3 0) sourceC722) = raw12065 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw12065; decide +kernel
    rw [ha]
    exact (canonical12065 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA722 + difference 1 3) (sourceB722 + difference 3 1) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA722 + difference 1 3) (sourceB722 + difference 3 1) sourceC722) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA722 + difference 2 3) (sourceB722 + difference 3 2) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3149) := by
    have ha : (tripleCharges (sourceA722 + difference 2 3) (sourceB722 + difference 3 2) sourceC722) = raw12072 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw12072; decide +kernel
    rw [ha]
    exact (canonical12072 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA722 + difference 3 3) (sourceB722 + difference 3 3) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA722 + difference 3 3) (sourceB722 + difference 3 3) sourceC722) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA722 + difference 4 3) (sourceB722 + difference 3 4) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA722 + difference 4 3) (sourceB722 + difference 3 4) sourceC722) = raw12079 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw12079; decide +kernel
    rw [ha]
    exact (canonical12079 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA722 + difference 5 3) (sourceB722 + difference 3 5) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA722 + difference 5 3) (sourceB722 + difference 3 5) sourceC722) = raw11762 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw11762; decide +kernel
    rw [ha]
    exact (canonical11762 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA722 + sourceB722) sourceC722) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA722 + sourceB722) sourceC722) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA722 sourceB722 sourceC722 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA722 sourceB722 sourceC722
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm722, Integer.Sparse.eval]
  linarith only [hs]

def sourceA723 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB723 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC723 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm723 : Integer.Sparse Master := [(Sum.inr 4618, 2), (Sum.inr 4619, 2), (Sum.inr 4623, 1), (Sum.inr 5166, 2), (Sum.inr 5168, 2), (Sum.inr 5170, 4), (Sum.inr 5301, 2), (Sum.inr 5302, 2), (Sum.inr 5306, 4), (Sum.inr 5308, 2), (Sum.inr 5310, 2), (Sum.inr 5439, 2), (Sum.inr 5453, 1), (Sum.inr 5455, 2)]

theorem sourceEq723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm723 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA723 + difference 0 1) (sourceB723 + difference 1 0) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA723 + difference 0 1) (sourceB723 + difference 1 0) sourceC723) = raw12080 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12080; decide +kernel
    rw [ha]
    exact (canonical12080 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA723 + difference 0 2) (sourceB723 + difference 2 0) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA723 + difference 0 2) (sourceB723 + difference 2 0) sourceC723) = raw12081 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12081; decide +kernel
    rw [ha]
    exact (canonical12081 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA723 + difference 0 3) (sourceB723 + difference 3 0) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA723 + difference 0 3) (sourceB723 + difference 3 0) sourceC723) = raw10219 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw10219; decide +kernel
    rw [ha]
    exact (canonical10219 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA723 + difference 0 4) (sourceB723 + difference 4 0) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA723 + difference 0 4) (sourceB723 + difference 4 0) sourceC723) = raw12082 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12082; decide +kernel
    rw [ha]
    exact (canonical12082 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA723 + difference 0 5) (sourceB723 + difference 5 0) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA723 + difference 0 5) (sourceB723 + difference 5 0) sourceC723) = raw12083 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12083; decide +kernel
    rw [ha]
    exact (canonical12083 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA723 + difference 1 0) (sourceB723 + difference 0 1) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA723 + difference 1 0) (sourceB723 + difference 0 1) sourceC723) = raw12084 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12084; decide +kernel
    rw [ha]
    exact (canonical12084 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA723 + difference 1 2) (sourceB723 + difference 2 1) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA723 + difference 1 2) (sourceB723 + difference 2 1) sourceC723) = raw12085 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12085; decide +kernel
    rw [ha]
    exact (canonical12085 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA723 + difference 1 3) (sourceB723 + difference 3 1) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA723 + difference 1 3) (sourceB723 + difference 3 1) sourceC723) = raw10223 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw10223; decide +kernel
    rw [ha]
    exact (canonical10223 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA723 + difference 1 4) (sourceB723 + difference 4 1) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA723 + difference 1 4) (sourceB723 + difference 4 1) sourceC723) = raw12086 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12086; decide +kernel
    rw [ha]
    exact (canonical12086 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA723 + difference 1 5) (sourceB723 + difference 5 1) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA723 + difference 1 5) (sourceB723 + difference 5 1) sourceC723) = raw12087 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12087; decide +kernel
    rw [ha]
    exact (canonical12087 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA723 + difference 2 0) (sourceB723 + difference 0 2) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA723 + difference 2 0) (sourceB723 + difference 0 2) sourceC723) = raw12088 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12088; decide +kernel
    rw [ha]
    exact (canonical12088 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA723 + difference 2 1) (sourceB723 + difference 1 2) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA723 + difference 2 1) (sourceB723 + difference 1 2) sourceC723) = raw12089 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12089; decide +kernel
    rw [ha]
    exact (canonical12089 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA723 + difference 2 3) (sourceB723 + difference 3 2) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA723 + difference 2 3) (sourceB723 + difference 3 2) sourceC723) = raw10227 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw10227; decide +kernel
    rw [ha]
    exact (canonical10227 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA723 + difference 2 4) (sourceB723 + difference 4 2) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA723 + difference 2 4) (sourceB723 + difference 4 2) sourceC723) = raw12090 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12090; decide +kernel
    rw [ha]
    exact (canonical12090 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA723 + difference 2 5) (sourceB723 + difference 5 2) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA723 + difference 2 5) (sourceB723 + difference 5 2) sourceC723) = raw12091 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12091; decide +kernel
    rw [ha]
    exact (canonical12091 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA723 + difference 3 0) (sourceB723 + difference 0 3) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA723 + difference 3 0) (sourceB723 + difference 0 3) sourceC723) = raw12092 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12092; decide +kernel
    rw [ha]
    exact (canonical12092 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA723 + difference 3 1) (sourceB723 + difference 1 3) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA723 + difference 3 1) (sourceB723 + difference 1 3) sourceC723) = raw12093 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12093; decide +kernel
    rw [ha]
    exact (canonical12093 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA723 + difference 3 2) (sourceB723 + difference 2 3) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA723 + difference 3 2) (sourceB723 + difference 2 3) sourceC723) = raw12094 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12094; decide +kernel
    rw [ha]
    exact (canonical12094 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA723 + difference 3 4) (sourceB723 + difference 4 3) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA723 + difference 3 4) (sourceB723 + difference 4 3) sourceC723) = raw12095 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12095; decide +kernel
    rw [ha]
    exact (canonical12095 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA723 + difference 3 5) (sourceB723 + difference 5 3) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA723 + difference 3 5) (sourceB723 + difference 5 3) sourceC723) = raw12096 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12096; decide +kernel
    rw [ha]
    exact (canonical12096 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA723 + difference 4 0) (sourceB723 + difference 0 4) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA723 + difference 4 0) (sourceB723 + difference 0 4) sourceC723) = raw12097 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12097; decide +kernel
    rw [ha]
    exact (canonical12097 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA723 + difference 4 1) (sourceB723 + difference 1 4) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA723 + difference 4 1) (sourceB723 + difference 1 4) sourceC723) = raw12098 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12098; decide +kernel
    rw [ha]
    exact (canonical12098 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA723 + difference 4 2) (sourceB723 + difference 2 4) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA723 + difference 4 2) (sourceB723 + difference 2 4) sourceC723) = raw12099 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12099; decide +kernel
    rw [ha]
    exact (canonical12099 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA723 + difference 4 3) (sourceB723 + difference 3 4) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA723 + difference 4 3) (sourceB723 + difference 3 4) sourceC723) = raw10236 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw10236; decide +kernel
    rw [ha]
    exact (canonical10236 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA723 + difference 4 5) (sourceB723 + difference 5 4) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA723 + difference 4 5) (sourceB723 + difference 5 4) sourceC723) = raw12100 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw12100; decide +kernel
    rw [ha]
    exact (canonical12100 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA723 + difference 5 0) (sourceB723 + difference 0 5) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA723 + difference 5 0) (sourceB723 + difference 0 5) sourceC723) = raw10228 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw10228; decide +kernel
    rw [ha]
    exact (canonical10228 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA723 + difference 5 1) (sourceB723 + difference 1 5) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA723 + difference 5 1) (sourceB723 + difference 1 5) sourceC723) = raw10229 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw10229; decide +kernel
    rw [ha]
    exact (canonical10229 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA723 + difference 5 2) (sourceB723 + difference 2 5) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA723 + difference 5 2) (sourceB723 + difference 2 5) sourceC723) = raw10230 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw10230; decide +kernel
    rw [ha]
    exact (canonical10230 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA723 + difference 5 3) (sourceB723 + difference 3 5) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA723 + difference 5 3) (sourceB723 + difference 3 5) sourceC723) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA723 + difference 5 4) (sourceB723 + difference 4 5) sourceC723) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA723 + difference 5 4) (sourceB723 + difference 4 5) sourceC723) = raw5077 := by
      apply Matrix.ext; unfold tripleCharges sourceA723 sourceB723 sourceC723 difference raw5077; decide +kernel
    rw [ha]
    exact (canonical5077 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA723 sourceB723 sourceC723
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm723, Integer.Sparse.eval]
  linarith only [hs]

def sourceA724 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB724 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC724 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm724 : Integer.Sparse Master := [(Sum.inr 1293, 2), (Sum.inr 1294, 2), (Sum.inr 1305, 1), (Sum.inr 2953, 2), (Sum.inr 2954, 4), (Sum.inr 2963, 2), (Sum.inr 3053, 2), (Sum.inr 3054, 2), (Sum.inr 3120, 4), (Sum.inr 3121, 2), (Sum.inr 3124, 2), (Sum.inr 3912, 1), (Sum.inr 4012, 2), (Sum.inr 4019, 2)]

theorem sourceEq724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm724 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA724 + difference 0 1) (sourceB724 + difference 1 0) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA724 + difference 0 1) (sourceB724 + difference 1 0) sourceC724) = raw12101 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12101; decide +kernel
    rw [ha]
    exact (canonical12101 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA724 + difference 0 2) (sourceB724 + difference 2 0) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA724 + difference 0 2) (sourceB724 + difference 2 0) sourceC724) = raw12102 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12102; decide +kernel
    rw [ha]
    exact (canonical12102 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA724 + difference 0 3) (sourceB724 + difference 3 0) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA724 + difference 0 3) (sourceB724 + difference 3 0) sourceC724) = raw12103 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12103; decide +kernel
    rw [ha]
    exact (canonical12103 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA724 + difference 0 4) (sourceB724 + difference 4 0) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA724 + difference 0 4) (sourceB724 + difference 4 0) sourceC724) = raw12104 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12104; decide +kernel
    rw [ha]
    exact (canonical12104 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA724 + difference 0 5) (sourceB724 + difference 5 0) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA724 + difference 0 5) (sourceB724 + difference 5 0) sourceC724) = raw12105 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12105; decide +kernel
    rw [ha]
    exact (canonical12105 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA724 + difference 1 0) (sourceB724 + difference 0 1) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA724 + difference 1 0) (sourceB724 + difference 0 1) sourceC724) = raw12106 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12106; decide +kernel
    rw [ha]
    exact (canonical12106 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA724 + difference 1 2) (sourceB724 + difference 2 1) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2953) := by
    have ha : (tripleCharges (sourceA724 + difference 1 2) (sourceB724 + difference 2 1) sourceC724) = raw12107 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12107; decide +kernel
    rw [ha]
    exact (canonical12107 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA724 + difference 1 3) (sourceB724 + difference 3 1) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA724 + difference 1 3) (sourceB724 + difference 3 1) sourceC724) = raw12108 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12108; decide +kernel
    rw [ha]
    exact (canonical12108 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA724 + difference 1 4) (sourceB724 + difference 4 1) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA724 + difference 1 4) (sourceB724 + difference 4 1) sourceC724) = raw12109 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12109; decide +kernel
    rw [ha]
    exact (canonical12109 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA724 + difference 1 5) (sourceB724 + difference 5 1) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA724 + difference 1 5) (sourceB724 + difference 5 1) sourceC724) = raw12110 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12110; decide +kernel
    rw [ha]
    exact (canonical12110 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA724 + difference 2 0) (sourceB724 + difference 0 2) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA724 + difference 2 0) (sourceB724 + difference 0 2) sourceC724) = raw12111 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12111; decide +kernel
    rw [ha]
    exact (canonical12111 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA724 + difference 2 1) (sourceB724 + difference 1 2) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2953) := by
    have ha : (tripleCharges (sourceA724 + difference 2 1) (sourceB724 + difference 1 2) sourceC724) = raw12112 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12112; decide +kernel
    rw [ha]
    exact (canonical12112 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA724 + difference 2 3) (sourceB724 + difference 3 2) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA724 + difference 2 3) (sourceB724 + difference 3 2) sourceC724) = raw12113 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12113; decide +kernel
    rw [ha]
    exact (canonical12113 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA724 + difference 2 4) (sourceB724 + difference 4 2) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA724 + difference 2 4) (sourceB724 + difference 4 2) sourceC724) = raw12114 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12114; decide +kernel
    rw [ha]
    exact (canonical12114 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA724 + difference 2 5) (sourceB724 + difference 5 2) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA724 + difference 2 5) (sourceB724 + difference 5 2) sourceC724) = raw12115 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12115; decide +kernel
    rw [ha]
    exact (canonical12115 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA724 + difference 3 0) (sourceB724 + difference 0 3) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA724 + difference 3 0) (sourceB724 + difference 0 3) sourceC724) = raw12116 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12116; decide +kernel
    rw [ha]
    exact (canonical12116 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA724 + difference 3 1) (sourceB724 + difference 1 3) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA724 + difference 3 1) (sourceB724 + difference 1 3) sourceC724) = raw12117 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12117; decide +kernel
    rw [ha]
    exact (canonical12117 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA724 + difference 3 2) (sourceB724 + difference 2 3) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA724 + difference 3 2) (sourceB724 + difference 2 3) sourceC724) = raw12118 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12118; decide +kernel
    rw [ha]
    exact (canonical12118 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA724 + difference 3 4) (sourceB724 + difference 4 3) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA724 + difference 3 4) (sourceB724 + difference 4 3) sourceC724) = raw12119 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12119; decide +kernel
    rw [ha]
    exact (canonical12119 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA724 + difference 3 5) (sourceB724 + difference 5 3) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA724 + difference 3 5) (sourceB724 + difference 5 3) sourceC724) = raw12120 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12120; decide +kernel
    rw [ha]
    exact (canonical12120 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA724 + difference 4 0) (sourceB724 + difference 0 4) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA724 + difference 4 0) (sourceB724 + difference 0 4) sourceC724) = raw12121 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12121; decide +kernel
    rw [ha]
    exact (canonical12121 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA724 + difference 4 1) (sourceB724 + difference 1 4) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA724 + difference 4 1) (sourceB724 + difference 1 4) sourceC724) = raw12122 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12122; decide +kernel
    rw [ha]
    exact (canonical12122 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA724 + difference 4 2) (sourceB724 + difference 2 4) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA724 + difference 4 2) (sourceB724 + difference 2 4) sourceC724) = raw12123 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12123; decide +kernel
    rw [ha]
    exact (canonical12123 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA724 + difference 4 3) (sourceB724 + difference 3 4) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA724 + difference 4 3) (sourceB724 + difference 3 4) sourceC724) = raw12124 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12124; decide +kernel
    rw [ha]
    exact (canonical12124 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA724 + difference 4 5) (sourceB724 + difference 5 4) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA724 + difference 4 5) (sourceB724 + difference 5 4) sourceC724) = raw12125 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12125; decide +kernel
    rw [ha]
    exact (canonical12125 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA724 + difference 5 0) (sourceB724 + difference 0 5) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA724 + difference 5 0) (sourceB724 + difference 0 5) sourceC724) = raw12126 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12126; decide +kernel
    rw [ha]
    exact (canonical12126 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA724 + difference 5 1) (sourceB724 + difference 1 5) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA724 + difference 5 1) (sourceB724 + difference 1 5) sourceC724) = raw12127 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12127; decide +kernel
    rw [ha]
    exact (canonical12127 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA724 + difference 5 2) (sourceB724 + difference 2 5) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA724 + difference 5 2) (sourceB724 + difference 2 5) sourceC724) = raw12128 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12128; decide +kernel
    rw [ha]
    exact (canonical12128 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA724 + difference 5 3) (sourceB724 + difference 3 5) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA724 + difference 5 3) (sourceB724 + difference 3 5) sourceC724) = raw12129 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12129; decide +kernel
    rw [ha]
    exact (canonical12129 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA724 + difference 5 4) (sourceB724 + difference 4 5) sourceC724) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA724 + difference 5 4) (sourceB724 + difference 4 5) sourceC724) = raw12130 := by
      apply Matrix.ext; unfold tripleCharges sourceA724 sourceB724 sourceC724 difference raw12130; decide +kernel
    rw [ha]
    exact (canonical12130 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA724 sourceB724 sourceC724
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm724, Integer.Sparse.eval]
  linarith only [hs]

def sourceA725 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB725 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC725 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceForm725 : Integer.Sparse Master := [(Sum.inr 4495, 2), (Sum.inr 4496, 1), (Sum.inr 4499, 2), (Sum.inr 5098, 2), (Sum.inr 5099, 2), (Sum.inr 5102, 4), (Sum.inr 5271, 4), (Sum.inr 5272, 2), (Sum.inr 5275, 2), (Sum.inr 5292, 2), (Sum.inr 5293, 2), (Sum.inr 5485, 2), (Sum.inr 5492, 2), (Sum.inr 5493, 1)]

theorem sourceEq725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm725 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA725 + difference 0 1) (sourceB725 + difference 1 0) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA725 + difference 0 1) (sourceB725 + difference 1 0) sourceC725) = raw12131 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12131; decide +kernel
    rw [ha]
    exact (canonical12131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA725 + difference 0 2) (sourceB725 + difference 2 0) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA725 + difference 0 2) (sourceB725 + difference 2 0) sourceC725) = raw12132 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12132; decide +kernel
    rw [ha]
    exact (canonical12132 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA725 + difference 0 3) (sourceB725 + difference 3 0) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA725 + difference 0 3) (sourceB725 + difference 3 0) sourceC725) = raw10676 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw10676; decide +kernel
    rw [ha]
    exact (canonical10676 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA725 + difference 0 4) (sourceB725 + difference 4 0) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA725 + difference 0 4) (sourceB725 + difference 4 0) sourceC725) = raw12133 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12133; decide +kernel
    rw [ha]
    exact (canonical12133 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA725 + difference 0 5) (sourceB725 + difference 5 0) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA725 + difference 0 5) (sourceB725 + difference 5 0) sourceC725) = raw12134 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12134; decide +kernel
    rw [ha]
    exact (canonical12134 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA725 + difference 1 0) (sourceB725 + difference 0 1) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA725 + difference 1 0) (sourceB725 + difference 0 1) sourceC725) = raw12135 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12135; decide +kernel
    rw [ha]
    exact (canonical12135 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA725 + difference 1 2) (sourceB725 + difference 2 1) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA725 + difference 1 2) (sourceB725 + difference 2 1) sourceC725) = raw12136 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12136; decide +kernel
    rw [ha]
    exact (canonical12136 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA725 + difference 1 3) (sourceB725 + difference 3 1) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA725 + difference 1 3) (sourceB725 + difference 3 1) sourceC725) = raw10681 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw10681; decide +kernel
    rw [ha]
    exact (canonical10681 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA725 + difference 1 4) (sourceB725 + difference 4 1) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA725 + difference 1 4) (sourceB725 + difference 4 1) sourceC725) = raw12137 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12137; decide +kernel
    rw [ha]
    exact (canonical12137 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA725 + difference 1 5) (sourceB725 + difference 5 1) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA725 + difference 1 5) (sourceB725 + difference 5 1) sourceC725) = raw12138 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12138; decide +kernel
    rw [ha]
    exact (canonical12138 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA725 + difference 2 0) (sourceB725 + difference 0 2) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA725 + difference 2 0) (sourceB725 + difference 0 2) sourceC725) = raw12139 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12139; decide +kernel
    rw [ha]
    exact (canonical12139 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA725 + difference 2 1) (sourceB725 + difference 1 2) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA725 + difference 2 1) (sourceB725 + difference 1 2) sourceC725) = raw12140 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12140; decide +kernel
    rw [ha]
    exact (canonical12140 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA725 + difference 2 3) (sourceB725 + difference 3 2) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA725 + difference 2 3) (sourceB725 + difference 3 2) sourceC725) = raw10686 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw10686; decide +kernel
    rw [ha]
    exact (canonical10686 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA725 + difference 2 4) (sourceB725 + difference 4 2) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA725 + difference 2 4) (sourceB725 + difference 4 2) sourceC725) = raw12141 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12141; decide +kernel
    rw [ha]
    exact (canonical12141 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA725 + difference 2 5) (sourceB725 + difference 5 2) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA725 + difference 2 5) (sourceB725 + difference 5 2) sourceC725) = raw12142 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12142; decide +kernel
    rw [ha]
    exact (canonical12142 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA725 + difference 3 0) (sourceB725 + difference 0 3) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA725 + difference 3 0) (sourceB725 + difference 0 3) sourceC725) = raw12143 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12143; decide +kernel
    rw [ha]
    exact (canonical12143 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA725 + difference 3 1) (sourceB725 + difference 1 3) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA725 + difference 3 1) (sourceB725 + difference 1 3) sourceC725) = raw12144 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12144; decide +kernel
    rw [ha]
    exact (canonical12144 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA725 + difference 3 2) (sourceB725 + difference 2 3) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA725 + difference 3 2) (sourceB725 + difference 2 3) sourceC725) = raw12145 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12145; decide +kernel
    rw [ha]
    exact (canonical12145 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA725 + difference 3 4) (sourceB725 + difference 4 3) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA725 + difference 3 4) (sourceB725 + difference 4 3) sourceC725) = raw12146 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12146; decide +kernel
    rw [ha]
    exact (canonical12146 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA725 + difference 3 5) (sourceB725 + difference 5 3) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA725 + difference 3 5) (sourceB725 + difference 5 3) sourceC725) = raw12147 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12147; decide +kernel
    rw [ha]
    exact (canonical12147 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA725 + difference 4 0) (sourceB725 + difference 0 4) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA725 + difference 4 0) (sourceB725 + difference 0 4) sourceC725) = raw12148 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12148; decide +kernel
    rw [ha]
    exact (canonical12148 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA725 + difference 4 1) (sourceB725 + difference 1 4) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA725 + difference 4 1) (sourceB725 + difference 1 4) sourceC725) = raw12149 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12149; decide +kernel
    rw [ha]
    exact (canonical12149 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA725 + difference 4 2) (sourceB725 + difference 2 4) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA725 + difference 4 2) (sourceB725 + difference 2 4) sourceC725) = raw12150 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12150; decide +kernel
    rw [ha]
    exact (canonical12150 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA725 + difference 4 3) (sourceB725 + difference 3 4) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA725 + difference 4 3) (sourceB725 + difference 3 4) sourceC725) = raw10696 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw10696; decide +kernel
    rw [ha]
    exact (canonical10696 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA725 + difference 4 5) (sourceB725 + difference 5 4) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA725 + difference 4 5) (sourceB725 + difference 5 4) sourceC725) = raw12151 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12151; decide +kernel
    rw [ha]
    exact (canonical12151 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA725 + difference 5 0) (sourceB725 + difference 0 5) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA725 + difference 5 0) (sourceB725 + difference 0 5) sourceC725) = raw10687 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw10687; decide +kernel
    rw [ha]
    exact (canonical10687 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA725 + difference 5 1) (sourceB725 + difference 1 5) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA725 + difference 5 1) (sourceB725 + difference 1 5) sourceC725) = raw10688 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw10688; decide +kernel
    rw [ha]
    exact (canonical10688 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA725 + difference 5 2) (sourceB725 + difference 2 5) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA725 + difference 5 2) (sourceB725 + difference 2 5) sourceC725) = raw10689 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw10689; decide +kernel
    rw [ha]
    exact (canonical10689 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA725 + difference 5 3) (sourceB725 + difference 3 5) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA725 + difference 5 3) (sourceB725 + difference 3 5) sourceC725) = raw12152 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw12152; decide +kernel
    rw [ha]
    exact (canonical12152 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA725 + difference 5 4) (sourceB725 + difference 4 5) sourceC725) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA725 + difference 5 4) (sourceB725 + difference 4 5) sourceC725) = raw10690 := by
      apply Matrix.ext; unfold tripleCharges sourceA725 sourceB725 sourceC725 difference raw10690; decide +kernel
    rw [ha]
    exact (canonical10690 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA725 sourceB725 sourceC725
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm725, Integer.Sparse.eval]
  linarith only [hs]

def sourceA726 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB726 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC726 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceForm726 : Integer.Sparse Master := [(Sum.inr 1079, 2), (Sum.inr 1080, 1), (Sum.inr 1083, 2), (Sum.inr 2508, 2), (Sum.inr 2509, 2), (Sum.inr 2512, 4), (Sum.inr 2739, 4), (Sum.inr 2740, 2), (Sum.inr 2743, 2), (Sum.inr 2766, 2), (Sum.inr 2767, 2), (Sum.inr 3984, 2), (Sum.inr 4015, 2), (Sum.inr 4018, 1)]

theorem sourceEq726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm726 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA726 + difference 0 1) (sourceB726 + difference 1 0) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA726 + difference 0 1) (sourceB726 + difference 1 0) sourceC726) = raw12153 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12153; decide +kernel
    rw [ha]
    exact (canonical12153 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA726 + difference 0 2) (sourceB726 + difference 2 0) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA726 + difference 0 2) (sourceB726 + difference 2 0) sourceC726) = raw12154 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12154; decide +kernel
    rw [ha]
    exact (canonical12154 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA726 + difference 0 3) (sourceB726 + difference 3 0) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA726 + difference 0 3) (sourceB726 + difference 3 0) sourceC726) = raw12155 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12155; decide +kernel
    rw [ha]
    exact (canonical12155 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA726 + difference 0 4) (sourceB726 + difference 4 0) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA726 + difference 0 4) (sourceB726 + difference 4 0) sourceC726) = raw12156 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12156; decide +kernel
    rw [ha]
    exact (canonical12156 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA726 + difference 0 5) (sourceB726 + difference 5 0) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4018) := by
    have ha : (tripleCharges (sourceA726 + difference 0 5) (sourceB726 + difference 5 0) sourceC726) = raw12157 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12157; decide +kernel
    rw [ha]
    exact (canonical12157 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA726 + difference 1 0) (sourceB726 + difference 0 1) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA726 + difference 1 0) (sourceB726 + difference 0 1) sourceC726) = raw12158 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12158; decide +kernel
    rw [ha]
    exact (canonical12158 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA726 + difference 1 2) (sourceB726 + difference 2 1) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA726 + difference 1 2) (sourceB726 + difference 2 1) sourceC726) = raw12159 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12159; decide +kernel
    rw [ha]
    exact (canonical12159 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA726 + difference 1 3) (sourceB726 + difference 3 1) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA726 + difference 1 3) (sourceB726 + difference 3 1) sourceC726) = raw12160 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12160; decide +kernel
    rw [ha]
    exact (canonical12160 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA726 + difference 1 4) (sourceB726 + difference 4 1) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA726 + difference 1 4) (sourceB726 + difference 4 1) sourceC726) = raw12161 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12161; decide +kernel
    rw [ha]
    exact (canonical12161 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA726 + difference 1 5) (sourceB726 + difference 5 1) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA726 + difference 1 5) (sourceB726 + difference 5 1) sourceC726) = raw12162 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12162; decide +kernel
    rw [ha]
    exact (canonical12162 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA726 + difference 2 0) (sourceB726 + difference 0 2) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA726 + difference 2 0) (sourceB726 + difference 0 2) sourceC726) = raw12163 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12163; decide +kernel
    rw [ha]
    exact (canonical12163 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA726 + difference 2 1) (sourceB726 + difference 1 2) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA726 + difference 2 1) (sourceB726 + difference 1 2) sourceC726) = raw12164 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12164; decide +kernel
    rw [ha]
    exact (canonical12164 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA726 + difference 2 3) (sourceB726 + difference 3 2) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA726 + difference 2 3) (sourceB726 + difference 3 2) sourceC726) = raw12165 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12165; decide +kernel
    rw [ha]
    exact (canonical12165 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA726 + difference 2 4) (sourceB726 + difference 4 2) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA726 + difference 2 4) (sourceB726 + difference 4 2) sourceC726) = raw12166 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12166; decide +kernel
    rw [ha]
    exact (canonical12166 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA726 + difference 2 5) (sourceB726 + difference 5 2) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA726 + difference 2 5) (sourceB726 + difference 5 2) sourceC726) = raw12167 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12167; decide +kernel
    rw [ha]
    exact (canonical12167 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA726 + difference 3 0) (sourceB726 + difference 0 3) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA726 + difference 3 0) (sourceB726 + difference 0 3) sourceC726) = raw12168 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12168; decide +kernel
    rw [ha]
    exact (canonical12168 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA726 + difference 3 1) (sourceB726 + difference 1 3) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA726 + difference 3 1) (sourceB726 + difference 1 3) sourceC726) = raw12169 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12169; decide +kernel
    rw [ha]
    exact (canonical12169 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA726 + difference 3 2) (sourceB726 + difference 2 3) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA726 + difference 3 2) (sourceB726 + difference 2 3) sourceC726) = raw12170 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12170; decide +kernel
    rw [ha]
    exact (canonical12170 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA726 + difference 3 4) (sourceB726 + difference 4 3) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA726 + difference 3 4) (sourceB726 + difference 4 3) sourceC726) = raw12171 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12171; decide +kernel
    rw [ha]
    exact (canonical12171 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA726 + difference 3 5) (sourceB726 + difference 5 3) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA726 + difference 3 5) (sourceB726 + difference 5 3) sourceC726) = raw12172 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12172; decide +kernel
    rw [ha]
    exact (canonical12172 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA726 + difference 4 0) (sourceB726 + difference 0 4) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA726 + difference 4 0) (sourceB726 + difference 0 4) sourceC726) = raw12173 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12173; decide +kernel
    rw [ha]
    exact (canonical12173 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA726 + difference 4 1) (sourceB726 + difference 1 4) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA726 + difference 4 1) (sourceB726 + difference 1 4) sourceC726) = raw12174 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12174; decide +kernel
    rw [ha]
    exact (canonical12174 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA726 + difference 4 2) (sourceB726 + difference 2 4) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA726 + difference 4 2) (sourceB726 + difference 2 4) sourceC726) = raw12175 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12175; decide +kernel
    rw [ha]
    exact (canonical12175 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA726 + difference 4 3) (sourceB726 + difference 3 4) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA726 + difference 4 3) (sourceB726 + difference 3 4) sourceC726) = raw12176 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12176; decide +kernel
    rw [ha]
    exact (canonical12176 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA726 + difference 4 5) (sourceB726 + difference 5 4) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA726 + difference 4 5) (sourceB726 + difference 5 4) sourceC726) = raw12177 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12177; decide +kernel
    rw [ha]
    exact (canonical12177 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA726 + difference 5 0) (sourceB726 + difference 0 5) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA726 + difference 5 0) (sourceB726 + difference 0 5) sourceC726) = raw12178 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12178; decide +kernel
    rw [ha]
    exact (canonical12178 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA726 + difference 5 1) (sourceB726 + difference 1 5) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA726 + difference 5 1) (sourceB726 + difference 1 5) sourceC726) = raw12179 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12179; decide +kernel
    rw [ha]
    exact (canonical12179 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA726 + difference 5 2) (sourceB726 + difference 2 5) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA726 + difference 5 2) (sourceB726 + difference 2 5) sourceC726) = raw12180 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12180; decide +kernel
    rw [ha]
    exact (canonical12180 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA726 + difference 5 3) (sourceB726 + difference 3 5) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA726 + difference 5 3) (sourceB726 + difference 3 5) sourceC726) = raw12181 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12181; decide +kernel
    rw [ha]
    exact (canonical12181 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA726 + difference 5 4) (sourceB726 + difference 4 5) sourceC726) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA726 + difference 5 4) (sourceB726 + difference 4 5) sourceC726) = raw12182 := by
      apply Matrix.ext; unfold tripleCharges sourceA726 sourceB726 sourceC726 difference raw12182; decide +kernel
    rw [ha]
    exact (canonical12182 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA726 sourceB726 sourceC726
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm726, Integer.Sparse.eval]
  linarith only [hs]

def sourceA727 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB727 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC727 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm727 : Integer.Sparse Master := [(Sum.inr 4888, 2), (Sum.inr 4890, 1), (Sum.inr 4895, 2), (Sum.inr 5256, 2), (Sum.inr 5270, 2), (Sum.inr 5271, 4), (Sum.inr 5289, 4), (Sum.inr 5290, 2), (Sum.inr 5292, 2), (Sum.inr 5295, 2), (Sum.inr 5304, 4), (Sum.inr 5307, 3)]

theorem sourceEq727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm727 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA727 + difference 0 1) (sourceB727 + difference 1 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA727 + difference 0 1) (sourceB727 + difference 1 0) sourceC727) = raw11661 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11661; decide +kernel
    rw [ha]
    exact (canonical11661 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA727 + difference 0 2) (sourceB727 + difference 2 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA727 + difference 0 2) (sourceB727 + difference 2 0) sourceC727) = raw12183 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12183; decide +kernel
    rw [ha]
    exact (canonical12183 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA727 + difference 0 3) (sourceB727 + difference 3 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA727 + difference 0 3) (sourceB727 + difference 3 0) sourceC727) = raw12184 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12184; decide +kernel
    rw [ha]
    exact (canonical12184 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA727 + difference 0 4) (sourceB727 + difference 4 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA727 + difference 0 4) (sourceB727 + difference 4 0) sourceC727) = raw12185 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12185; decide +kernel
    rw [ha]
    exact (canonical12185 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA727 + difference 0 5) (sourceB727 + difference 5 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA727 + difference 0 5) (sourceB727 + difference 5 0) sourceC727) = raw12186 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12186; decide +kernel
    rw [ha]
    exact (canonical12186 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA727 + difference 1 0) (sourceB727 + difference 0 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA727 + difference 1 0) (sourceB727 + difference 0 1) sourceC727) = raw12187 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12187; decide +kernel
    rw [ha]
    exact (canonical12187 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA727 + difference 1 2) (sourceB727 + difference 2 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA727 + difference 1 2) (sourceB727 + difference 2 1) sourceC727) = raw12188 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12188; decide +kernel
    rw [ha]
    exact (canonical12188 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA727 + difference 1 3) (sourceB727 + difference 3 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA727 + difference 1 3) (sourceB727 + difference 3 1) sourceC727) = raw12189 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12189; decide +kernel
    rw [ha]
    exact (canonical12189 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA727 + difference 1 4) (sourceB727 + difference 4 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA727 + difference 1 4) (sourceB727 + difference 4 1) sourceC727) = raw12190 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12190; decide +kernel
    rw [ha]
    exact (canonical12190 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA727 + difference 1 5) (sourceB727 + difference 5 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA727 + difference 1 5) (sourceB727 + difference 5 1) sourceC727) = raw12191 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12191; decide +kernel
    rw [ha]
    exact (canonical12191 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA727 + difference 2 0) (sourceB727 + difference 0 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA727 + difference 2 0) (sourceB727 + difference 0 2) sourceC727) = raw11665 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11665; decide +kernel
    rw [ha]
    exact (canonical11665 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA727 + difference 2 1) (sourceB727 + difference 1 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA727 + difference 2 1) (sourceB727 + difference 1 2) sourceC727) = raw12019 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12019; decide +kernel
    rw [ha]
    exact (canonical12019 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA727 + difference 2 3) (sourceB727 + difference 3 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA727 + difference 2 3) (sourceB727 + difference 3 2) sourceC727) = raw11667 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11667; decide +kernel
    rw [ha]
    exact (canonical11667 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA727 + difference 2 4) (sourceB727 + difference 4 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA727 + difference 2 4) (sourceB727 + difference 4 2) sourceC727) = raw11668 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11668; decide +kernel
    rw [ha]
    exact (canonical11668 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA727 + difference 2 5) (sourceB727 + difference 5 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA727 + difference 2 5) (sourceB727 + difference 5 2) sourceC727) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA727 + difference 3 0) (sourceB727 + difference 0 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA727 + difference 3 0) (sourceB727 + difference 0 3) sourceC727) = raw12192 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12192; decide +kernel
    rw [ha]
    exact (canonical12192 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA727 + difference 3 1) (sourceB727 + difference 1 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA727 + difference 3 1) (sourceB727 + difference 1 3) sourceC727) = raw11677 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11677; decide +kernel
    rw [ha]
    exact (canonical11677 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA727 + difference 3 2) (sourceB727 + difference 2 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA727 + difference 3 2) (sourceB727 + difference 2 3) sourceC727) = raw12193 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12193; decide +kernel
    rw [ha]
    exact (canonical12193 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA727 + difference 3 4) (sourceB727 + difference 4 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA727 + difference 3 4) (sourceB727 + difference 4 3) sourceC727) = raw12194 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12194; decide +kernel
    rw [ha]
    exact (canonical12194 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA727 + difference 3 5) (sourceB727 + difference 5 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA727 + difference 3 5) (sourceB727 + difference 5 3) sourceC727) = raw12195 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12195; decide +kernel
    rw [ha]
    exact (canonical12195 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA727 + difference 4 0) (sourceB727 + difference 0 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA727 + difference 4 0) (sourceB727 + difference 0 4) sourceC727) = raw12196 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12196; decide +kernel
    rw [ha]
    exact (canonical12196 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA727 + difference 4 1) (sourceB727 + difference 1 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA727 + difference 4 1) (sourceB727 + difference 1 4) sourceC727) = raw11682 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11682; decide +kernel
    rw [ha]
    exact (canonical11682 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA727 + difference 4 2) (sourceB727 + difference 2 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA727 + difference 4 2) (sourceB727 + difference 2 4) sourceC727) = raw12197 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12197; decide +kernel
    rw [ha]
    exact (canonical12197 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA727 + difference 4 3) (sourceB727 + difference 3 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA727 + difference 4 3) (sourceB727 + difference 3 4) sourceC727) = raw12198 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12198; decide +kernel
    rw [ha]
    exact (canonical12198 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA727 + difference 4 5) (sourceB727 + difference 5 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA727 + difference 4 5) (sourceB727 + difference 5 4) sourceC727) = raw12199 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12199; decide +kernel
    rw [ha]
    exact (canonical12199 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA727 + difference 5 0) (sourceB727 + difference 0 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA727 + difference 5 0) (sourceB727 + difference 0 5) sourceC727) = raw12200 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12200; decide +kernel
    rw [ha]
    exact (canonical12200 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA727 + difference 5 1) (sourceB727 + difference 1 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA727 + difference 5 1) (sourceB727 + difference 1 5) sourceC727) = raw11687 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11687; decide +kernel
    rw [ha]
    exact (canonical11687 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA727 + difference 5 2) (sourceB727 + difference 2 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA727 + difference 5 2) (sourceB727 + difference 2 5) sourceC727) = raw12201 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12201; decide +kernel
    rw [ha]
    exact (canonical12201 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA727 + difference 5 3) (sourceB727 + difference 3 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA727 + difference 5 3) (sourceB727 + difference 3 5) sourceC727) = raw12202 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12202; decide +kernel
    rw [ha]
    exact (canonical12202 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA727 + difference 5 4) (sourceB727 + difference 4 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA727 + difference 5 4) (sourceB727 + difference 4 5) sourceC727) = raw12203 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12203; decide +kernel
    rw [ha]
    exact (canonical12203 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA727 sourceB727 sourceC727
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm727, Integer.Sparse.eval]
  linarith only [hs]

def sourceA728 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB728 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC728 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm728 : Integer.Sparse Master := [(Sum.inr 2754, 2), (Sum.inr 2755, 1), (Sum.inr 2764, 2), (Sum.inr 2769, 2), (Sum.inr 2782, 2), (Sum.inr 2785, 1), (Sum.inr 3085, 2), (Sum.inr 3097, 4), (Sum.inr 3100, 2), (Sum.inr 3109, 4), (Sum.inr 3119, 2), (Sum.inr 3122, 2), (Sum.inr 3227, 2), (Sum.inr 3229, 2)]

theorem sourceEq728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm728 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA728 + difference 0 1) (sourceB728 + difference 1 0) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA728 + difference 0 1) (sourceB728 + difference 1 0) sourceC728) = raw11721 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw11721; decide +kernel
    rw [ha]
    exact (canonical11721 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA728 + difference 0 2) (sourceB728 + difference 2 0) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA728 + difference 0 2) (sourceB728 + difference 2 0) sourceC728) = raw12204 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12204; decide +kernel
    rw [ha]
    exact (canonical12204 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA728 + difference 0 3) (sourceB728 + difference 3 0) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA728 + difference 0 3) (sourceB728 + difference 3 0) sourceC728) = raw12205 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12205; decide +kernel
    rw [ha]
    exact (canonical12205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA728 + difference 0 4) (sourceB728 + difference 4 0) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA728 + difference 0 4) (sourceB728 + difference 4 0) sourceC728) = raw12206 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12206; decide +kernel
    rw [ha]
    exact (canonical12206 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA728 + difference 0 5) (sourceB728 + difference 5 0) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2785) := by
    have ha : (tripleCharges (sourceA728 + difference 0 5) (sourceB728 + difference 5 0) sourceC728) = raw12207 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12207; decide +kernel
    rw [ha]
    exact (canonical12207 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA728 + difference 1 0) (sourceB728 + difference 0 1) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA728 + difference 1 0) (sourceB728 + difference 0 1) sourceC728) = raw12208 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12208; decide +kernel
    rw [ha]
    exact (canonical12208 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA728 + difference 1 2) (sourceB728 + difference 2 1) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA728 + difference 1 2) (sourceB728 + difference 2 1) sourceC728) = raw12209 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12209; decide +kernel
    rw [ha]
    exact (canonical12209 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA728 + difference 1 3) (sourceB728 + difference 3 1) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA728 + difference 1 3) (sourceB728 + difference 3 1) sourceC728) = raw12210 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12210; decide +kernel
    rw [ha]
    exact (canonical12210 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA728 + difference 1 4) (sourceB728 + difference 4 1) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA728 + difference 1 4) (sourceB728 + difference 4 1) sourceC728) = raw12211 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12211; decide +kernel
    rw [ha]
    exact (canonical12211 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA728 + difference 1 5) (sourceB728 + difference 5 1) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA728 + difference 1 5) (sourceB728 + difference 5 1) sourceC728) = raw12212 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12212; decide +kernel
    rw [ha]
    exact (canonical12212 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA728 + difference 2 0) (sourceB728 + difference 0 2) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA728 + difference 2 0) (sourceB728 + difference 0 2) sourceC728) = raw11725 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw11725; decide +kernel
    rw [ha]
    exact (canonical11725 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA728 + difference 2 1) (sourceB728 + difference 1 2) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA728 + difference 2 1) (sourceB728 + difference 1 2) sourceC728) = raw12063 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12063; decide +kernel
    rw [ha]
    exact (canonical12063 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA728 + difference 2 3) (sourceB728 + difference 3 2) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA728 + difference 2 3) (sourceB728 + difference 3 2) sourceC728) = raw11727 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw11727; decide +kernel
    rw [ha]
    exact (canonical11727 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA728 + difference 2 4) (sourceB728 + difference 4 2) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA728 + difference 2 4) (sourceB728 + difference 4 2) sourceC728) = raw11728 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw11728; decide +kernel
    rw [ha]
    exact (canonical11728 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA728 + difference 2 5) (sourceB728 + difference 5 2) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA728 + difference 2 5) (sourceB728 + difference 5 2) sourceC728) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA728 + difference 3 0) (sourceB728 + difference 0 3) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA728 + difference 3 0) (sourceB728 + difference 0 3) sourceC728) = raw12213 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12213; decide +kernel
    rw [ha]
    exact (canonical12213 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA728 + difference 3 1) (sourceB728 + difference 1 3) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA728 + difference 3 1) (sourceB728 + difference 1 3) sourceC728) = raw11737 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw11737; decide +kernel
    rw [ha]
    exact (canonical11737 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA728 + difference 3 2) (sourceB728 + difference 2 3) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA728 + difference 3 2) (sourceB728 + difference 2 3) sourceC728) = raw12214 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12214; decide +kernel
    rw [ha]
    exact (canonical12214 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA728 + difference 3 4) (sourceB728 + difference 4 3) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA728 + difference 3 4) (sourceB728 + difference 4 3) sourceC728) = raw12215 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12215; decide +kernel
    rw [ha]
    exact (canonical12215 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA728 + difference 3 5) (sourceB728 + difference 5 3) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA728 + difference 3 5) (sourceB728 + difference 5 3) sourceC728) = raw12216 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12216; decide +kernel
    rw [ha]
    exact (canonical12216 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA728 + difference 4 0) (sourceB728 + difference 0 4) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA728 + difference 4 0) (sourceB728 + difference 0 4) sourceC728) = raw12217 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12217; decide +kernel
    rw [ha]
    exact (canonical12217 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA728 + difference 4 1) (sourceB728 + difference 1 4) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA728 + difference 4 1) (sourceB728 + difference 1 4) sourceC728) = raw11742 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw11742; decide +kernel
    rw [ha]
    exact (canonical11742 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA728 + difference 4 2) (sourceB728 + difference 2 4) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA728 + difference 4 2) (sourceB728 + difference 2 4) sourceC728) = raw12218 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12218; decide +kernel
    rw [ha]
    exact (canonical12218 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA728 + difference 4 3) (sourceB728 + difference 3 4) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA728 + difference 4 3) (sourceB728 + difference 3 4) sourceC728) = raw12219 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12219; decide +kernel
    rw [ha]
    exact (canonical12219 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA728 + difference 4 5) (sourceB728 + difference 5 4) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA728 + difference 4 5) (sourceB728 + difference 5 4) sourceC728) = raw12220 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12220; decide +kernel
    rw [ha]
    exact (canonical12220 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA728 + difference 5 0) (sourceB728 + difference 0 5) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA728 + difference 5 0) (sourceB728 + difference 0 5) sourceC728) = raw12221 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12221; decide +kernel
    rw [ha]
    exact (canonical12221 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA728 + difference 5 1) (sourceB728 + difference 1 5) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA728 + difference 5 1) (sourceB728 + difference 1 5) sourceC728) = raw11747 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw11747; decide +kernel
    rw [ha]
    exact (canonical11747 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA728 + difference 5 2) (sourceB728 + difference 2 5) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA728 + difference 5 2) (sourceB728 + difference 2 5) sourceC728) = raw12222 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12222; decide +kernel
    rw [ha]
    exact (canonical12222 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA728 + difference 5 3) (sourceB728 + difference 3 5) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA728 + difference 5 3) (sourceB728 + difference 3 5) sourceC728) = raw12223 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12223; decide +kernel
    rw [ha]
    exact (canonical12223 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA728 + difference 5 4) (sourceB728 + difference 4 5) sourceC728) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA728 + difference 5 4) (sourceB728 + difference 4 5) sourceC728) = raw12224 := by
      apply Matrix.ext; unfold tripleCharges sourceA728 sourceB728 sourceC728 difference raw12224; decide +kernel
    rw [ha]
    exact (canonical12224 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA728 sourceB728 sourceC728
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm728, Integer.Sparse.eval]
  linarith only [hs]

def sourceA729 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB729 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC729 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm729 : Integer.Sparse Master := [(Sum.inr 3581, 2), (Sum.inr 3583, 2), (Sum.inr 3623, 1), (Sum.inr 3628, 1), (Sum.inr 4083, -1)]

theorem sourceEq729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm729 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA729 + difference 0 0) (sourceB729 + difference 0 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA729 + difference 0 0) (sourceB729 + difference 0 0) sourceC729) = raw12225 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12225; decide +kernel
    rw [ha]
    exact (canonical12225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA729 + difference 0 1) (sourceB729 + difference 1 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA729 + difference 0 1) (sourceB729 + difference 1 0) sourceC729) = raw11752 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw11752; decide +kernel
    rw [ha]
    exact (canonical11752 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA729 + difference 0 2) (sourceB729 + difference 2 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA729 + difference 0 2) (sourceB729 + difference 2 0) sourceC729) = raw12226 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12226; decide +kernel
    rw [ha]
    exact (canonical12226 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA729 + difference 0 3) (sourceB729 + difference 3 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA729 + difference 0 3) (sourceB729 + difference 3 0) sourceC729) = raw12227 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12227; decide +kernel
    rw [ha]
    exact (canonical12227 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA729 + difference 0 4) (sourceB729 + difference 4 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA729 + difference 0 4) (sourceB729 + difference 4 0) sourceC729) = raw12228 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12228; decide +kernel
    rw [ha]
    exact (canonical12228 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA729 + difference 0 5) (sourceB729 + difference 5 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3628) := by
    have ha : (tripleCharges (sourceA729 + difference 0 5) (sourceB729 + difference 5 0) sourceC729) = raw12229 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12229; decide +kernel
    rw [ha]
    exact (canonical12229 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA729 + sourceB729) sourceC729) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA729 + sourceB729) sourceC729) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA729 sourceB729 sourceC729 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA729 sourceB729 sourceC729
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm729, Integer.Sparse.eval]
  linarith only [hs]

def sourceA730 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB730 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC730 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm730 : Integer.Sparse Master := [(Sum.inr 4595, 1), (Sum.inr 4596, 1), (Sum.inr 4597, 1), (Sum.inr 4607, 1), (Sum.inr 4616, 1), (Sum.inr 5091, 1), (Sum.inr 5096, 1), (Sum.inr 5103, 1), (Sum.inr 5144, 1), (Sum.inr 5146, 1), (Sum.inr 5160, 1), (Sum.inr 5196, 1), (Sum.inr 5198, 1), (Sum.inr 5200, 1), (Sum.inr 5256, 1), (Sum.inr 5258, 1), (Sum.inr 5260, 1), (Sum.inr 5271, 1), (Sum.inr 5286, 1), (Sum.inr 5287, 1), (Sum.inr 5289, 1), (Sum.inr 5291, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 1), (Sum.inr 5304, 1), (Sum.inr 5411, 1), (Sum.inr 5430, 1), (Sum.inr 5434, 1), (Sum.inr 5446, 1), (Sum.inr 5451, 1)]

theorem sourceEq730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm730 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA730 + difference 0 1) (sourceB730 + difference 1 0) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA730 + difference 0 1) (sourceB730 + difference 1 0) sourceC730) = raw12230 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12230; decide +kernel
    rw [ha]
    exact (canonical12230 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA730 + difference 0 2) (sourceB730 + difference 2 0) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA730 + difference 0 2) (sourceB730 + difference 2 0) sourceC730) = raw12231 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12231; decide +kernel
    rw [ha]
    exact (canonical12231 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA730 + difference 0 3) (sourceB730 + difference 3 0) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA730 + difference 0 3) (sourceB730 + difference 3 0) sourceC730) = raw12232 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12232; decide +kernel
    rw [ha]
    exact (canonical12232 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA730 + difference 0 4) (sourceB730 + difference 4 0) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA730 + difference 0 4) (sourceB730 + difference 4 0) sourceC730) = raw12233 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12233; decide +kernel
    rw [ha]
    exact (canonical12233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA730 + difference 0 5) (sourceB730 + difference 5 0) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA730 + difference 0 5) (sourceB730 + difference 5 0) sourceC730) = raw12234 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12234; decide +kernel
    rw [ha]
    exact (canonical12234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA730 + difference 1 0) (sourceB730 + difference 0 1) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4595) := by
    have ha : (tripleCharges (sourceA730 + difference 1 0) (sourceB730 + difference 0 1) sourceC730) = raw12235 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12235; decide +kernel
    rw [ha]
    exact (canonical12235 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA730 + difference 1 2) (sourceB730 + difference 2 1) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5196) := by
    have ha : (tripleCharges (sourceA730 + difference 1 2) (sourceB730 + difference 2 1) sourceC730) = raw12236 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12236; decide +kernel
    rw [ha]
    exact (canonical12236 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA730 + difference 1 3) (sourceB730 + difference 3 1) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA730 + difference 1 3) (sourceB730 + difference 3 1) sourceC730) = raw12237 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12237; decide +kernel
    rw [ha]
    exact (canonical12237 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA730 + difference 1 4) (sourceB730 + difference 4 1) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA730 + difference 1 4) (sourceB730 + difference 4 1) sourceC730) = raw12238 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12238; decide +kernel
    rw [ha]
    exact (canonical12238 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA730 + difference 1 5) (sourceB730 + difference 5 1) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA730 + difference 1 5) (sourceB730 + difference 5 1) sourceC730) = raw12239 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12239; decide +kernel
    rw [ha]
    exact (canonical12239 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA730 + difference 2 0) (sourceB730 + difference 0 2) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA730 + difference 2 0) (sourceB730 + difference 0 2) sourceC730) = raw12240 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12240; decide +kernel
    rw [ha]
    exact (canonical12240 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA730 + difference 2 1) (sourceB730 + difference 1 2) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA730 + difference 2 1) (sourceB730 + difference 1 2) sourceC730) = raw12241 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12241; decide +kernel
    rw [ha]
    exact (canonical12241 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA730 + difference 2 3) (sourceB730 + difference 3 2) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA730 + difference 2 3) (sourceB730 + difference 3 2) sourceC730) = raw12242 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12242; decide +kernel
    rw [ha]
    exact (canonical12242 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA730 + difference 2 4) (sourceB730 + difference 4 2) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA730 + difference 2 4) (sourceB730 + difference 4 2) sourceC730) = raw12243 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12243; decide +kernel
    rw [ha]
    exact (canonical12243 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA730 + difference 2 5) (sourceB730 + difference 5 2) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA730 + difference 2 5) (sourceB730 + difference 5 2) sourceC730) = raw12244 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12244; decide +kernel
    rw [ha]
    exact (canonical12244 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA730 + difference 3 0) (sourceB730 + difference 0 3) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4596) := by
    have ha : (tripleCharges (sourceA730 + difference 3 0) (sourceB730 + difference 0 3) sourceC730) = raw12245 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12245; decide +kernel
    rw [ha]
    exact (canonical12245 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA730 + difference 3 1) (sourceB730 + difference 1 3) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5091) := by
    have ha : (tripleCharges (sourceA730 + difference 3 1) (sourceB730 + difference 1 3) sourceC730) = raw12246 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12246; decide +kernel
    rw [ha]
    exact (canonical12246 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA730 + difference 3 2) (sourceB730 + difference 2 3) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5096) := by
    have ha : (tripleCharges (sourceA730 + difference 3 2) (sourceB730 + difference 2 3) sourceC730) = raw12247 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12247; decide +kernel
    rw [ha]
    exact (canonical12247 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA730 + difference 3 4) (sourceB730 + difference 4 3) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA730 + difference 3 4) (sourceB730 + difference 4 3) sourceC730) = raw12248 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12248; decide +kernel
    rw [ha]
    exact (canonical12248 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA730 + difference 3 5) (sourceB730 + difference 5 3) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA730 + difference 3 5) (sourceB730 + difference 5 3) sourceC730) = raw12249 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12249; decide +kernel
    rw [ha]
    exact (canonical12249 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA730 + difference 4 0) (sourceB730 + difference 0 4) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4597) := by
    have ha : (tripleCharges (sourceA730 + difference 4 0) (sourceB730 + difference 0 4) sourceC730) = raw12250 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12250; decide +kernel
    rw [ha]
    exact (canonical12250 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA730 + difference 4 1) (sourceB730 + difference 1 4) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5146) := by
    have ha : (tripleCharges (sourceA730 + difference 4 1) (sourceB730 + difference 1 4) sourceC730) = raw12251 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12251; decide +kernel
    rw [ha]
    exact (canonical12251 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA730 + difference 4 2) (sourceB730 + difference 2 4) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5200) := by
    have ha : (tripleCharges (sourceA730 + difference 4 2) (sourceB730 + difference 2 4) sourceC730) = raw12252 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12252; decide +kernel
    rw [ha]
    exact (canonical12252 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA730 + difference 4 3) (sourceB730 + difference 3 4) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA730 + difference 4 3) (sourceB730 + difference 3 4) sourceC730) = raw12253 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12253; decide +kernel
    rw [ha]
    exact (canonical12253 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA730 + difference 4 5) (sourceB730 + difference 5 4) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA730 + difference 4 5) (sourceB730 + difference 5 4) sourceC730) = raw12254 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12254; decide +kernel
    rw [ha]
    exact (canonical12254 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA730 + difference 5 0) (sourceB730 + difference 0 5) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA730 + difference 5 0) (sourceB730 + difference 0 5) sourceC730) = raw12255 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12255; decide +kernel
    rw [ha]
    exact (canonical12255 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA730 + difference 5 1) (sourceB730 + difference 1 5) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA730 + difference 5 1) (sourceB730 + difference 1 5) sourceC730) = raw12256 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12256; decide +kernel
    rw [ha]
    exact (canonical12256 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA730 + difference 5 2) (sourceB730 + difference 2 5) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA730 + difference 5 2) (sourceB730 + difference 2 5) sourceC730) = raw12257 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12257; decide +kernel
    rw [ha]
    exact (canonical12257 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA730 + difference 5 3) (sourceB730 + difference 3 5) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA730 + difference 5 3) (sourceB730 + difference 3 5) sourceC730) = raw12258 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12258; decide +kernel
    rw [ha]
    exact (canonical12258 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA730 + difference 5 4) (sourceB730 + difference 4 5) sourceC730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA730 + difference 5 4) (sourceB730 + difference 4 5) sourceC730) = raw12259 := by
      apply Matrix.ext; unfold tripleCharges sourceA730 sourceB730 sourceC730 difference raw12259; decide +kernel
    rw [ha]
    exact (canonical12259 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA730 sourceB730 sourceC730
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm730, Integer.Sparse.eval]
  linarith only [hs]

def sourceA731 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB731 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC731 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm731 : Integer.Sparse Master := [(Sum.inr 1228, 1), (Sum.inr 1229, 1), (Sum.inr 1230, 1), (Sum.inr 1241, 1), (Sum.inr 1291, 1), (Sum.inr 2874, 1), (Sum.inr 2875, 1), (Sum.inr 2876, 1), (Sum.inr 2885, 1), (Sum.inr 2921, 1), (Sum.inr 2922, 1), (Sum.inr 2928, 1), (Sum.inr 2951, 1), (Sum.inr 3023, 1), (Sum.inr 3024, 1), (Sum.inr 3025, 1), (Sum.inr 3051, 1), (Sum.inr 3085, 1), (Sum.inr 3086, 1), (Sum.inr 3089, 1), (Sum.inr 3097, 1), (Sum.inr 3098, 1), (Sum.inr 3103, 1), (Sum.inr 3109, 1), (Sum.inr 3119, 1), (Sum.inr 3809, 1), (Sum.inr 3959, 1), (Sum.inr 3972, 1), (Sum.inr 3982, 1), (Sum.inr 3987, 1)]

theorem sourceEq731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm731 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA731 + difference 0 1) (sourceB731 + difference 1 0) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA731 + difference 0 1) (sourceB731 + difference 1 0) sourceC731) = raw12260 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12260; decide +kernel
    rw [ha]
    exact (canonical12260 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA731 + difference 0 2) (sourceB731 + difference 2 0) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA731 + difference 0 2) (sourceB731 + difference 2 0) sourceC731) = raw12261 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12261; decide +kernel
    rw [ha]
    exact (canonical12261 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA731 + difference 0 3) (sourceB731 + difference 3 0) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA731 + difference 0 3) (sourceB731 + difference 3 0) sourceC731) = raw12262 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12262; decide +kernel
    rw [ha]
    exact (canonical12262 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA731 + difference 0 4) (sourceB731 + difference 4 0) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA731 + difference 0 4) (sourceB731 + difference 4 0) sourceC731) = raw12263 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12263; decide +kernel
    rw [ha]
    exact (canonical12263 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA731 + difference 0 5) (sourceB731 + difference 5 0) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA731 + difference 0 5) (sourceB731 + difference 5 0) sourceC731) = raw12264 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12264; decide +kernel
    rw [ha]
    exact (canonical12264 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA731 + difference 1 0) (sourceB731 + difference 0 1) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA731 + difference 1 0) (sourceB731 + difference 0 1) sourceC731) = raw12265 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12265; decide +kernel
    rw [ha]
    exact (canonical12265 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA731 + difference 1 2) (sourceB731 + difference 2 1) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2874) := by
    have ha : (tripleCharges (sourceA731 + difference 1 2) (sourceB731 + difference 2 1) sourceC731) = raw12266 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12266; decide +kernel
    rw [ha]
    exact (canonical12266 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA731 + difference 1 3) (sourceB731 + difference 3 1) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA731 + difference 1 3) (sourceB731 + difference 3 1) sourceC731) = raw12267 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12267; decide +kernel
    rw [ha]
    exact (canonical12267 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA731 + difference 1 4) (sourceB731 + difference 4 1) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA731 + difference 1 4) (sourceB731 + difference 4 1) sourceC731) = raw12268 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12268; decide +kernel
    rw [ha]
    exact (canonical12268 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA731 + difference 1 5) (sourceB731 + difference 5 1) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA731 + difference 1 5) (sourceB731 + difference 5 1) sourceC731) = raw12269 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12269; decide +kernel
    rw [ha]
    exact (canonical12269 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA731 + difference 2 0) (sourceB731 + difference 0 2) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA731 + difference 2 0) (sourceB731 + difference 0 2) sourceC731) = raw12270 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12270; decide +kernel
    rw [ha]
    exact (canonical12270 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA731 + difference 2 1) (sourceB731 + difference 1 2) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA731 + difference 2 1) (sourceB731 + difference 1 2) sourceC731) = raw12271 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12271; decide +kernel
    rw [ha]
    exact (canonical12271 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA731 + difference 2 3) (sourceB731 + difference 3 2) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA731 + difference 2 3) (sourceB731 + difference 3 2) sourceC731) = raw12272 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12272; decide +kernel
    rw [ha]
    exact (canonical12272 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA731 + difference 2 4) (sourceB731 + difference 4 2) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA731 + difference 2 4) (sourceB731 + difference 4 2) sourceC731) = raw12273 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12273; decide +kernel
    rw [ha]
    exact (canonical12273 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA731 + difference 2 5) (sourceB731 + difference 5 2) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA731 + difference 2 5) (sourceB731 + difference 5 2) sourceC731) = raw12274 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12274; decide +kernel
    rw [ha]
    exact (canonical12274 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA731 + difference 3 0) (sourceB731 + difference 0 3) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA731 + difference 3 0) (sourceB731 + difference 0 3) sourceC731) = raw12275 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12275; decide +kernel
    rw [ha]
    exact (canonical12275 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA731 + difference 3 1) (sourceB731 + difference 1 3) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2921) := by
    have ha : (tripleCharges (sourceA731 + difference 3 1) (sourceB731 + difference 1 3) sourceC731) = raw12276 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12276; decide +kernel
    rw [ha]
    exact (canonical12276 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA731 + difference 3 2) (sourceB731 + difference 2 3) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2875) := by
    have ha : (tripleCharges (sourceA731 + difference 3 2) (sourceB731 + difference 2 3) sourceC731) = raw12277 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12277; decide +kernel
    rw [ha]
    exact (canonical12277 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA731 + difference 3 4) (sourceB731 + difference 4 3) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA731 + difference 3 4) (sourceB731 + difference 4 3) sourceC731) = raw12278 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12278; decide +kernel
    rw [ha]
    exact (canonical12278 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA731 + difference 3 5) (sourceB731 + difference 5 3) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA731 + difference 3 5) (sourceB731 + difference 5 3) sourceC731) = raw12279 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12279; decide +kernel
    rw [ha]
    exact (canonical12279 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA731 + difference 4 0) (sourceB731 + difference 0 4) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA731 + difference 4 0) (sourceB731 + difference 0 4) sourceC731) = raw12280 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12280; decide +kernel
    rw [ha]
    exact (canonical12280 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA731 + difference 4 1) (sourceB731 + difference 1 4) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2922) := by
    have ha : (tripleCharges (sourceA731 + difference 4 1) (sourceB731 + difference 1 4) sourceC731) = raw12281 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12281; decide +kernel
    rw [ha]
    exact (canonical12281 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA731 + difference 4 2) (sourceB731 + difference 2 4) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2876) := by
    have ha : (tripleCharges (sourceA731 + difference 4 2) (sourceB731 + difference 2 4) sourceC731) = raw12282 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12282; decide +kernel
    rw [ha]
    exact (canonical12282 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA731 + difference 4 3) (sourceB731 + difference 3 4) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA731 + difference 4 3) (sourceB731 + difference 3 4) sourceC731) = raw12283 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12283; decide +kernel
    rw [ha]
    exact (canonical12283 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA731 + difference 4 5) (sourceB731 + difference 5 4) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA731 + difference 4 5) (sourceB731 + difference 5 4) sourceC731) = raw12284 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12284; decide +kernel
    rw [ha]
    exact (canonical12284 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA731 + difference 5 0) (sourceB731 + difference 0 5) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA731 + difference 5 0) (sourceB731 + difference 0 5) sourceC731) = raw12285 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12285; decide +kernel
    rw [ha]
    exact (canonical12285 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA731 + difference 5 1) (sourceB731 + difference 1 5) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA731 + difference 5 1) (sourceB731 + difference 1 5) sourceC731) = raw12286 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12286; decide +kernel
    rw [ha]
    exact (canonical12286 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA731 + difference 5 2) (sourceB731 + difference 2 5) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA731 + difference 5 2) (sourceB731 + difference 2 5) sourceC731) = raw12287 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12287; decide +kernel
    rw [ha]
    exact (canonical12287 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA731 + difference 5 3) (sourceB731 + difference 3 5) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA731 + difference 5 3) (sourceB731 + difference 3 5) sourceC731) = raw12288 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12288; decide +kernel
    rw [ha]
    exact (canonical12288 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA731 + difference 5 4) (sourceB731 + difference 4 5) sourceC731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA731 + difference 5 4) (sourceB731 + difference 4 5) sourceC731) = raw12289 := by
      apply Matrix.ext; unfold tripleCharges sourceA731 sourceB731 sourceC731 difference raw12289; decide +kernel
    rw [ha]
    exact (canonical12289 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA731 sourceB731 sourceC731
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm731, Integer.Sparse.eval]
  linarith only [hs]

def sourceA732 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB732 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC732 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm732 : Integer.Sparse Master := [(Sum.inr 2500, 1), (Sum.inr 2502, 1), (Sum.inr 2506, 1), (Sum.inr 2513, 1), (Sum.inr 2781, 1), (Sum.inr 3286, 1), (Sum.inr 3287, 1), (Sum.inr 3296, 1), (Sum.inr 3303, 1), (Sum.inr 3525, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3540, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3560, 1), (Sum.inr 3566, 1), (Sum.inr 3567, 1), (Sum.inr 3570, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 3575, 1), (Sum.inr 3577, 1), (Sum.inr 3582, 1), (Sum.inr 3583, 1), (Sum.inr 3852, 1), (Sum.inr 3871, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3888, 1)]

theorem sourceEq732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm732 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA732 + difference 0 1) (sourceB732 + difference 1 0) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA732 + difference 0 1) (sourceB732 + difference 1 0) sourceC732) = raw12290 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12290; decide +kernel
    rw [ha]
    exact (canonical12290 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA732 + difference 0 2) (sourceB732 + difference 2 0) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA732 + difference 0 2) (sourceB732 + difference 2 0) sourceC732) = raw12291 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12291; decide +kernel
    rw [ha]
    exact (canonical12291 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA732 + difference 0 3) (sourceB732 + difference 3 0) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA732 + difference 0 3) (sourceB732 + difference 3 0) sourceC732) = raw12292 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12292; decide +kernel
    rw [ha]
    exact (canonical12292 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA732 + difference 0 4) (sourceB732 + difference 4 0) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA732 + difference 0 4) (sourceB732 + difference 4 0) sourceC732) = raw12293 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12293; decide +kernel
    rw [ha]
    exact (canonical12293 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA732 + difference 0 5) (sourceB732 + difference 5 0) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA732 + difference 0 5) (sourceB732 + difference 5 0) sourceC732) = raw12294 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12294; decide +kernel
    rw [ha]
    exact (canonical12294 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA732 + difference 1 0) (sourceB732 + difference 0 1) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA732 + difference 1 0) (sourceB732 + difference 0 1) sourceC732) = raw12295 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12295; decide +kernel
    rw [ha]
    exact (canonical12295 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA732 + difference 1 2) (sourceB732 + difference 2 1) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3566) := by
    have ha : (tripleCharges (sourceA732 + difference 1 2) (sourceB732 + difference 2 1) sourceC732) = raw12296 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12296; decide +kernel
    rw [ha]
    exact (canonical12296 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA732 + difference 1 3) (sourceB732 + difference 3 1) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA732 + difference 1 3) (sourceB732 + difference 3 1) sourceC732) = raw12297 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12297; decide +kernel
    rw [ha]
    exact (canonical12297 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA732 + difference 1 4) (sourceB732 + difference 4 1) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA732 + difference 1 4) (sourceB732 + difference 4 1) sourceC732) = raw12298 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12298; decide +kernel
    rw [ha]
    exact (canonical12298 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA732 + difference 1 5) (sourceB732 + difference 5 1) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA732 + difference 1 5) (sourceB732 + difference 5 1) sourceC732) = raw12299 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12299; decide +kernel
    rw [ha]
    exact (canonical12299 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA732 + difference 2 0) (sourceB732 + difference 0 2) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA732 + difference 2 0) (sourceB732 + difference 0 2) sourceC732) = raw12300 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12300; decide +kernel
    rw [ha]
    exact (canonical12300 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA732 + difference 2 1) (sourceB732 + difference 1 2) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA732 + difference 2 1) (sourceB732 + difference 1 2) sourceC732) = raw12301 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12301; decide +kernel
    rw [ha]
    exact (canonical12301 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA732 + difference 2 3) (sourceB732 + difference 3 2) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA732 + difference 2 3) (sourceB732 + difference 3 2) sourceC732) = raw12302 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12302; decide +kernel
    rw [ha]
    exact (canonical12302 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA732 + difference 2 4) (sourceB732 + difference 4 2) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA732 + difference 2 4) (sourceB732 + difference 4 2) sourceC732) = raw12303 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12303; decide +kernel
    rw [ha]
    exact (canonical12303 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA732 + difference 2 5) (sourceB732 + difference 5 2) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA732 + difference 2 5) (sourceB732 + difference 5 2) sourceC732) = raw12304 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12304; decide +kernel
    rw [ha]
    exact (canonical12304 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA732 + difference 3 0) (sourceB732 + difference 0 3) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA732 + difference 3 0) (sourceB732 + difference 0 3) sourceC732) = raw12305 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12305; decide +kernel
    rw [ha]
    exact (canonical12305 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA732 + difference 3 1) (sourceB732 + difference 1 3) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2500) := by
    have ha : (tripleCharges (sourceA732 + difference 3 1) (sourceB732 + difference 1 3) sourceC732) = raw12306 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12306; decide +kernel
    rw [ha]
    exact (canonical12306 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA732 + difference 3 2) (sourceB732 + difference 2 3) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2506) := by
    have ha : (tripleCharges (sourceA732 + difference 3 2) (sourceB732 + difference 2 3) sourceC732) = raw12307 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12307; decide +kernel
    rw [ha]
    exact (canonical12307 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA732 + difference 3 4) (sourceB732 + difference 4 3) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA732 + difference 3 4) (sourceB732 + difference 4 3) sourceC732) = raw12308 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12308; decide +kernel
    rw [ha]
    exact (canonical12308 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA732 + difference 3 5) (sourceB732 + difference 5 3) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA732 + difference 3 5) (sourceB732 + difference 5 3) sourceC732) = raw12309 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12309; decide +kernel
    rw [ha]
    exact (canonical12309 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA732 + difference 4 0) (sourceB732 + difference 0 4) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA732 + difference 4 0) (sourceB732 + difference 0 4) sourceC732) = raw12310 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12310; decide +kernel
    rw [ha]
    exact (canonical12310 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA732 + difference 4 1) (sourceB732 + difference 1 4) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3560) := by
    have ha : (tripleCharges (sourceA732 + difference 4 1) (sourceB732 + difference 1 4) sourceC732) = raw12311 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12311; decide +kernel
    rw [ha]
    exact (canonical12311 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA732 + difference 4 2) (sourceB732 + difference 2 4) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3575) := by
    have ha : (tripleCharges (sourceA732 + difference 4 2) (sourceB732 + difference 2 4) sourceC732) = raw12312 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12312; decide +kernel
    rw [ha]
    exact (canonical12312 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA732 + difference 4 3) (sourceB732 + difference 3 4) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA732 + difference 4 3) (sourceB732 + difference 3 4) sourceC732) = raw12313 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12313; decide +kernel
    rw [ha]
    exact (canonical12313 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA732 + difference 4 5) (sourceB732 + difference 5 4) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA732 + difference 4 5) (sourceB732 + difference 5 4) sourceC732) = raw12314 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12314; decide +kernel
    rw [ha]
    exact (canonical12314 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA732 + difference 5 0) (sourceB732 + difference 0 5) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA732 + difference 5 0) (sourceB732 + difference 0 5) sourceC732) = raw12315 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12315; decide +kernel
    rw [ha]
    exact (canonical12315 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA732 + difference 5 1) (sourceB732 + difference 1 5) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA732 + difference 5 1) (sourceB732 + difference 1 5) sourceC732) = raw12316 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12316; decide +kernel
    rw [ha]
    exact (canonical12316 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA732 + difference 5 2) (sourceB732 + difference 2 5) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA732 + difference 5 2) (sourceB732 + difference 2 5) sourceC732) = raw12317 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12317; decide +kernel
    rw [ha]
    exact (canonical12317 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA732 + difference 5 3) (sourceB732 + difference 3 5) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA732 + difference 5 3) (sourceB732 + difference 3 5) sourceC732) = raw12318 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12318; decide +kernel
    rw [ha]
    exact (canonical12318 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA732 + difference 5 4) (sourceB732 + difference 4 5) sourceC732) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA732 + difference 5 4) (sourceB732 + difference 4 5) sourceC732) = raw12319 := by
      apply Matrix.ext; unfold tripleCharges sourceA732 sourceB732 sourceC732 difference raw12319; decide +kernel
    rw [ha]
    exact (canonical12319 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA732 sourceB732 sourceC732
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm732, Integer.Sparse.eval]
  linarith only [hs]

def sourceA733 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB733 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC733 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm733 : Integer.Sparse Master := [(Sum.inr 2763, 1), (Sum.inr 3813, 1), (Sum.inr 3848, 1), (Sum.inr 3884, 1), (Sum.inr 3903, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

theorem sourceEq733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm733 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA733 + difference 0 0) (sourceB733 + difference 0 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA733 + difference 0 0) (sourceB733 + difference 0 0) sourceC733) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA733 + difference 0 1) (sourceB733 + difference 1 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA733 + difference 0 1) (sourceB733 + difference 1 0) sourceC733) = raw12321 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12321; decide +kernel
    rw [ha]
    exact (canonical12321 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA733 + difference 0 2) (sourceB733 + difference 2 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA733 + difference 0 2) (sourceB733 + difference 2 0) sourceC733) = raw12322 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12322; decide +kernel
    rw [ha]
    exact (canonical12322 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA733 + difference 0 3) (sourceB733 + difference 3 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA733 + difference 0 3) (sourceB733 + difference 3 0) sourceC733) = raw12323 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12323; decide +kernel
    rw [ha]
    exact (canonical12323 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA733 + difference 0 4) (sourceB733 + difference 4 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA733 + difference 0 4) (sourceB733 + difference 4 0) sourceC733) = raw12324 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12324; decide +kernel
    rw [ha]
    exact (canonical12324 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA733 + difference 0 5) (sourceB733 + difference 5 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA733 + difference 0 5) (sourceB733 + difference 5 0) sourceC733) = raw12325 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12325; decide +kernel
    rw [ha]
    exact (canonical12325 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA733 + sourceB733) sourceC733) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA733 + sourceB733) sourceC733) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA733 sourceB733 sourceC733 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA733 sourceB733 sourceC733
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm733, Integer.Sparse.eval]
  linarith only [hs]

def sourceA734 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB734 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC734 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm734 : Integer.Sparse Master := [(Sum.inr 1259, 1), (Sum.inr 1261, 1), (Sum.inr 1263, 1), (Sum.inr 1268, 1), (Sum.inr 1291, 1), (Sum.inr 2763, 1), (Sum.inr 4092, -1)]

theorem sourceEq734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm734 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA734 + difference 0 0) (sourceB734 + difference 0 0) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA734 + difference 0 0) (sourceB734 + difference 0 0) sourceC734) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA734 + difference 1 0) (sourceB734 + difference 0 1) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1259) := by
    have ha : (tripleCharges (sourceA734 + difference 1 0) (sourceB734 + difference 0 1) sourceC734) = raw12327 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12327; decide +kernel
    rw [ha]
    exact (canonical12327 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA734 + difference 2 0) (sourceB734 + difference 0 2) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA734 + difference 2 0) (sourceB734 + difference 0 2) sourceC734) = raw12328 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12328; decide +kernel
    rw [ha]
    exact (canonical12328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA734 + difference 3 0) (sourceB734 + difference 0 3) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1268) := by
    have ha : (tripleCharges (sourceA734 + difference 3 0) (sourceB734 + difference 0 3) sourceC734) = raw12329 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12329; decide +kernel
    rw [ha]
    exact (canonical12329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA734 + difference 4 0) (sourceB734 + difference 0 4) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1263) := by
    have ha : (tripleCharges (sourceA734 + difference 4 0) (sourceB734 + difference 0 4) sourceC734) = raw12330 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12330; decide +kernel
    rw [ha]
    exact (canonical12330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA734 + difference 5 0) (sourceB734 + difference 0 5) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA734 + difference 5 0) (sourceB734 + difference 0 5) sourceC734) = raw12331 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12331; decide +kernel
    rw [ha]
    exact (canonical12331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA734 + sourceB734) sourceC734) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA734 + sourceB734) sourceC734) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA734 sourceB734 sourceC734 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA734 sourceB734 sourceC734
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm734, Integer.Sparse.eval]
  linarith only [hs]

def sourceA735 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB735 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC735 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm735 : Integer.Sparse Master := [(Sum.inr 2566, 1), (Sum.inr 2568, 1), (Sum.inr 2571, 1), (Sum.inr 2587, 1), (Sum.inr 2763, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

theorem sourceEq735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm735 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA735 + difference 0 1) (sourceB735 + difference 1 0) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA735 + difference 0 1) (sourceB735 + difference 1 0) sourceC735) = raw12321 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12321; decide +kernel
    rw [ha]
    exact (canonical12321 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA735 + difference 1 1) (sourceB735 + difference 1 1) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA735 + difference 1 1) (sourceB735 + difference 1 1) sourceC735) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA735 + difference 2 1) (sourceB735 + difference 1 2) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA735 + difference 2 1) (sourceB735 + difference 1 2) sourceC735) = raw12332 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12332; decide +kernel
    rw [ha]
    exact (canonical12332 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA735 + difference 3 1) (sourceB735 + difference 1 3) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2571) := by
    have ha : (tripleCharges (sourceA735 + difference 3 1) (sourceB735 + difference 1 3) sourceC735) = raw12333 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12333; decide +kernel
    rw [ha]
    exact (canonical12333 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA735 + difference 4 1) (sourceB735 + difference 1 4) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2568) := by
    have ha : (tripleCharges (sourceA735 + difference 4 1) (sourceB735 + difference 1 4) sourceC735) = raw12334 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12334; decide +kernel
    rw [ha]
    exact (canonical12334 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA735 + difference 5 1) (sourceB735 + difference 1 5) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA735 + difference 5 1) (sourceB735 + difference 1 5) sourceC735) = raw12335 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12335; decide +kernel
    rw [ha]
    exact (canonical12335 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA735 + sourceB735) sourceC735) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA735 + sourceB735) sourceC735) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA735 sourceB735 sourceC735 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA735 sourceB735 sourceC735
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm735, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
