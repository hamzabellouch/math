import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical32

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA64 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB64 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC64 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm64 : Integer.Sparse Master := [(Sum.inr 1460, 1), (Sum.inr 2083, 1), (Sum.inr 2092, 2), (Sum.inr 2235, 1), (Sum.inr 3158, 1), (Sum.inr 4083, -1)]

theorem sourceEq64 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm64 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA64 + difference 0 2) (sourceB64 + difference 2 0) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA64 + difference 0 2) (sourceB64 + difference 2 0) sourceC64) = raw3830 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3830; decide +kernel
    rw [ha]
    exact (canonical3830 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA64 + difference 1 2) (sourceB64 + difference 2 1) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA64 + difference 1 2) (sourceB64 + difference 2 1) sourceC64) = raw3840 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3840; decide +kernel
    rw [ha]
    exact (canonical3840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA64 + difference 2 2) (sourceB64 + difference 2 2) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA64 + difference 2 2) (sourceB64 + difference 2 2) sourceC64) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA64 + difference 3 2) (sourceB64 + difference 2 3) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA64 + difference 3 2) (sourceB64 + difference 2 3) sourceC64) = raw3851 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3851; decide +kernel
    rw [ha]
    exact (canonical3851 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA64 + difference 4 2) (sourceB64 + difference 2 4) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA64 + difference 4 2) (sourceB64 + difference 2 4) sourceC64) = raw3852 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3852; decide +kernel
    rw [ha]
    exact (canonical3852 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA64 + difference 5 2) (sourceB64 + difference 2 5) sourceC64) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1460) := by
    have ha : (tripleCharges (sourceA64 + difference 5 2) (sourceB64 + difference 2 5) sourceC64) = raw3853 := by
      apply Matrix.ext; unfold tripleCharges sourceA64 sourceB64 sourceC64 difference raw3853; decide +kernel
    rw [ha]
    exact (canonical3853 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA64 + sourceB64) sourceC64) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA64 + sourceB64) sourceC64) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA64 sourceB64 sourceC64 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA64 sourceB64 sourceC64
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm64, Integer.Sparse.eval]
  linarith only [hs]

def sourceA65 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB65 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC65 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm65 : Integer.Sparse Master := [(Sum.inr 1016, 1), (Sum.inr 1457, 1), (Sum.inr 1460, 3), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

theorem sourceEq65 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm65 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA65 + difference 5 0) (sourceB65 + difference 0 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1016) := by
    have ha : (tripleCharges (sourceA65 + difference 5 0) (sourceB65 + difference 0 5) sourceC65) = raw3839 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3839; decide +kernel
    rw [ha]
    exact (canonical3839 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA65 + difference 5 1) (sourceB65 + difference 1 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1457) := by
    have ha : (tripleCharges (sourceA65 + difference 5 1) (sourceB65 + difference 1 5) sourceC65) = raw3847 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3847; decide +kernel
    rw [ha]
    exact (canonical3847 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA65 + difference 5 2) (sourceB65 + difference 2 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1460) := by
    have ha : (tripleCharges (sourceA65 + difference 5 2) (sourceB65 + difference 2 5) sourceC65) = raw3853 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3853; decide +kernel
    rw [ha]
    exact (canonical3853 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA65 + difference 5 3) (sourceB65 + difference 3 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1460) := by
    have ha : (tripleCharges (sourceA65 + difference 5 3) (sourceB65 + difference 3 5) sourceC65) = raw3854 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3854; decide +kernel
    rw [ha]
    exact (canonical3854 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA65 + difference 5 4) (sourceB65 + difference 4 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1460) := by
    have ha : (tripleCharges (sourceA65 + difference 5 4) (sourceB65 + difference 4 5) sourceC65) = raw3855 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3855; decide +kernel
    rw [ha]
    exact (canonical3855 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA65 + difference 5 5) (sourceB65 + difference 5 5) sourceC65) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA65 + difference 5 5) (sourceB65 + difference 5 5) sourceC65) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA65 sourceB65 sourceC65 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA65 + sourceB65) sourceC65) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA65 + sourceB65) sourceC65) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA65 sourceB65 sourceC65 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA65 sourceB65 sourceC65
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm65, Integer.Sparse.eval]
  linarith only [hs]

def sourceA66 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceB66 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC66 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm66 : Integer.Sparse Master := [(Sum.inr 4482, 2), (Sum.inr 4483, 6), (Sum.inr 4494, 2), (Sum.inr 4822, 3), (Sum.inr 4830, 2), (Sum.inr 4886, 3), (Sum.inr 4890, 6), (Sum.inr 4892, 6)]

theorem sourceEq66 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm66 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA66 + difference 0 1) (sourceB66 + difference 1 0) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA66 + difference 0 1) (sourceB66 + difference 1 0) sourceC66) = raw3856 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3856; decide +kernel
    rw [ha]
    exact (canonical3856 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA66 + difference 0 2) (sourceB66 + difference 2 0) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA66 + difference 0 2) (sourceB66 + difference 2 0) sourceC66) = raw3658 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3658; decide +kernel
    rw [ha]
    exact (canonical3658 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA66 + difference 0 3) (sourceB66 + difference 3 0) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA66 + difference 0 3) (sourceB66 + difference 3 0) sourceC66) = raw3857 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3857; decide +kernel
    rw [ha]
    exact (canonical3857 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA66 + difference 0 4) (sourceB66 + difference 4 0) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA66 + difference 0 4) (sourceB66 + difference 4 0) sourceC66) = raw3858 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3858; decide +kernel
    rw [ha]
    exact (canonical3858 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA66 + difference 0 5) (sourceB66 + difference 5 0) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA66 + difference 0 5) (sourceB66 + difference 5 0) sourceC66) = raw3859 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3859; decide +kernel
    rw [ha]
    exact (canonical3859 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA66 + difference 1 0) (sourceB66 + difference 0 1) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4482) := by
    have ha : (tripleCharges (sourceA66 + difference 1 0) (sourceB66 + difference 0 1) sourceC66) = raw3860 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3860; decide +kernel
    rw [ha]
    exact (canonical3860 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA66 + difference 1 2) (sourceB66 + difference 2 1) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA66 + difference 1 2) (sourceB66 + difference 2 1) sourceC66) = raw3663 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3663; decide +kernel
    rw [ha]
    exact (canonical3663 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA66 + difference 1 3) (sourceB66 + difference 3 1) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA66 + difference 1 3) (sourceB66 + difference 3 1) sourceC66) = raw3861 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3861; decide +kernel
    rw [ha]
    exact (canonical3861 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA66 + difference 1 4) (sourceB66 + difference 4 1) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA66 + difference 1 4) (sourceB66 + difference 4 1) sourceC66) = raw3862 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3862; decide +kernel
    rw [ha]
    exact (canonical3862 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA66 + difference 1 5) (sourceB66 + difference 5 1) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4482) := by
    have ha : (tripleCharges (sourceA66 + difference 1 5) (sourceB66 + difference 5 1) sourceC66) = raw3863 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3863; decide +kernel
    rw [ha]
    exact (canonical3863 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA66 + difference 2 0) (sourceB66 + difference 0 2) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA66 + difference 2 0) (sourceB66 + difference 0 2) sourceC66) = raw3864 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3864; decide +kernel
    rw [ha]
    exact (canonical3864 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA66 + difference 2 1) (sourceB66 + difference 1 2) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4822) := by
    have ha : (tripleCharges (sourceA66 + difference 2 1) (sourceB66 + difference 1 2) sourceC66) = raw3865 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3865; decide +kernel
    rw [ha]
    exact (canonical3865 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA66 + difference 2 3) (sourceB66 + difference 3 2) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA66 + difference 2 3) (sourceB66 + difference 3 2) sourceC66) = raw3866 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3866; decide +kernel
    rw [ha]
    exact (canonical3866 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA66 + difference 2 4) (sourceB66 + difference 4 2) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA66 + difference 2 4) (sourceB66 + difference 4 2) sourceC66) = raw3867 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3867; decide +kernel
    rw [ha]
    exact (canonical3867 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA66 + difference 2 5) (sourceB66 + difference 5 2) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA66 + difference 2 5) (sourceB66 + difference 5 2) sourceC66) = raw3868 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3868; decide +kernel
    rw [ha]
    exact (canonical3868 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA66 + difference 3 0) (sourceB66 + difference 0 3) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA66 + difference 3 0) (sourceB66 + difference 0 3) sourceC66) = raw3869 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3869; decide +kernel
    rw [ha]
    exact (canonical3869 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA66 + difference 3 1) (sourceB66 + difference 1 3) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4822) := by
    have ha : (tripleCharges (sourceA66 + difference 3 1) (sourceB66 + difference 1 3) sourceC66) = raw3870 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3870; decide +kernel
    rw [ha]
    exact (canonical3870 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA66 + difference 3 2) (sourceB66 + difference 2 3) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA66 + difference 3 2) (sourceB66 + difference 2 3) sourceC66) = raw3673 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3673; decide +kernel
    rw [ha]
    exact (canonical3673 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA66 + difference 3 4) (sourceB66 + difference 4 3) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA66 + difference 3 4) (sourceB66 + difference 4 3) sourceC66) = raw3871 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3871; decide +kernel
    rw [ha]
    exact (canonical3871 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA66 + difference 3 5) (sourceB66 + difference 5 3) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA66 + difference 3 5) (sourceB66 + difference 5 3) sourceC66) = raw3872 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3872; decide +kernel
    rw [ha]
    exact (canonical3872 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA66 + difference 4 0) (sourceB66 + difference 0 4) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA66 + difference 4 0) (sourceB66 + difference 0 4) sourceC66) = raw3665 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3665; decide +kernel
    rw [ha]
    exact (canonical3665 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA66 + difference 4 1) (sourceB66 + difference 1 4) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4822) := by
    have ha : (tripleCharges (sourceA66 + difference 4 1) (sourceB66 + difference 1 4) sourceC66) = raw3666 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3666; decide +kernel
    rw [ha]
    exact (canonical3666 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA66 + difference 4 2) (sourceB66 + difference 2 4) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA66 + difference 4 2) (sourceB66 + difference 2 4) sourceC66) = raw3873 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3873; decide +kernel
    rw [ha]
    exact (canonical3873 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA66 + difference 4 3) (sourceB66 + difference 3 4) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA66 + difference 4 3) (sourceB66 + difference 3 4) sourceC66) = raw3667 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3667; decide +kernel
    rw [ha]
    exact (canonical3667 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA66 + difference 4 5) (sourceB66 + difference 5 4) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA66 + difference 4 5) (sourceB66 + difference 5 4) sourceC66) = raw3669 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3669; decide +kernel
    rw [ha]
    exact (canonical3669 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA66 + difference 5 0) (sourceB66 + difference 0 5) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA66 + difference 5 0) (sourceB66 + difference 0 5) sourceC66) = raw3874 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3874; decide +kernel
    rw [ha]
    exact (canonical3874 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA66 + difference 5 1) (sourceB66 + difference 1 5) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA66 + difference 5 1) (sourceB66 + difference 1 5) sourceC66) = raw3875 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3875; decide +kernel
    rw [ha]
    exact (canonical3875 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA66 + difference 5 2) (sourceB66 + difference 2 5) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA66 + difference 5 2) (sourceB66 + difference 2 5) sourceC66) = raw3684 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3684; decide +kernel
    rw [ha]
    exact (canonical3684 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA66 + difference 5 3) (sourceB66 + difference 3 5) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA66 + difference 5 3) (sourceB66 + difference 3 5) sourceC66) = raw3876 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3876; decide +kernel
    rw [ha]
    exact (canonical3876 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA66 + difference 5 4) (sourceB66 + difference 4 5) sourceC66) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA66 + difference 5 4) (sourceB66 + difference 4 5) sourceC66) = raw3877 := by
      apply Matrix.ext; unfold tripleCharges sourceA66 sourceB66 sourceC66 difference raw3877; decide +kernel
    rw [ha]
    exact (canonical3877 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA66 sourceB66 sourceC66
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm66, Integer.Sparse.eval]
  linarith only [hs]

def sourceA67 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceB67 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC67 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm67 : Integer.Sparse Master := [(Sum.inr 1350, 1), (Sum.inr 1351, 3), (Sum.inr 1435, 1), (Sum.inr 1696, 1), (Sum.inr 1700, 1), (Sum.inr 1702, 3), (Sum.inr 2187, 1), (Sum.inr 2188, 3), (Sum.inr 2235, 3), (Sum.inr 2247, 3), (Sum.inr 2255, 6), (Sum.inr 2707, 1), (Sum.inr 2755, 3)]

theorem sourceEq67 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm67 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA67 + difference 0 1) (sourceB67 + difference 1 0) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA67 + difference 0 1) (sourceB67 + difference 1 0) sourceC67) = raw3878 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3878; decide +kernel
    rw [ha]
    exact (canonical3878 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA67 + difference 0 2) (sourceB67 + difference 2 0) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA67 + difference 0 2) (sourceB67 + difference 2 0) sourceC67) = raw3688 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3688; decide +kernel
    rw [ha]
    exact (canonical3688 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA67 + difference 0 3) (sourceB67 + difference 3 0) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA67 + difference 0 3) (sourceB67 + difference 3 0) sourceC67) = raw3879 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3879; decide +kernel
    rw [ha]
    exact (canonical3879 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA67 + difference 0 4) (sourceB67 + difference 4 0) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA67 + difference 0 4) (sourceB67 + difference 4 0) sourceC67) = raw3880 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3880; decide +kernel
    rw [ha]
    exact (canonical3880 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA67 + difference 0 5) (sourceB67 + difference 5 0) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1435) := by
    have ha : (tripleCharges (sourceA67 + difference 0 5) (sourceB67 + difference 5 0) sourceC67) = raw3881 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3881; decide +kernel
    rw [ha]
    exact (canonical3881 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA67 + difference 1 0) (sourceB67 + difference 0 1) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1696) := by
    have ha : (tripleCharges (sourceA67 + difference 1 0) (sourceB67 + difference 0 1) sourceC67) = raw3882 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3882; decide +kernel
    rw [ha]
    exact (canonical3882 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA67 + difference 1 2) (sourceB67 + difference 2 1) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA67 + difference 1 2) (sourceB67 + difference 2 1) sourceC67) = raw3693 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3693; decide +kernel
    rw [ha]
    exact (canonical3693 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA67 + difference 1 3) (sourceB67 + difference 3 1) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA67 + difference 1 3) (sourceB67 + difference 3 1) sourceC67) = raw3883 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3883; decide +kernel
    rw [ha]
    exact (canonical3883 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA67 + difference 1 4) (sourceB67 + difference 4 1) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA67 + difference 1 4) (sourceB67 + difference 4 1) sourceC67) = raw3884 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3884; decide +kernel
    rw [ha]
    exact (canonical3884 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA67 + difference 1 5) (sourceB67 + difference 5 1) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1350) := by
    have ha : (tripleCharges (sourceA67 + difference 1 5) (sourceB67 + difference 5 1) sourceC67) = raw3885 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3885; decide +kernel
    rw [ha]
    exact (canonical3885 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA67 + difference 2 0) (sourceB67 + difference 0 2) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1702) := by
    have ha : (tripleCharges (sourceA67 + difference 2 0) (sourceB67 + difference 0 2) sourceC67) = raw3886 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3886; decide +kernel
    rw [ha]
    exact (canonical3886 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA67 + difference 2 1) (sourceB67 + difference 1 2) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2188) := by
    have ha : (tripleCharges (sourceA67 + difference 2 1) (sourceB67 + difference 1 2) sourceC67) = raw3887 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3887; decide +kernel
    rw [ha]
    exact (canonical3887 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA67 + difference 2 3) (sourceB67 + difference 3 2) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA67 + difference 2 3) (sourceB67 + difference 3 2) sourceC67) = raw3888 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3888; decide +kernel
    rw [ha]
    exact (canonical3888 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA67 + difference 2 4) (sourceB67 + difference 4 2) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA67 + difference 2 4) (sourceB67 + difference 4 2) sourceC67) = raw3889 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3889; decide +kernel
    rw [ha]
    exact (canonical3889 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA67 + difference 2 5) (sourceB67 + difference 5 2) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1351) := by
    have ha : (tripleCharges (sourceA67 + difference 2 5) (sourceB67 + difference 5 2) sourceC67) = raw3890 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3890; decide +kernel
    rw [ha]
    exact (canonical3890 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA67 + difference 3 0) (sourceB67 + difference 0 3) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1702) := by
    have ha : (tripleCharges (sourceA67 + difference 3 0) (sourceB67 + difference 0 3) sourceC67) = raw3891 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3891; decide +kernel
    rw [ha]
    exact (canonical3891 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA67 + difference 3 1) (sourceB67 + difference 1 3) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2188) := by
    have ha : (tripleCharges (sourceA67 + difference 3 1) (sourceB67 + difference 1 3) sourceC67) = raw3892 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3892; decide +kernel
    rw [ha]
    exact (canonical3892 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA67 + difference 3 2) (sourceB67 + difference 2 3) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA67 + difference 3 2) (sourceB67 + difference 2 3) sourceC67) = raw3703 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3703; decide +kernel
    rw [ha]
    exact (canonical3703 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA67 + difference 3 4) (sourceB67 + difference 4 3) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA67 + difference 3 4) (sourceB67 + difference 4 3) sourceC67) = raw3893 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3893; decide +kernel
    rw [ha]
    exact (canonical3893 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA67 + difference 3 5) (sourceB67 + difference 5 3) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1351) := by
    have ha : (tripleCharges (sourceA67 + difference 3 5) (sourceB67 + difference 5 3) sourceC67) = raw3894 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3894; decide +kernel
    rw [ha]
    exact (canonical3894 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA67 + difference 4 0) (sourceB67 + difference 0 4) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1702) := by
    have ha : (tripleCharges (sourceA67 + difference 4 0) (sourceB67 + difference 0 4) sourceC67) = raw3695 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3695; decide +kernel
    rw [ha]
    exact (canonical3695 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA67 + difference 4 1) (sourceB67 + difference 1 4) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2188) := by
    have ha : (tripleCharges (sourceA67 + difference 4 1) (sourceB67 + difference 1 4) sourceC67) = raw3696 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3696; decide +kernel
    rw [ha]
    exact (canonical3696 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA67 + difference 4 2) (sourceB67 + difference 2 4) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA67 + difference 4 2) (sourceB67 + difference 2 4) sourceC67) = raw3895 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3895; decide +kernel
    rw [ha]
    exact (canonical3895 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA67 + difference 4 3) (sourceB67 + difference 3 4) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA67 + difference 4 3) (sourceB67 + difference 3 4) sourceC67) = raw3697 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3697; decide +kernel
    rw [ha]
    exact (canonical3697 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA67 + difference 4 5) (sourceB67 + difference 5 4) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1351) := by
    have ha : (tripleCharges (sourceA67 + difference 4 5) (sourceB67 + difference 5 4) sourceC67) = raw3699 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3699; decide +kernel
    rw [ha]
    exact (canonical3699 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA67 + difference 5 0) (sourceB67 + difference 0 5) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA67 + difference 5 0) (sourceB67 + difference 0 5) sourceC67) = raw3896 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3896; decide +kernel
    rw [ha]
    exact (canonical3896 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA67 + difference 5 1) (sourceB67 + difference 1 5) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA67 + difference 5 1) (sourceB67 + difference 1 5) sourceC67) = raw3897 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3897; decide +kernel
    rw [ha]
    exact (canonical3897 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA67 + difference 5 2) (sourceB67 + difference 2 5) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA67 + difference 5 2) (sourceB67 + difference 2 5) sourceC67) = raw3714 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3714; decide +kernel
    rw [ha]
    exact (canonical3714 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA67 + difference 5 3) (sourceB67 + difference 3 5) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA67 + difference 5 3) (sourceB67 + difference 3 5) sourceC67) = raw3898 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3898; decide +kernel
    rw [ha]
    exact (canonical3898 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA67 + difference 5 4) (sourceB67 + difference 4 5) sourceC67) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA67 + difference 5 4) (sourceB67 + difference 4 5) sourceC67) = raw3899 := by
      apply Matrix.ext; unfold tripleCharges sourceA67 sourceB67 sourceC67 difference raw3899; decide +kernel
    rw [ha]
    exact (canonical3899 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA67 sourceB67 sourceC67
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm67, Integer.Sparse.eval]
  linarith only [hs]

def sourceA68 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceB68 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC68 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm68 : Integer.Sparse Master := [(Sum.inr 1078, 1), (Sum.inr 2050, 1), (Sum.inr 2283, 1), (Sum.inr 2290, 3), (Sum.inr 4085, -1)]

theorem sourceEq68 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm68 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA68 + difference 0 0) (sourceB68 + difference 0 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA68 + difference 0 0) (sourceB68 + difference 0 0) sourceC68) = raw3900 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3900; decide +kernel
    rw [ha]
    exact (canonical3900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA68 + difference 0 1) (sourceB68 + difference 1 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA68 + difference 0 1) (sourceB68 + difference 1 0) sourceC68) = raw3901 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3901; decide +kernel
    rw [ha]
    exact (canonical3901 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA68 + difference 0 2) (sourceB68 + difference 2 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA68 + difference 0 2) (sourceB68 + difference 2 0) sourceC68) = raw3719 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3719; decide +kernel
    rw [ha]
    exact (canonical3719 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA68 + difference 0 3) (sourceB68 + difference 3 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA68 + difference 0 3) (sourceB68 + difference 3 0) sourceC68) = raw3902 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3902; decide +kernel
    rw [ha]
    exact (canonical3902 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA68 + difference 0 4) (sourceB68 + difference 4 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA68 + difference 0 4) (sourceB68 + difference 4 0) sourceC68) = raw3903 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3903; decide +kernel
    rw [ha]
    exact (canonical3903 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA68 + difference 0 5) (sourceB68 + difference 5 0) sourceC68) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1078) := by
    have ha : (tripleCharges (sourceA68 + difference 0 5) (sourceB68 + difference 5 0) sourceC68) = raw3904 := by
      apply Matrix.ext; unfold tripleCharges sourceA68 sourceB68 sourceC68 difference raw3904; decide +kernel
    rw [ha]
    exact (canonical3904 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA68 + sourceB68) sourceC68) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA68 + sourceB68) sourceC68) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA68 sourceB68 sourceC68 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA68 sourceB68 sourceC68
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm68, Integer.Sparse.eval]
  linarith only [hs]

def sourceA69 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceB69 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC69 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm69 : Integer.Sparse Master := [(Sum.inr 1065, 1), (Sum.inr 1066, 3), (Sum.inr 1078, 1), (Sum.inr 2283, 1), (Sum.inr 4085, -1)]

theorem sourceEq69 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm69 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA69 + difference 0 0) (sourceB69 + difference 0 0) sourceC69) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA69 + difference 0 0) (sourceB69 + difference 0 0) sourceC69) = raw3900 := by
      apply Matrix.ext; unfold tripleCharges sourceA69 sourceB69 sourceC69 difference raw3900; decide +kernel
    rw [ha]
    exact (canonical3900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA69 + difference 1 0) (sourceB69 + difference 0 1) sourceC69) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1065) := by
    have ha : (tripleCharges (sourceA69 + difference 1 0) (sourceB69 + difference 0 1) sourceC69) = raw3905 := by
      apply Matrix.ext; unfold tripleCharges sourceA69 sourceB69 sourceC69 difference raw3905; decide +kernel
    rw [ha]
    exact (canonical3905 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA69 + difference 2 0) (sourceB69 + difference 0 2) sourceC69) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA69 + difference 2 0) (sourceB69 + difference 0 2) sourceC69) = raw3906 := by
      apply Matrix.ext; unfold tripleCharges sourceA69 sourceB69 sourceC69 difference raw3906; decide +kernel
    rw [ha]
    exact (canonical3906 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA69 + difference 3 0) (sourceB69 + difference 0 3) sourceC69) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA69 + difference 3 0) (sourceB69 + difference 0 3) sourceC69) = raw3907 := by
      apply Matrix.ext; unfold tripleCharges sourceA69 sourceB69 sourceC69 difference raw3907; decide +kernel
    rw [ha]
    exact (canonical3907 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA69 + difference 4 0) (sourceB69 + difference 0 4) sourceC69) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA69 + difference 4 0) (sourceB69 + difference 0 4) sourceC69) = raw3723 := by
      apply Matrix.ext; unfold tripleCharges sourceA69 sourceB69 sourceC69 difference raw3723; decide +kernel
    rw [ha]
    exact (canonical3723 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA69 + difference 5 0) (sourceB69 + difference 0 5) sourceC69) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1078) := by
    have ha : (tripleCharges (sourceA69 + difference 5 0) (sourceB69 + difference 0 5) sourceC69) = raw3908 := by
      apply Matrix.ext; unfold tripleCharges sourceA69 sourceB69 sourceC69 difference raw3908; decide +kernel
    rw [ha]
    exact (canonical3908 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA69 + sourceB69) sourceC69) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA69 + sourceB69) sourceC69) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA69 sourceB69 sourceC69 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA69 sourceB69 sourceC69
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm69, Integer.Sparse.eval]
  linarith only [hs]

def sourceA70 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceB70 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC70 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm70 : Integer.Sparse Master := [(Sum.inr 1065, 2), (Sum.inr 2283, 4), (Sum.inr 4085, -1)]

theorem sourceEq70 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm70 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA70 + difference 1 0) (sourceB70 + difference 0 1) sourceC70) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1065) := by
    have ha : (tripleCharges (sourceA70 + difference 1 0) (sourceB70 + difference 0 1) sourceC70) = raw3905 := by
      apply Matrix.ext; unfold tripleCharges sourceA70 sourceB70 sourceC70 difference raw3905; decide +kernel
    rw [ha]
    exact (canonical3905 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA70 + difference 1 1) (sourceB70 + difference 1 1) sourceC70) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA70 + difference 1 1) (sourceB70 + difference 1 1) sourceC70) = raw3900 := by
      apply Matrix.ext; unfold tripleCharges sourceA70 sourceB70 sourceC70 difference raw3900; decide +kernel
    rw [ha]
    exact (canonical3900 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA70 + difference 1 2) (sourceB70 + difference 2 1) sourceC70) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA70 + difference 1 2) (sourceB70 + difference 2 1) sourceC70) = raw3729 := by
      apply Matrix.ext; unfold tripleCharges sourceA70 sourceB70 sourceC70 difference raw3729; decide +kernel
    rw [ha]
    exact (canonical3729 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA70 + difference 1 3) (sourceB70 + difference 3 1) sourceC70) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA70 + difference 1 3) (sourceB70 + difference 3 1) sourceC70) = raw3909 := by
      apply Matrix.ext; unfold tripleCharges sourceA70 sourceB70 sourceC70 difference raw3909; decide +kernel
    rw [ha]
    exact (canonical3909 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA70 + difference 1 4) (sourceB70 + difference 4 1) sourceC70) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA70 + difference 1 4) (sourceB70 + difference 4 1) sourceC70) = raw3910 := by
      apply Matrix.ext; unfold tripleCharges sourceA70 sourceB70 sourceC70 difference raw3910; decide +kernel
    rw [ha]
    exact (canonical3910 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA70 + difference 1 5) (sourceB70 + difference 5 1) sourceC70) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1065) := by
    have ha : (tripleCharges (sourceA70 + difference 1 5) (sourceB70 + difference 5 1) sourceC70) = raw3911 := by
      apply Matrix.ext; unfold tripleCharges sourceA70 sourceB70 sourceC70 difference raw3911; decide +kernel
    rw [ha]
    exact (canonical3911 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA70 + sourceB70) sourceC70) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA70 + sourceB70) sourceC70) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA70 sourceB70 sourceC70 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA70 sourceB70 sourceC70
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm70, Integer.Sparse.eval]
  linarith only [hs]

def sourceA71 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB71 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC71 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm71 : Integer.Sparse Master := [(Sum.inr 4410, 2), (Sum.inr 4413, 1), (Sum.inr 4429, 1), (Sum.inr 4476, 1), (Sum.inr 4564, 2), (Sum.inr 4573, 1), (Sum.inr 4609, 1), (Sum.inr 5008, 2), (Sum.inr 5022, 1), (Sum.inr 5052, 2), (Sum.inr 5062, 2), (Sum.inr 5087, 2), (Sum.inr 5109, 1), (Sum.inr 5139, 2), (Sum.inr 5266, 2), (Sum.inr 5267, 2), (Sum.inr 5275, 1), (Sum.inr 5276, 1), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5443, 1)]

theorem sourceEq71 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm71 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA71 + difference 0 1) (sourceB71 + difference 1 0) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA71 + difference 0 1) (sourceB71 + difference 1 0) sourceC71) = raw3912 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3912; decide +kernel
    rw [ha]
    exact (canonical3912 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA71 + difference 0 2) (sourceB71 + difference 2 0) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA71 + difference 0 2) (sourceB71 + difference 2 0) sourceC71) = raw3913 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3913; decide +kernel
    rw [ha]
    exact (canonical3913 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA71 + difference 0 3) (sourceB71 + difference 3 0) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA71 + difference 0 3) (sourceB71 + difference 3 0) sourceC71) = raw3914 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3914; decide +kernel
    rw [ha]
    exact (canonical3914 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA71 + difference 0 4) (sourceB71 + difference 4 0) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA71 + difference 0 4) (sourceB71 + difference 4 0) sourceC71) = raw3915 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3915; decide +kernel
    rw [ha]
    exact (canonical3915 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA71 + difference 0 5) (sourceB71 + difference 5 0) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA71 + difference 0 5) (sourceB71 + difference 5 0) sourceC71) = raw3916 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3916; decide +kernel
    rw [ha]
    exact (canonical3916 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA71 + difference 1 0) (sourceB71 + difference 0 1) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4573) := by
    have ha : (tripleCharges (sourceA71 + difference 1 0) (sourceB71 + difference 0 1) sourceC71) = raw3917 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3917; decide +kernel
    rw [ha]
    exact (canonical3917 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA71 + difference 1 2) (sourceB71 + difference 2 1) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5008) := by
    have ha : (tripleCharges (sourceA71 + difference 1 2) (sourceB71 + difference 2 1) sourceC71) = raw3918 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3918; decide +kernel
    rw [ha]
    exact (canonical3918 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA71 + difference 1 3) (sourceB71 + difference 3 1) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5008) := by
    have ha : (tripleCharges (sourceA71 + difference 1 3) (sourceB71 + difference 3 1) sourceC71) = raw3919 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3919; decide +kernel
    rw [ha]
    exact (canonical3919 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA71 + difference 1 4) (sourceB71 + difference 4 1) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5022) := by
    have ha : (tripleCharges (sourceA71 + difference 1 4) (sourceB71 + difference 4 1) sourceC71) = raw3920 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3920; decide +kernel
    rw [ha]
    exact (canonical3920 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA71 + difference 1 5) (sourceB71 + difference 5 1) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA71 + difference 1 5) (sourceB71 + difference 5 1) sourceC71) = raw3921 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3921; decide +kernel
    rw [ha]
    exact (canonical3921 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA71 + difference 2 0) (sourceB71 + difference 0 2) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4564) := by
    have ha : (tripleCharges (sourceA71 + difference 2 0) (sourceB71 + difference 0 2) sourceC71) = raw3922 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3922; decide +kernel
    rw [ha]
    exact (canonical3922 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA71 + difference 2 1) (sourceB71 + difference 1 2) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA71 + difference 2 1) (sourceB71 + difference 1 2) sourceC71) = raw3923 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3923; decide +kernel
    rw [ha]
    exact (canonical3923 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA71 + difference 2 3) (sourceB71 + difference 3 2) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5052) := by
    have ha : (tripleCharges (sourceA71 + difference 2 3) (sourceB71 + difference 3 2) sourceC71) = raw3924 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3924; decide +kernel
    rw [ha]
    exact (canonical3924 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA71 + difference 2 4) (sourceB71 + difference 4 2) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5062) := by
    have ha : (tripleCharges (sourceA71 + difference 2 4) (sourceB71 + difference 4 2) sourceC71) = raw3925 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3925; decide +kernel
    rw [ha]
    exact (canonical3925 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA71 + difference 2 5) (sourceB71 + difference 5 2) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA71 + difference 2 5) (sourceB71 + difference 5 2) sourceC71) = raw3926 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3926; decide +kernel
    rw [ha]
    exact (canonical3926 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA71 + difference 3 0) (sourceB71 + difference 0 3) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4564) := by
    have ha : (tripleCharges (sourceA71 + difference 3 0) (sourceB71 + difference 0 3) sourceC71) = raw3927 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3927; decide +kernel
    rw [ha]
    exact (canonical3927 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA71 + difference 3 1) (sourceB71 + difference 1 3) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA71 + difference 3 1) (sourceB71 + difference 1 3) sourceC71) = raw3928 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3928; decide +kernel
    rw [ha]
    exact (canonical3928 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA71 + difference 3 2) (sourceB71 + difference 2 3) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5052) := by
    have ha : (tripleCharges (sourceA71 + difference 3 2) (sourceB71 + difference 2 3) sourceC71) = raw3929 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3929; decide +kernel
    rw [ha]
    exact (canonical3929 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA71 + difference 3 4) (sourceB71 + difference 4 3) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5062) := by
    have ha : (tripleCharges (sourceA71 + difference 3 4) (sourceB71 + difference 4 3) sourceC71) = raw3930 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3930; decide +kernel
    rw [ha]
    exact (canonical3930 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA71 + difference 3 5) (sourceB71 + difference 5 3) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA71 + difference 3 5) (sourceB71 + difference 5 3) sourceC71) = raw3931 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3931; decide +kernel
    rw [ha]
    exact (canonical3931 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA71 + difference 4 0) (sourceB71 + difference 0 4) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA71 + difference 4 0) (sourceB71 + difference 0 4) sourceC71) = raw3932 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3932; decide +kernel
    rw [ha]
    exact (canonical3932 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA71 + difference 4 1) (sourceB71 + difference 1 4) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA71 + difference 4 1) (sourceB71 + difference 1 4) sourceC71) = raw3933 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3933; decide +kernel
    rw [ha]
    exact (canonical3933 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA71 + difference 4 2) (sourceB71 + difference 2 4) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA71 + difference 4 2) (sourceB71 + difference 2 4) sourceC71) = raw3934 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3934; decide +kernel
    rw [ha]
    exact (canonical3934 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA71 + difference 4 3) (sourceB71 + difference 3 4) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA71 + difference 4 3) (sourceB71 + difference 3 4) sourceC71) = raw3935 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3935; decide +kernel
    rw [ha]
    exact (canonical3935 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA71 + difference 4 5) (sourceB71 + difference 5 4) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA71 + difference 4 5) (sourceB71 + difference 5 4) sourceC71) = raw3936 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3936; decide +kernel
    rw [ha]
    exact (canonical3936 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA71 + difference 5 0) (sourceB71 + difference 0 5) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4413) := by
    have ha : (tripleCharges (sourceA71 + difference 5 0) (sourceB71 + difference 0 5) sourceC71) = raw3937 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3937; decide +kernel
    rw [ha]
    exact (canonical3937 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA71 + difference 5 1) (sourceB71 + difference 1 5) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA71 + difference 5 1) (sourceB71 + difference 1 5) sourceC71) = raw3938 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3938; decide +kernel
    rw [ha]
    exact (canonical3938 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA71 + difference 5 2) (sourceB71 + difference 2 5) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4410) := by
    have ha : (tripleCharges (sourceA71 + difference 5 2) (sourceB71 + difference 2 5) sourceC71) = raw3939 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3939; decide +kernel
    rw [ha]
    exact (canonical3939 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA71 + difference 5 3) (sourceB71 + difference 3 5) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4410) := by
    have ha : (tripleCharges (sourceA71 + difference 5 3) (sourceB71 + difference 3 5) sourceC71) = raw3940 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3940; decide +kernel
    rw [ha]
    exact (canonical3940 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA71 + difference 5 4) (sourceB71 + difference 4 5) sourceC71) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4429) := by
    have ha : (tripleCharges (sourceA71 + difference 5 4) (sourceB71 + difference 4 5) sourceC71) = raw3941 := by
      apply Matrix.ext; unfold tripleCharges sourceA71 sourceB71 sourceC71 difference raw3941; decide +kernel
    rw [ha]
    exact (canonical3941 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA71 sourceB71 sourceC71
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm71, Integer.Sparse.eval]
  linarith only [hs]

def sourceA72 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB72 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC72 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm72 : Integer.Sparse Master := [(Sum.inr 991, 2), (Sum.inr 994, 1), (Sum.inr 1010, 1), (Sum.inr 1059, 1), (Sum.inr 1181, 2), (Sum.inr 1191, 1), (Sum.inr 1264, 1), (Sum.inr 2393, 2), (Sum.inr 2408, 1), (Sum.inr 2454, 2), (Sum.inr 2465, 2), (Sum.inr 2495, 2), (Sum.inr 2618, 2), (Sum.inr 2640, 1), (Sum.inr 2732, 2), (Sum.inr 2744, 1), (Sum.inr 2776, 1), (Sum.inr 3039, 2), (Sum.inr 3055, 1), (Sum.inr 3110, 1), (Sum.inr 3889, 1)]

theorem sourceEq72 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm72 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA72 + difference 0 1) (sourceB72 + difference 1 0) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA72 + difference 0 1) (sourceB72 + difference 1 0) sourceC72) = raw3942 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3942; decide +kernel
    rw [ha]
    exact (canonical3942 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA72 + difference 0 2) (sourceB72 + difference 2 0) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA72 + difference 0 2) (sourceB72 + difference 2 0) sourceC72) = raw3943 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3943; decide +kernel
    rw [ha]
    exact (canonical3943 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA72 + difference 0 3) (sourceB72 + difference 3 0) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA72 + difference 0 3) (sourceB72 + difference 3 0) sourceC72) = raw3944 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3944; decide +kernel
    rw [ha]
    exact (canonical3944 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA72 + difference 0 4) (sourceB72 + difference 4 0) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA72 + difference 0 4) (sourceB72 + difference 4 0) sourceC72) = raw3945 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3945; decide +kernel
    rw [ha]
    exact (canonical3945 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA72 + difference 0 5) (sourceB72 + difference 5 0) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA72 + difference 0 5) (sourceB72 + difference 5 0) sourceC72) = raw3946 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3946; decide +kernel
    rw [ha]
    exact (canonical3946 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA72 + difference 1 0) (sourceB72 + difference 0 1) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1191) := by
    have ha : (tripleCharges (sourceA72 + difference 1 0) (sourceB72 + difference 0 1) sourceC72) = raw3947 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3947; decide +kernel
    rw [ha]
    exact (canonical3947 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA72 + difference 1 2) (sourceB72 + difference 2 1) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA72 + difference 1 2) (sourceB72 + difference 2 1) sourceC72) = raw3948 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3948; decide +kernel
    rw [ha]
    exact (canonical3948 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA72 + difference 1 3) (sourceB72 + difference 3 1) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA72 + difference 1 3) (sourceB72 + difference 3 1) sourceC72) = raw3949 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3949; decide +kernel
    rw [ha]
    exact (canonical3949 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA72 + difference 1 4) (sourceB72 + difference 4 1) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2408) := by
    have ha : (tripleCharges (sourceA72 + difference 1 4) (sourceB72 + difference 4 1) sourceC72) = raw3950 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3950; decide +kernel
    rw [ha]
    exact (canonical3950 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA72 + difference 1 5) (sourceB72 + difference 5 1) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA72 + difference 1 5) (sourceB72 + difference 5 1) sourceC72) = raw3951 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3951; decide +kernel
    rw [ha]
    exact (canonical3951 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA72 + difference 2 0) (sourceB72 + difference 0 2) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1181) := by
    have ha : (tripleCharges (sourceA72 + difference 2 0) (sourceB72 + difference 0 2) sourceC72) = raw3952 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3952; decide +kernel
    rw [ha]
    exact (canonical3952 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA72 + difference 2 1) (sourceB72 + difference 1 2) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA72 + difference 2 1) (sourceB72 + difference 1 2) sourceC72) = raw3953 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3953; decide +kernel
    rw [ha]
    exact (canonical3953 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA72 + difference 2 3) (sourceB72 + difference 3 2) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2454) := by
    have ha : (tripleCharges (sourceA72 + difference 2 3) (sourceB72 + difference 3 2) sourceC72) = raw3954 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3954; decide +kernel
    rw [ha]
    exact (canonical3954 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA72 + difference 2 4) (sourceB72 + difference 4 2) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA72 + difference 2 4) (sourceB72 + difference 4 2) sourceC72) = raw3955 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3955; decide +kernel
    rw [ha]
    exact (canonical3955 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA72 + difference 2 5) (sourceB72 + difference 5 2) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA72 + difference 2 5) (sourceB72 + difference 5 2) sourceC72) = raw3956 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3956; decide +kernel
    rw [ha]
    exact (canonical3956 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA72 + difference 3 0) (sourceB72 + difference 0 3) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1181) := by
    have ha : (tripleCharges (sourceA72 + difference 3 0) (sourceB72 + difference 0 3) sourceC72) = raw3957 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3957; decide +kernel
    rw [ha]
    exact (canonical3957 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA72 + difference 3 1) (sourceB72 + difference 1 3) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA72 + difference 3 1) (sourceB72 + difference 1 3) sourceC72) = raw3958 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3958; decide +kernel
    rw [ha]
    exact (canonical3958 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA72 + difference 3 2) (sourceB72 + difference 2 3) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2454) := by
    have ha : (tripleCharges (sourceA72 + difference 3 2) (sourceB72 + difference 2 3) sourceC72) = raw3959 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3959; decide +kernel
    rw [ha]
    exact (canonical3959 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA72 + difference 3 4) (sourceB72 + difference 4 3) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA72 + difference 3 4) (sourceB72 + difference 4 3) sourceC72) = raw3960 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3960; decide +kernel
    rw [ha]
    exact (canonical3960 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA72 + difference 3 5) (sourceB72 + difference 5 3) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA72 + difference 3 5) (sourceB72 + difference 5 3) sourceC72) = raw3961 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3961; decide +kernel
    rw [ha]
    exact (canonical3961 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA72 + difference 4 0) (sourceB72 + difference 0 4) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA72 + difference 4 0) (sourceB72 + difference 0 4) sourceC72) = raw3962 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3962; decide +kernel
    rw [ha]
    exact (canonical3962 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA72 + difference 4 1) (sourceB72 + difference 1 4) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2640) := by
    have ha : (tripleCharges (sourceA72 + difference 4 1) (sourceB72 + difference 1 4) sourceC72) = raw3963 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3963; decide +kernel
    rw [ha]
    exact (canonical3963 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA72 + difference 4 2) (sourceB72 + difference 2 4) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA72 + difference 4 2) (sourceB72 + difference 2 4) sourceC72) = raw3964 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3964; decide +kernel
    rw [ha]
    exact (canonical3964 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA72 + difference 4 3) (sourceB72 + difference 3 4) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA72 + difference 4 3) (sourceB72 + difference 3 4) sourceC72) = raw3965 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3965; decide +kernel
    rw [ha]
    exact (canonical3965 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA72 + difference 4 5) (sourceB72 + difference 5 4) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA72 + difference 4 5) (sourceB72 + difference 5 4) sourceC72) = raw3966 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3966; decide +kernel
    rw [ha]
    exact (canonical3966 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA72 + difference 5 0) (sourceB72 + difference 0 5) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 994) := by
    have ha : (tripleCharges (sourceA72 + difference 5 0) (sourceB72 + difference 0 5) sourceC72) = raw3967 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3967; decide +kernel
    rw [ha]
    exact (canonical3967 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA72 + difference 5 1) (sourceB72 + difference 1 5) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA72 + difference 5 1) (sourceB72 + difference 1 5) sourceC72) = raw3968 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3968; decide +kernel
    rw [ha]
    exact (canonical3968 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA72 + difference 5 2) (sourceB72 + difference 2 5) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 991) := by
    have ha : (tripleCharges (sourceA72 + difference 5 2) (sourceB72 + difference 2 5) sourceC72) = raw3969 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3969; decide +kernel
    rw [ha]
    exact (canonical3969 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA72 + difference 5 3) (sourceB72 + difference 3 5) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 991) := by
    have ha : (tripleCharges (sourceA72 + difference 5 3) (sourceB72 + difference 3 5) sourceC72) = raw3970 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3970; decide +kernel
    rw [ha]
    exact (canonical3970 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA72 + difference 5 4) (sourceB72 + difference 4 5) sourceC72) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA72 + difference 5 4) (sourceB72 + difference 4 5) sourceC72) = raw3971 := by
      apply Matrix.ext; unfold tripleCharges sourceA72 sourceB72 sourceC72 difference raw3971; decide +kernel
    rw [ha]
    exact (canonical3971 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA72 sourceB72 sourceC72
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm72, Integer.Sparse.eval]
  linarith only [hs]

def sourceA73 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB73 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC73 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm73 : Integer.Sparse Master := [(Sum.inr 1624, 2), (Sum.inr 1628, 1), (Sum.inr 1629, 1), (Sum.inr 1729, 1), (Sum.inr 2837, 2), (Sum.inr 2842, 1), (Sum.inr 3052, 1), (Sum.inr 3242, 2), (Sum.inr 3247, 1), (Sum.inr 3302, 1), (Sum.inr 3358, 2), (Sum.inr 3437, 2), (Sum.inr 3472, 2), (Sum.inr 3486, 1), (Sum.inr 3523, 2), (Sum.inr 3535, 2), (Sum.inr 3541, 2), (Sum.inr 3548, 1), (Sum.inr 3584, 1), (Sum.inr 3626, 1), (Sum.inr 3862, 1)]

theorem sourceEq73 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm73 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA73 + difference 0 1) (sourceB73 + difference 1 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA73 + difference 0 1) (sourceB73 + difference 1 0) sourceC73) = raw3972 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3972; decide +kernel
    rw [ha]
    exact (canonical3972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA73 + difference 0 2) (sourceB73 + difference 2 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA73 + difference 0 2) (sourceB73 + difference 2 0) sourceC73) = raw3973 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3973; decide +kernel
    rw [ha]
    exact (canonical3973 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA73 + difference 0 3) (sourceB73 + difference 3 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA73 + difference 0 3) (sourceB73 + difference 3 0) sourceC73) = raw3974 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3974; decide +kernel
    rw [ha]
    exact (canonical3974 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA73 + difference 0 4) (sourceB73 + difference 4 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA73 + difference 0 4) (sourceB73 + difference 4 0) sourceC73) = raw3975 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3975; decide +kernel
    rw [ha]
    exact (canonical3975 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA73 + difference 0 5) (sourceB73 + difference 5 0) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA73 + difference 0 5) (sourceB73 + difference 5 0) sourceC73) = raw3976 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3976; decide +kernel
    rw [ha]
    exact (canonical3976 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA73 + difference 1 0) (sourceB73 + difference 0 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3247) := by
    have ha : (tripleCharges (sourceA73 + difference 1 0) (sourceB73 + difference 0 1) sourceC73) = raw3977 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3977; decide +kernel
    rw [ha]
    exact (canonical3977 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA73 + difference 1 2) (sourceB73 + difference 2 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA73 + difference 1 2) (sourceB73 + difference 2 1) sourceC73) = raw3978 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3978; decide +kernel
    rw [ha]
    exact (canonical3978 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA73 + difference 1 3) (sourceB73 + difference 3 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA73 + difference 1 3) (sourceB73 + difference 3 1) sourceC73) = raw3979 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3979; decide +kernel
    rw [ha]
    exact (canonical3979 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA73 + difference 1 4) (sourceB73 + difference 4 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2842) := by
    have ha : (tripleCharges (sourceA73 + difference 1 4) (sourceB73 + difference 4 1) sourceC73) = raw3980 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3980; decide +kernel
    rw [ha]
    exact (canonical3980 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA73 + difference 1 5) (sourceB73 + difference 5 1) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA73 + difference 1 5) (sourceB73 + difference 5 1) sourceC73) = raw3981 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3981; decide +kernel
    rw [ha]
    exact (canonical3981 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA73 + difference 2 0) (sourceB73 + difference 0 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA73 + difference 2 0) (sourceB73 + difference 0 2) sourceC73) = raw3982 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3982; decide +kernel
    rw [ha]
    exact (canonical3982 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA73 + difference 2 1) (sourceB73 + difference 1 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA73 + difference 2 1) (sourceB73 + difference 1 2) sourceC73) = raw3983 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3983; decide +kernel
    rw [ha]
    exact (canonical3983 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA73 + difference 2 3) (sourceB73 + difference 3 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA73 + difference 2 3) (sourceB73 + difference 3 2) sourceC73) = raw3984 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3984; decide +kernel
    rw [ha]
    exact (canonical3984 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA73 + difference 2 4) (sourceB73 + difference 4 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA73 + difference 2 4) (sourceB73 + difference 4 2) sourceC73) = raw3985 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3985; decide +kernel
    rw [ha]
    exact (canonical3985 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA73 + difference 2 5) (sourceB73 + difference 5 2) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA73 + difference 2 5) (sourceB73 + difference 5 2) sourceC73) = raw3986 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3986; decide +kernel
    rw [ha]
    exact (canonical3986 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA73 + difference 3 0) (sourceB73 + difference 0 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA73 + difference 3 0) (sourceB73 + difference 0 3) sourceC73) = raw3987 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3987; decide +kernel
    rw [ha]
    exact (canonical3987 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA73 + difference 3 1) (sourceB73 + difference 1 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA73 + difference 3 1) (sourceB73 + difference 1 3) sourceC73) = raw3988 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3988; decide +kernel
    rw [ha]
    exact (canonical3988 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA73 + difference 3 2) (sourceB73 + difference 2 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA73 + difference 3 2) (sourceB73 + difference 2 3) sourceC73) = raw3989 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3989; decide +kernel
    rw [ha]
    exact (canonical3989 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA73 + difference 3 4) (sourceB73 + difference 4 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA73 + difference 3 4) (sourceB73 + difference 4 3) sourceC73) = raw3990 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3990; decide +kernel
    rw [ha]
    exact (canonical3990 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA73 + difference 3 5) (sourceB73 + difference 5 3) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA73 + difference 3 5) (sourceB73 + difference 5 3) sourceC73) = raw3991 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3991; decide +kernel
    rw [ha]
    exact (canonical3991 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA73 + difference 4 0) (sourceB73 + difference 0 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA73 + difference 4 0) (sourceB73 + difference 0 4) sourceC73) = raw3992 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3992; decide +kernel
    rw [ha]
    exact (canonical3992 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA73 + difference 4 1) (sourceB73 + difference 1 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA73 + difference 4 1) (sourceB73 + difference 1 4) sourceC73) = raw3993 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3993; decide +kernel
    rw [ha]
    exact (canonical3993 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA73 + difference 4 2) (sourceB73 + difference 2 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA73 + difference 4 2) (sourceB73 + difference 2 4) sourceC73) = raw3994 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3994; decide +kernel
    rw [ha]
    exact (canonical3994 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA73 + difference 4 3) (sourceB73 + difference 3 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA73 + difference 4 3) (sourceB73 + difference 3 4) sourceC73) = raw3995 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3995; decide +kernel
    rw [ha]
    exact (canonical3995 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA73 + difference 4 5) (sourceB73 + difference 5 4) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA73 + difference 4 5) (sourceB73 + difference 5 4) sourceC73) = raw3996 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3996; decide +kernel
    rw [ha]
    exact (canonical3996 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA73 + difference 5 0) (sourceB73 + difference 0 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA73 + difference 5 0) (sourceB73 + difference 0 5) sourceC73) = raw3997 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3997; decide +kernel
    rw [ha]
    exact (canonical3997 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA73 + difference 5 1) (sourceB73 + difference 1 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA73 + difference 5 1) (sourceB73 + difference 1 5) sourceC73) = raw3998 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3998; decide +kernel
    rw [ha]
    exact (canonical3998 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA73 + difference 5 2) (sourceB73 + difference 2 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA73 + difference 5 2) (sourceB73 + difference 2 5) sourceC73) = raw3999 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw3999; decide +kernel
    rw [ha]
    exact (canonical3999 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA73 + difference 5 3) (sourceB73 + difference 3 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA73 + difference 5 3) (sourceB73 + difference 3 5) sourceC73) = raw4000 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw4000; decide +kernel
    rw [ha]
    exact (canonical4000 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA73 + difference 5 4) (sourceB73 + difference 4 5) sourceC73) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA73 + difference 5 4) (sourceB73 + difference 4 5) sourceC73) = raw4001 := by
      apply Matrix.ext; unfold tripleCharges sourceA73 sourceB73 sourceC73 difference raw4001; decide +kernel
    rw [ha]
    exact (canonical4001 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA73 sourceB73 sourceC73
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm73, Integer.Sparse.eval]
  linarith only [hs]

def sourceA74 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB74 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC74 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm74 : Integer.Sparse Master := [(Sum.inr 2734, 1), (Sum.inr 2777, 1), (Sum.inr 3038, 2), (Sum.inr 3054, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

theorem sourceEq74 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm74 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA74 + difference 0 0) (sourceB74 + difference 0 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA74 + difference 0 0) (sourceB74 + difference 0 0) sourceC74) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA74 + difference 0 1) (sourceB74 + difference 1 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA74 + difference 0 1) (sourceB74 + difference 1 0) sourceC74) = raw4003 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4003; decide +kernel
    rw [ha]
    exact (canonical4003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA74 + difference 0 2) (sourceB74 + difference 2 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA74 + difference 0 2) (sourceB74 + difference 2 0) sourceC74) = raw4004 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4004; decide +kernel
    rw [ha]
    exact (canonical4004 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA74 + difference 0 3) (sourceB74 + difference 3 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA74 + difference 0 3) (sourceB74 + difference 3 0) sourceC74) = raw4005 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4005; decide +kernel
    rw [ha]
    exact (canonical4005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA74 + difference 0 4) (sourceB74 + difference 4 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA74 + difference 0 4) (sourceB74 + difference 4 0) sourceC74) = raw4006 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4006; decide +kernel
    rw [ha]
    exact (canonical4006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA74 + difference 0 5) (sourceB74 + difference 5 0) sourceC74) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA74 + difference 0 5) (sourceB74 + difference 5 0) sourceC74) = raw4007 := by
      apply Matrix.ext; unfold tripleCharges sourceA74 sourceB74 sourceC74 difference raw4007; decide +kernel
    rw [ha]
    exact (canonical4007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA74 + sourceB74) sourceC74) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA74 + sourceB74) sourceC74) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA74 sourceB74 sourceC74 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA74 sourceB74 sourceC74
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm74, Integer.Sparse.eval]
  linarith only [hs]

def sourceA75 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB75 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC75 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm75 : Integer.Sparse Master := [(Sum.inr 1224, 2), (Sum.inr 1227, 1), (Sum.inr 1243, 1), (Sum.inr 1279, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

theorem sourceEq75 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm75 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA75 + difference 0 0) (sourceB75 + difference 0 0) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA75 + difference 0 0) (sourceB75 + difference 0 0) sourceC75) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA75 + difference 1 0) (sourceB75 + difference 0 1) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1279) := by
    have ha : (tripleCharges (sourceA75 + difference 1 0) (sourceB75 + difference 0 1) sourceC75) = raw4009 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4009; decide +kernel
    rw [ha]
    exact (canonical4009 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA75 + difference 2 0) (sourceB75 + difference 0 2) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1224) := by
    have ha : (tripleCharges (sourceA75 + difference 2 0) (sourceB75 + difference 0 2) sourceC75) = raw4010 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4010; decide +kernel
    rw [ha]
    exact (canonical4010 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA75 + difference 3 0) (sourceB75 + difference 0 3) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1224) := by
    have ha : (tripleCharges (sourceA75 + difference 3 0) (sourceB75 + difference 0 3) sourceC75) = raw4011 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4011; decide +kernel
    rw [ha]
    exact (canonical4011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA75 + difference 4 0) (sourceB75 + difference 0 4) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA75 + difference 4 0) (sourceB75 + difference 0 4) sourceC75) = raw4012 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4012; decide +kernel
    rw [ha]
    exact (canonical4012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA75 + difference 5 0) (sourceB75 + difference 0 5) sourceC75) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1227) := by
    have ha : (tripleCharges (sourceA75 + difference 5 0) (sourceB75 + difference 0 5) sourceC75) = raw4013 := by
      apply Matrix.ext; unfold tripleCharges sourceA75 sourceB75 sourceC75 difference raw4013; decide +kernel
    rw [ha]
    exact (canonical4013 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA75 + sourceB75) sourceC75) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA75 + sourceB75) sourceC75) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA75 sourceB75 sourceC75 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA75 sourceB75 sourceC75
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm75, Integer.Sparse.eval]
  linarith only [hs]

def sourceA76 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB76 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC76 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm76 : Integer.Sparse Master := [(Sum.inr 1279, 1), (Sum.inr 2579, 2), (Sum.inr 2651, 1), (Sum.inr 2734, 1), (Sum.inr 2774, 1), (Sum.inr 4092, -1)]

theorem sourceEq76 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm76 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA76 + difference 1 0) (sourceB76 + difference 0 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1279) := by
    have ha : (tripleCharges (sourceA76 + difference 1 0) (sourceB76 + difference 0 1) sourceC76) = raw4009 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4009; decide +kernel
    rw [ha]
    exact (canonical4009 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA76 + difference 1 1) (sourceB76 + difference 1 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA76 + difference 1 1) (sourceB76 + difference 1 1) sourceC76) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA76 + difference 1 2) (sourceB76 + difference 2 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2579) := by
    have ha : (tripleCharges (sourceA76 + difference 1 2) (sourceB76 + difference 2 1) sourceC76) = raw4014 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4014; decide +kernel
    rw [ha]
    exact (canonical4014 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA76 + difference 1 3) (sourceB76 + difference 3 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2579) := by
    have ha : (tripleCharges (sourceA76 + difference 1 3) (sourceB76 + difference 3 1) sourceC76) = raw4015 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4015; decide +kernel
    rw [ha]
    exact (canonical4015 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA76 + difference 1 4) (sourceB76 + difference 4 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2651) := by
    have ha : (tripleCharges (sourceA76 + difference 1 4) (sourceB76 + difference 4 1) sourceC76) = raw4016 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4016; decide +kernel
    rw [ha]
    exact (canonical4016 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA76 + difference 1 5) (sourceB76 + difference 5 1) sourceC76) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA76 + difference 1 5) (sourceB76 + difference 5 1) sourceC76) = raw4017 := by
      apply Matrix.ext; unfold tripleCharges sourceA76 sourceB76 sourceC76 difference raw4017; decide +kernel
    rw [ha]
    exact (canonical4017 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA76 + sourceB76) sourceC76) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA76 + sourceB76) sourceC76) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA76 sourceB76 sourceC76 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA76 sourceB76 sourceC76
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm76, Integer.Sparse.eval]
  linarith only [hs]

def sourceA77 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB77 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC77 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm77 : Integer.Sparse Master := [(Sum.inr 1372, 1), (Sum.inr 2495, 2), (Sum.inr 2519, 1), (Sum.inr 2734, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

theorem sourceEq77 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm77 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA77 + difference 0 1) (sourceB77 + difference 1 0) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA77 + difference 0 1) (sourceB77 + difference 1 0) sourceC77) = raw4003 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4003; decide +kernel
    rw [ha]
    exact (canonical4003 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA77 + difference 1 1) (sourceB77 + difference 1 1) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA77 + difference 1 1) (sourceB77 + difference 1 1) sourceC77) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA77 + difference 2 1) (sourceB77 + difference 1 2) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA77 + difference 2 1) (sourceB77 + difference 1 2) sourceC77) = raw4018 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4018; decide +kernel
    rw [ha]
    exact (canonical4018 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA77 + difference 3 1) (sourceB77 + difference 1 3) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA77 + difference 3 1) (sourceB77 + difference 1 3) sourceC77) = raw4019 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4019; decide +kernel
    rw [ha]
    exact (canonical4019 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA77 + difference 4 1) (sourceB77 + difference 1 4) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA77 + difference 4 1) (sourceB77 + difference 1 4) sourceC77) = raw4020 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4020; decide +kernel
    rw [ha]
    exact (canonical4020 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA77 + difference 5 1) (sourceB77 + difference 1 5) sourceC77) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA77 + difference 5 1) (sourceB77 + difference 1 5) sourceC77) = raw4021 := by
      apply Matrix.ext; unfold tripleCharges sourceA77 sourceB77 sourceC77 difference raw4021; decide +kernel
    rw [ha]
    exact (canonical4021 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA77 + sourceB77) sourceC77) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA77 + sourceB77) sourceC77) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA77 sourceB77 sourceC77 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA77 sourceB77 sourceC77
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm77, Integer.Sparse.eval]
  linarith only [hs]

def sourceA78 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB78 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC78 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm78 : Integer.Sparse Master := [(Sum.inr 1224, 1), (Sum.inr 2495, 1), (Sum.inr 2547, 1), (Sum.inr 2647, 1), (Sum.inr 2731, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

theorem sourceEq78 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm78 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA78 + difference 2 0) (sourceB78 + difference 0 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1224) := by
    have ha : (tripleCharges (sourceA78 + difference 2 0) (sourceB78 + difference 0 2) sourceC78) = raw4010 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4010; decide +kernel
    rw [ha]
    exact (canonical4010 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA78 + difference 2 1) (sourceB78 + difference 1 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA78 + difference 2 1) (sourceB78 + difference 1 2) sourceC78) = raw4018 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4018; decide +kernel
    rw [ha]
    exact (canonical4018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA78 + difference 2 2) (sourceB78 + difference 2 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA78 + difference 2 2) (sourceB78 + difference 2 2) sourceC78) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA78 + difference 2 3) (sourceB78 + difference 3 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2547) := by
    have ha : (tripleCharges (sourceA78 + difference 2 3) (sourceB78 + difference 3 2) sourceC78) = raw4022 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4022; decide +kernel
    rw [ha]
    exact (canonical4022 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA78 + difference 2 4) (sourceB78 + difference 4 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA78 + difference 2 4) (sourceB78 + difference 4 2) sourceC78) = raw4023 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4023; decide +kernel
    rw [ha]
    exact (canonical4023 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA78 + difference 2 5) (sourceB78 + difference 5 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA78 + difference 2 5) (sourceB78 + difference 5 2) sourceC78) = raw4024 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4024; decide +kernel
    rw [ha]
    exact (canonical4024 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA78 + sourceB78) sourceC78) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA78 + sourceB78) sourceC78) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA78 sourceB78 sourceC78 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA78 sourceB78 sourceC78
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm78, Integer.Sparse.eval]
  linarith only [hs]

def sourceA79 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB79 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC79 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm79 : Integer.Sparse Master := [(Sum.inr 1359, 1), (Sum.inr 2547, 1), (Sum.inr 2558, 1), (Sum.inr 2579, 1), (Sum.inr 2734, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

theorem sourceEq79 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm79 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA79 + difference 0 2) (sourceB79 + difference 2 0) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA79 + difference 0 2) (sourceB79 + difference 2 0) sourceC79) = raw4004 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4004; decide +kernel
    rw [ha]
    exact (canonical4004 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA79 + difference 1 2) (sourceB79 + difference 2 1) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2579) := by
    have ha : (tripleCharges (sourceA79 + difference 1 2) (sourceB79 + difference 2 1) sourceC79) = raw4014 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4014; decide +kernel
    rw [ha]
    exact (canonical4014 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA79 + difference 2 2) (sourceB79 + difference 2 2) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA79 + difference 2 2) (sourceB79 + difference 2 2) sourceC79) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA79 + difference 3 2) (sourceB79 + difference 2 3) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2547) := by
    have ha : (tripleCharges (sourceA79 + difference 3 2) (sourceB79 + difference 2 3) sourceC79) = raw4025 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4025; decide +kernel
    rw [ha]
    exact (canonical4025 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA79 + difference 4 2) (sourceB79 + difference 2 4) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA79 + difference 4 2) (sourceB79 + difference 2 4) sourceC79) = raw4026 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4026; decide +kernel
    rw [ha]
    exact (canonical4026 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA79 + difference 5 2) (sourceB79 + difference 2 5) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA79 + difference 5 2) (sourceB79 + difference 2 5) sourceC79) = raw4027 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4027; decide +kernel
    rw [ha]
    exact (canonical4027 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA79 + sourceB79) sourceC79) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA79 + sourceB79) sourceC79) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA79 sourceB79 sourceC79 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA79 sourceB79 sourceC79
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm79, Integer.Sparse.eval]
  linarith only [hs]

def sourceA80 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB80 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC80 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm80 : Integer.Sparse Master := [(Sum.inr 1243, 1), (Sum.inr 2519, 1), (Sum.inr 2558, 2), (Sum.inr 2734, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

theorem sourceEq80 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm80 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA80 + difference 4 0) (sourceB80 + difference 0 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA80 + difference 4 0) (sourceB80 + difference 0 4) sourceC80) = raw4012 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4012; decide +kernel
    rw [ha]
    exact (canonical4012 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA80 + difference 4 1) (sourceB80 + difference 1 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA80 + difference 4 1) (sourceB80 + difference 1 4) sourceC80) = raw4020 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4020; decide +kernel
    rw [ha]
    exact (canonical4020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA80 + difference 4 2) (sourceB80 + difference 2 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA80 + difference 4 2) (sourceB80 + difference 2 4) sourceC80) = raw4026 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4026; decide +kernel
    rw [ha]
    exact (canonical4026 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA80 + difference 4 3) (sourceB80 + difference 3 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA80 + difference 4 3) (sourceB80 + difference 3 4) sourceC80) = raw4028 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4028; decide +kernel
    rw [ha]
    exact (canonical4028 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA80 + difference 4 4) (sourceB80 + difference 4 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA80 + difference 4 4) (sourceB80 + difference 4 4) sourceC80) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA80 + difference 4 5) (sourceB80 + difference 5 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA80 + difference 4 5) (sourceB80 + difference 5 4) sourceC80) = raw4029 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4029; decide +kernel
    rw [ha]
    exact (canonical4029 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA80 + sourceB80) sourceC80) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA80 + sourceB80) sourceC80) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA80 sourceB80 sourceC80 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA80 sourceB80 sourceC80
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm80, Integer.Sparse.eval]
  linarith only [hs]

def sourceA81 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB81 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC81 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm81 : Integer.Sparse Master := [(Sum.inr 1424, 1), (Sum.inr 2647, 2), (Sum.inr 2651, 1), (Sum.inr 2734, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem sourceEq81 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm81 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA81 + difference 0 4) (sourceB81 + difference 4 0) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA81 + difference 0 4) (sourceB81 + difference 4 0) sourceC81) = raw4006 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4006; decide +kernel
    rw [ha]
    exact (canonical4006 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA81 + difference 1 4) (sourceB81 + difference 4 1) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2651) := by
    have ha : (tripleCharges (sourceA81 + difference 1 4) (sourceB81 + difference 4 1) sourceC81) = raw4016 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4016; decide +kernel
    rw [ha]
    exact (canonical4016 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA81 + difference 2 4) (sourceB81 + difference 4 2) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA81 + difference 2 4) (sourceB81 + difference 4 2) sourceC81) = raw4023 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4023; decide +kernel
    rw [ha]
    exact (canonical4023 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA81 + difference 3 4) (sourceB81 + difference 4 3) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA81 + difference 3 4) (sourceB81 + difference 4 3) sourceC81) = raw4030 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4030; decide +kernel
    rw [ha]
    exact (canonical4030 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA81 + difference 4 4) (sourceB81 + difference 4 4) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA81 + difference 4 4) (sourceB81 + difference 4 4) sourceC81) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA81 + difference 5 4) (sourceB81 + difference 4 5) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1424) := by
    have ha : (tripleCharges (sourceA81 + difference 5 4) (sourceB81 + difference 4 5) sourceC81) = raw4031 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4031; decide +kernel
    rw [ha]
    exact (canonical4031 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA81 + sourceB81) sourceC81) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA81 + sourceB81) sourceC81) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA81 sourceB81 sourceC81 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA81 sourceB81 sourceC81
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm81, Integer.Sparse.eval]
  linarith only [hs]

def sourceA82 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB82 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC82 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm82 : Integer.Sparse Master := [(Sum.inr 1227, 1), (Sum.inr 1359, 2), (Sum.inr 1372, 1), (Sum.inr 1424, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

theorem sourceEq82 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm82 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA82 + difference 5 0) (sourceB82 + difference 0 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1227) := by
    have ha : (tripleCharges (sourceA82 + difference 5 0) (sourceB82 + difference 0 5) sourceC82) = raw4013 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4013; decide +kernel
    rw [ha]
    exact (canonical4013 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA82 + difference 5 1) (sourceB82 + difference 1 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA82 + difference 5 1) (sourceB82 + difference 1 5) sourceC82) = raw4021 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4021; decide +kernel
    rw [ha]
    exact (canonical4021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA82 + difference 5 2) (sourceB82 + difference 2 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA82 + difference 5 2) (sourceB82 + difference 2 5) sourceC82) = raw4027 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4027; decide +kernel
    rw [ha]
    exact (canonical4027 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA82 + difference 5 3) (sourceB82 + difference 3 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA82 + difference 5 3) (sourceB82 + difference 3 5) sourceC82) = raw4032 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4032; decide +kernel
    rw [ha]
    exact (canonical4032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA82 + difference 5 4) (sourceB82 + difference 4 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1424) := by
    have ha : (tripleCharges (sourceA82 + difference 5 4) (sourceB82 + difference 4 5) sourceC82) = raw4031 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4031; decide +kernel
    rw [ha]
    exact (canonical4031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA82 + difference 5 5) (sourceB82 + difference 5 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA82 + difference 5 5) (sourceB82 + difference 5 5) sourceC82) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA82 + sourceB82) sourceC82) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA82 + sourceB82) sourceC82) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA82 sourceB82 sourceC82 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA82 sourceB82 sourceC82
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm82, Integer.Sparse.eval]
  linarith only [hs]

def sourceA83 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB83 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC83 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm83 : Integer.Sparse Master := [(Sum.inr 4836, 4), (Sum.inr 4844, 2), (Sum.inr 4845, 2), (Sum.inr 4882, 2), (Sum.inr 4883, 1), (Sum.inr 4899, 2), (Sum.inr 5222, 4), (Sum.inr 5225, 2), (Sum.inr 5235, 2), (Sum.inr 5240, 2), (Sum.inr 5252, 2), (Sum.inr 5261, 2), (Sum.inr 5268, 2), (Sum.inr 5296, 1)]

theorem sourceEq83 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm83 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA83 + difference 0 1) (sourceB83 + difference 1 0) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5235) := by
    have ha : (tripleCharges (sourceA83 + difference 0 1) (sourceB83 + difference 1 0) sourceC83) = raw4033 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4033; decide +kernel
    rw [ha]
    exact (canonical4033 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA83 + difference 0 2) (sourceB83 + difference 2 0) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA83 + difference 0 2) (sourceB83 + difference 2 0) sourceC83) = raw4034 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4034; decide +kernel
    rw [ha]
    exact (canonical4034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA83 + difference 0 3) (sourceB83 + difference 3 0) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA83 + difference 0 3) (sourceB83 + difference 3 0) sourceC83) = raw4035 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4035; decide +kernel
    rw [ha]
    exact (canonical4035 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA83 + difference 0 4) (sourceB83 + difference 4 0) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA83 + difference 0 4) (sourceB83 + difference 4 0) sourceC83) = raw4036 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4036; decide +kernel
    rw [ha]
    exact (canonical4036 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA83 + difference 0 5) (sourceB83 + difference 5 0) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA83 + difference 0 5) (sourceB83 + difference 5 0) sourceC83) = raw4037 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4037; decide +kernel
    rw [ha]
    exact (canonical4037 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA83 + difference 1 0) (sourceB83 + difference 0 1) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA83 + difference 1 0) (sourceB83 + difference 0 1) sourceC83) = raw3683 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw3683; decide +kernel
    rw [ha]
    exact (canonical3683 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA83 + difference 1 2) (sourceB83 + difference 2 1) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA83 + difference 1 2) (sourceB83 + difference 2 1) sourceC83) = raw4038 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4038; decide +kernel
    rw [ha]
    exact (canonical4038 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA83 + difference 1 3) (sourceB83 + difference 3 1) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA83 + difference 1 3) (sourceB83 + difference 3 1) sourceC83) = raw4039 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4039; decide +kernel
    rw [ha]
    exact (canonical4039 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA83 + difference 1 4) (sourceB83 + difference 4 1) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA83 + difference 1 4) (sourceB83 + difference 4 1) sourceC83) = raw4040 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4040; decide +kernel
    rw [ha]
    exact (canonical4040 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA83 + difference 1 5) (sourceB83 + difference 5 1) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA83 + difference 1 5) (sourceB83 + difference 5 1) sourceC83) = raw3657 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw3657; decide +kernel
    rw [ha]
    exact (canonical3657 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA83 + difference 2 0) (sourceB83 + difference 0 2) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA83 + difference 2 0) (sourceB83 + difference 0 2) sourceC83) = raw4041 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4041; decide +kernel
    rw [ha]
    exact (canonical4041 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA83 + difference 2 1) (sourceB83 + difference 1 2) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5225) := by
    have ha : (tripleCharges (sourceA83 + difference 2 1) (sourceB83 + difference 1 2) sourceC83) = raw4042 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4042; decide +kernel
    rw [ha]
    exact (canonical4042 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA83 + difference 2 3) (sourceB83 + difference 3 2) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5240) := by
    have ha : (tripleCharges (sourceA83 + difference 2 3) (sourceB83 + difference 3 2) sourceC83) = raw4043 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4043; decide +kernel
    rw [ha]
    exact (canonical4043 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA83 + difference 2 4) (sourceB83 + difference 4 2) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA83 + difference 2 4) (sourceB83 + difference 4 2) sourceC83) = raw4044 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4044; decide +kernel
    rw [ha]
    exact (canonical4044 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA83 + difference 2 5) (sourceB83 + difference 5 2) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA83 + difference 2 5) (sourceB83 + difference 5 2) sourceC83) = raw4045 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4045; decide +kernel
    rw [ha]
    exact (canonical4045 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA83 + difference 3 0) (sourceB83 + difference 0 3) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA83 + difference 3 0) (sourceB83 + difference 0 3) sourceC83) = raw3681 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw3681; decide +kernel
    rw [ha]
    exact (canonical3681 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA83 + difference 3 1) (sourceB83 + difference 1 3) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5225) := by
    have ha : (tripleCharges (sourceA83 + difference 3 1) (sourceB83 + difference 1 3) sourceC83) = raw4046 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4046; decide +kernel
    rw [ha]
    exact (canonical4046 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA83 + difference 3 2) (sourceB83 + difference 2 3) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5240) := by
    have ha : (tripleCharges (sourceA83 + difference 3 2) (sourceB83 + difference 2 3) sourceC83) = raw4047 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4047; decide +kernel
    rw [ha]
    exact (canonical4047 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA83 + difference 3 4) (sourceB83 + difference 4 3) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA83 + difference 3 4) (sourceB83 + difference 4 3) sourceC83) = raw4048 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4048; decide +kernel
    rw [ha]
    exact (canonical4048 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA83 + difference 3 5) (sourceB83 + difference 5 3) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA83 + difference 3 5) (sourceB83 + difference 5 3) sourceC83) = raw3655 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw3655; decide +kernel
    rw [ha]
    exact (canonical3655 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA83 + difference 4 0) (sourceB83 + difference 0 4) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA83 + difference 4 0) (sourceB83 + difference 0 4) sourceC83) = raw4049 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4049; decide +kernel
    rw [ha]
    exact (canonical4049 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA83 + difference 4 1) (sourceB83 + difference 1 4) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4883) := by
    have ha : (tripleCharges (sourceA83 + difference 4 1) (sourceB83 + difference 1 4) sourceC83) = raw4050 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4050; decide +kernel
    rw [ha]
    exact (canonical4050 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA83 + difference 4 2) (sourceB83 + difference 2 4) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4882) := by
    have ha : (tripleCharges (sourceA83 + difference 4 2) (sourceB83 + difference 2 4) sourceC83) = raw4051 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4051; decide +kernel
    rw [ha]
    exact (canonical4051 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA83 + difference 4 3) (sourceB83 + difference 3 4) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4882) := by
    have ha : (tripleCharges (sourceA83 + difference 4 3) (sourceB83 + difference 3 4) sourceC83) = raw4052 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4052; decide +kernel
    rw [ha]
    exact (canonical4052 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA83 + difference 4 5) (sourceB83 + difference 5 4) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA83 + difference 4 5) (sourceB83 + difference 5 4) sourceC83) = raw4053 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4053; decide +kernel
    rw [ha]
    exact (canonical4053 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA83 + difference 5 0) (sourceB83 + difference 0 5) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA83 + difference 5 0) (sourceB83 + difference 0 5) sourceC83) = raw4054 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4054; decide +kernel
    rw [ha]
    exact (canonical4054 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA83 + difference 5 1) (sourceB83 + difference 1 5) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5235) := by
    have ha : (tripleCharges (sourceA83 + difference 5 1) (sourceB83 + difference 1 5) sourceC83) = raw4055 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4055; decide +kernel
    rw [ha]
    exact (canonical4055 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA83 + difference 5 2) (sourceB83 + difference 2 5) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA83 + difference 5 2) (sourceB83 + difference 2 5) sourceC83) = raw4056 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4056; decide +kernel
    rw [ha]
    exact (canonical4056 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA83 + difference 5 3) (sourceB83 + difference 3 5) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA83 + difference 5 3) (sourceB83 + difference 3 5) sourceC83) = raw4057 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4057; decide +kernel
    rw [ha]
    exact (canonical4057 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA83 + difference 5 4) (sourceB83 + difference 4 5) sourceC83) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA83 + difference 5 4) (sourceB83 + difference 4 5) sourceC83) = raw4058 := by
      apply Matrix.ext; unfold tripleCharges sourceA83 sourceB83 sourceC83 difference raw4058; decide +kernel
    rw [ha]
    exact (canonical4058 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA83 sourceB83 sourceC83
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm83, Integer.Sparse.eval]
  linarith only [hs]

def sourceA84 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB84 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC84 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm84 : Integer.Sparse Master := [(Sum.inr 2135, 2), (Sum.inr 2136, 1), (Sum.inr 2137, 1), (Sum.inr 2197, 2), (Sum.inr 2218, 1), (Sum.inr 2222, 1), (Sum.inr 2281, 1), (Sum.inr 2664, 2), (Sum.inr 2667, 2), (Sum.inr 2680, 1), (Sum.inr 2692, 2), (Sum.inr 2712, 2), (Sum.inr 2716, 2), (Sum.inr 2726, 1), (Sum.inr 2734, 2), (Sum.inr 2770, 1), (Sum.inr 2778, 1), (Sum.inr 3031, 2), (Sum.inr 3046, 1), (Sum.inr 3090, 1), (Sum.inr 3095, 1)]

theorem sourceEq84 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm84 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA84 + difference 0 1) (sourceB84 + difference 1 0) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3046) := by
    have ha : (tripleCharges (sourceA84 + difference 0 1) (sourceB84 + difference 1 0) sourceC84) = raw4059 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4059; decide +kernel
    rw [ha]
    exact (canonical4059 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA84 + difference 0 2) (sourceB84 + difference 2 0) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA84 + difference 0 2) (sourceB84 + difference 2 0) sourceC84) = raw4060 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4060; decide +kernel
    rw [ha]
    exact (canonical4060 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA84 + difference 0 3) (sourceB84 + difference 3 0) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA84 + difference 0 3) (sourceB84 + difference 3 0) sourceC84) = raw4061 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4061; decide +kernel
    rw [ha]
    exact (canonical4061 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA84 + difference 0 4) (sourceB84 + difference 4 0) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA84 + difference 0 4) (sourceB84 + difference 4 0) sourceC84) = raw4062 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4062; decide +kernel
    rw [ha]
    exact (canonical4062 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA84 + difference 0 5) (sourceB84 + difference 5 0) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA84 + difference 0 5) (sourceB84 + difference 5 0) sourceC84) = raw4063 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4063; decide +kernel
    rw [ha]
    exact (canonical4063 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA84 + difference 1 0) (sourceB84 + difference 0 1) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA84 + difference 1 0) (sourceB84 + difference 0 1) sourceC84) = raw3713 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw3713; decide +kernel
    rw [ha]
    exact (canonical3713 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA84 + difference 1 2) (sourceB84 + difference 2 1) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA84 + difference 1 2) (sourceB84 + difference 2 1) sourceC84) = raw4064 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4064; decide +kernel
    rw [ha]
    exact (canonical4064 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA84 + difference 1 3) (sourceB84 + difference 3 1) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA84 + difference 1 3) (sourceB84 + difference 3 1) sourceC84) = raw4065 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4065; decide +kernel
    rw [ha]
    exact (canonical4065 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA84 + difference 1 4) (sourceB84 + difference 4 1) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA84 + difference 1 4) (sourceB84 + difference 4 1) sourceC84) = raw4066 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4066; decide +kernel
    rw [ha]
    exact (canonical4066 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA84 + difference 1 5) (sourceB84 + difference 5 1) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA84 + difference 1 5) (sourceB84 + difference 5 1) sourceC84) = raw3687 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw3687; decide +kernel
    rw [ha]
    exact (canonical3687 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA84 + difference 2 0) (sourceB84 + difference 0 2) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA84 + difference 2 0) (sourceB84 + difference 0 2) sourceC84) = raw4067 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4067; decide +kernel
    rw [ha]
    exact (canonical4067 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA84 + difference 2 1) (sourceB84 + difference 1 2) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2667) := by
    have ha : (tripleCharges (sourceA84 + difference 2 1) (sourceB84 + difference 1 2) sourceC84) = raw4068 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4068; decide +kernel
    rw [ha]
    exact (canonical4068 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA84 + difference 2 3) (sourceB84 + difference 3 2) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2692) := by
    have ha : (tripleCharges (sourceA84 + difference 2 3) (sourceB84 + difference 3 2) sourceC84) = raw4069 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4069; decide +kernel
    rw [ha]
    exact (canonical4069 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA84 + difference 2 4) (sourceB84 + difference 4 2) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA84 + difference 2 4) (sourceB84 + difference 4 2) sourceC84) = raw4070 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4070; decide +kernel
    rw [ha]
    exact (canonical4070 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA84 + difference 2 5) (sourceB84 + difference 5 2) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA84 + difference 2 5) (sourceB84 + difference 5 2) sourceC84) = raw4071 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4071; decide +kernel
    rw [ha]
    exact (canonical4071 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA84 + difference 3 0) (sourceB84 + difference 0 3) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA84 + difference 3 0) (sourceB84 + difference 0 3) sourceC84) = raw3711 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw3711; decide +kernel
    rw [ha]
    exact (canonical3711 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA84 + difference 3 1) (sourceB84 + difference 1 3) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2667) := by
    have ha : (tripleCharges (sourceA84 + difference 3 1) (sourceB84 + difference 1 3) sourceC84) = raw4072 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4072; decide +kernel
    rw [ha]
    exact (canonical4072 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA84 + difference 3 2) (sourceB84 + difference 2 3) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2692) := by
    have ha : (tripleCharges (sourceA84 + difference 3 2) (sourceB84 + difference 2 3) sourceC84) = raw4073 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4073; decide +kernel
    rw [ha]
    exact (canonical4073 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA84 + difference 3 4) (sourceB84 + difference 4 3) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA84 + difference 3 4) (sourceB84 + difference 4 3) sourceC84) = raw4074 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4074; decide +kernel
    rw [ha]
    exact (canonical4074 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA84 + difference 3 5) (sourceB84 + difference 5 3) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA84 + difference 3 5) (sourceB84 + difference 5 3) sourceC84) = raw3685 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw3685; decide +kernel
    rw [ha]
    exact (canonical3685 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA84 + difference 4 0) (sourceB84 + difference 0 4) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA84 + difference 4 0) (sourceB84 + difference 0 4) sourceC84) = raw4075 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4075; decide +kernel
    rw [ha]
    exact (canonical4075 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA84 + difference 4 1) (sourceB84 + difference 1 4) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2137) := by
    have ha : (tripleCharges (sourceA84 + difference 4 1) (sourceB84 + difference 1 4) sourceC84) = raw4076 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4076; decide +kernel
    rw [ha]
    exact (canonical4076 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA84 + difference 4 2) (sourceB84 + difference 2 4) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2135) := by
    have ha : (tripleCharges (sourceA84 + difference 4 2) (sourceB84 + difference 2 4) sourceC84) = raw4077 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4077; decide +kernel
    rw [ha]
    exact (canonical4077 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA84 + difference 4 3) (sourceB84 + difference 3 4) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2135) := by
    have ha : (tripleCharges (sourceA84 + difference 4 3) (sourceB84 + difference 3 4) sourceC84) = raw4078 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4078; decide +kernel
    rw [ha]
    exact (canonical4078 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA84 + difference 4 5) (sourceB84 + difference 5 4) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA84 + difference 4 5) (sourceB84 + difference 5 4) sourceC84) = raw4079 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4079; decide +kernel
    rw [ha]
    exact (canonical4079 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA84 + difference 5 0) (sourceB84 + difference 0 5) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA84 + difference 5 0) (sourceB84 + difference 0 5) sourceC84) = raw4080 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4080; decide +kernel
    rw [ha]
    exact (canonical4080 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA84 + difference 5 1) (sourceB84 + difference 1 5) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2680) := by
    have ha : (tripleCharges (sourceA84 + difference 5 1) (sourceB84 + difference 1 5) sourceC84) = raw4081 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4081; decide +kernel
    rw [ha]
    exact (canonical4081 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA84 + difference 5 2) (sourceB84 + difference 2 5) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA84 + difference 5 2) (sourceB84 + difference 2 5) sourceC84) = raw4082 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4082; decide +kernel
    rw [ha]
    exact (canonical4082 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA84 + difference 5 3) (sourceB84 + difference 3 5) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA84 + difference 5 3) (sourceB84 + difference 3 5) sourceC84) = raw4083 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4083; decide +kernel
    rw [ha]
    exact (canonical4083 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA84 + difference 5 4) (sourceB84 + difference 4 5) sourceC84) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA84 + difference 5 4) (sourceB84 + difference 4 5) sourceC84) = raw4084 := by
      apply Matrix.ext; unfold tripleCharges sourceA84 sourceB84 sourceC84 difference raw4084; decide +kernel
    rw [ha]
    exact (canonical4084 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA84 sourceB84 sourceC84
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm84, Integer.Sparse.eval]
  linarith only [hs]

def sourceA85 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB85 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC85 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm85 : Integer.Sparse Master := [(Sum.inr 2065, 1), (Sum.inr 3389, 2), (Sum.inr 3396, 1), (Sum.inr 3545, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem sourceEq85 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm85 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA85 + difference 0 0) (sourceB85 + difference 0 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA85 + difference 0 0) (sourceB85 + difference 0 0) sourceC85) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA85 + difference 0 1) (sourceB85 + difference 1 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3396) := by
    have ha : (tripleCharges (sourceA85 + difference 0 1) (sourceB85 + difference 1 0) sourceC85) = raw4086 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4086; decide +kernel
    rw [ha]
    exact (canonical4086 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA85 + difference 0 2) (sourceB85 + difference 2 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA85 + difference 0 2) (sourceB85 + difference 2 0) sourceC85) = raw4087 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4087; decide +kernel
    rw [ha]
    exact (canonical4087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA85 + difference 0 3) (sourceB85 + difference 3 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA85 + difference 0 3) (sourceB85 + difference 3 0) sourceC85) = raw4088 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4088; decide +kernel
    rw [ha]
    exact (canonical4088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA85 + difference 0 4) (sourceB85 + difference 4 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA85 + difference 0 4) (sourceB85 + difference 4 0) sourceC85) = raw4089 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4089; decide +kernel
    rw [ha]
    exact (canonical4089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA85 + difference 0 5) (sourceB85 + difference 5 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA85 + difference 0 5) (sourceB85 + difference 5 0) sourceC85) = raw4090 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4090; decide +kernel
    rw [ha]
    exact (canonical4090 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA85 + sourceB85) sourceC85) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA85 + sourceB85) sourceC85) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA85 sourceB85 sourceC85 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA85 sourceB85 sourceC85
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm85, Integer.Sparse.eval]
  linarith only [hs]

def sourceA86 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB86 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC86 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm86 : Integer.Sparse Master := [(Sum.inr 2055, 2), (Sum.inr 2063, 1), (Sum.inr 2065, 1), (Sum.inr 2294, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem sourceEq86 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm86 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA86 + difference 0 0) (sourceB86 + difference 0 0) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA86 + difference 0 0) (sourceB86 + difference 0 0) sourceC86) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA86 + difference 1 0) (sourceB86 + difference 0 1) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA86 + difference 1 0) (sourceB86 + difference 0 1) sourceC86) = raw4091 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4091; decide +kernel
    rw [ha]
    exact (canonical4091 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA86 + difference 2 0) (sourceB86 + difference 0 2) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA86 + difference 2 0) (sourceB86 + difference 0 2) sourceC86) = raw4092 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4092; decide +kernel
    rw [ha]
    exact (canonical4092 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA86 + difference 3 0) (sourceB86 + difference 0 3) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA86 + difference 3 0) (sourceB86 + difference 0 3) sourceC86) = raw3734 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw3734; decide +kernel
    rw [ha]
    exact (canonical3734 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA86 + difference 4 0) (sourceB86 + difference 0 4) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA86 + difference 4 0) (sourceB86 + difference 0 4) sourceC86) = raw4093 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4093; decide +kernel
    rw [ha]
    exact (canonical4093 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA86 + difference 5 0) (sourceB86 + difference 0 5) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA86 + difference 5 0) (sourceB86 + difference 0 5) sourceC86) = raw4094 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4094; decide +kernel
    rw [ha]
    exact (canonical4094 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA86 + sourceB86) sourceC86) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA86 + sourceB86) sourceC86) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA86 sourceB86 sourceC86 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA86 sourceB86 sourceC86
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm86, Integer.Sparse.eval]
  linarith only [hs]

def sourceA87 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB87 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC87 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm87 : Integer.Sparse Master := [(Sum.inr 2294, 2), (Sum.inr 3549, 3), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

theorem sourceEq87 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm87 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA87 + difference 1 0) (sourceB87 + difference 0 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA87 + difference 1 0) (sourceB87 + difference 0 1) sourceC87) = raw4091 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4091; decide +kernel
    rw [ha]
    exact (canonical4091 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA87 + difference 1 1) (sourceB87 + difference 1 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA87 + difference 1 1) (sourceB87 + difference 1 1) sourceC87) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA87 + difference 1 2) (sourceB87 + difference 2 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA87 + difference 1 2) (sourceB87 + difference 2 1) sourceC87) = raw4095 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4095; decide +kernel
    rw [ha]
    exact (canonical4095 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA87 + difference 1 3) (sourceB87 + difference 3 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA87 + difference 1 3) (sourceB87 + difference 3 1) sourceC87) = raw4096 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4096; decide +kernel
    rw [ha]
    exact (canonical4096 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA87 + difference 1 4) (sourceB87 + difference 4 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA87 + difference 1 4) (sourceB87 + difference 4 1) sourceC87) = raw4097 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4097; decide +kernel
    rw [ha]
    exact (canonical4097 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA87 + difference 1 5) (sourceB87 + difference 5 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA87 + difference 1 5) (sourceB87 + difference 5 1) sourceC87) = raw3718 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw3718; decide +kernel
    rw [ha]
    exact (canonical3718 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA87 + sourceB87) sourceC87) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA87 + sourceB87) sourceC87) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA87 sourceB87 sourceC87 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA87 sourceB87 sourceC87
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm87, Integer.Sparse.eval]
  linarith only [hs]

def sourceA88 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB88 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC88 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm88 : Integer.Sparse Master := [(Sum.inr 3160, 1), (Sum.inr 3393, 2), (Sum.inr 3396, 2), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem sourceEq88 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm88 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA88 + difference 0 1) (sourceB88 + difference 1 0) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3396) := by
    have ha : (tripleCharges (sourceA88 + difference 0 1) (sourceB88 + difference 1 0) sourceC88) = raw4086 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4086; decide +kernel
    rw [ha]
    exact (canonical4086 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA88 + difference 1 1) (sourceB88 + difference 1 1) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA88 + difference 1 1) (sourceB88 + difference 1 1) sourceC88) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA88 + difference 2 1) (sourceB88 + difference 1 2) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA88 + difference 2 1) (sourceB88 + difference 1 2) sourceC88) = raw4098 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4098; decide +kernel
    rw [ha]
    exact (canonical4098 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA88 + difference 3 1) (sourceB88 + difference 1 3) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA88 + difference 3 1) (sourceB88 + difference 1 3) sourceC88) = raw4099 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4099; decide +kernel
    rw [ha]
    exact (canonical4099 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA88 + difference 4 1) (sourceB88 + difference 1 4) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3160) := by
    have ha : (tripleCharges (sourceA88 + difference 4 1) (sourceB88 + difference 1 4) sourceC88) = raw4100 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4100; decide +kernel
    rw [ha]
    exact (canonical4100 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA88 + difference 5 1) (sourceB88 + difference 1 5) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3396) := by
    have ha : (tripleCharges (sourceA88 + difference 5 1) (sourceB88 + difference 1 5) sourceC88) = raw4101 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4101; decide +kernel
    rw [ha]
    exact (canonical4101 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA88 + sourceB88) sourceC88) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA88 + sourceB88) sourceC88) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA88 sourceB88 sourceC88 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA88 sourceB88 sourceC88
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm88, Integer.Sparse.eval]
  linarith only [hs]

def sourceA89 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB89 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC89 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm89 : Integer.Sparse Master := [(Sum.inr 2055, 2), (Sum.inr 3393, 1), (Sum.inr 3495, 1), (Sum.inr 3543, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem sourceEq89 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm89 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA89 + difference 2 0) (sourceB89 + difference 0 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA89 + difference 2 0) (sourceB89 + difference 0 2) sourceC89) = raw4092 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4092; decide +kernel
    rw [ha]
    exact (canonical4092 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA89 + difference 2 1) (sourceB89 + difference 1 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA89 + difference 2 1) (sourceB89 + difference 1 2) sourceC89) = raw4098 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4098; decide +kernel
    rw [ha]
    exact (canonical4098 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA89 + difference 2 2) (sourceB89 + difference 2 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA89 + difference 2 2) (sourceB89 + difference 2 2) sourceC89) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA89 + difference 2 3) (sourceB89 + difference 3 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3495) := by
    have ha : (tripleCharges (sourceA89 + difference 2 3) (sourceB89 + difference 3 2) sourceC89) = raw4102 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4102; decide +kernel
    rw [ha]
    exact (canonical4102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA89 + difference 2 4) (sourceB89 + difference 4 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA89 + difference 2 4) (sourceB89 + difference 4 2) sourceC89) = raw4103 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4103; decide +kernel
    rw [ha]
    exact (canonical4103 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA89 + difference 2 5) (sourceB89 + difference 5 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA89 + difference 2 5) (sourceB89 + difference 5 2) sourceC89) = raw4104 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4104; decide +kernel
    rw [ha]
    exact (canonical4104 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA89 + sourceB89) sourceC89) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA89 + sourceB89) sourceC89) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA89 sourceB89 sourceC89 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA89 sourceB89 sourceC89
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm89, Integer.Sparse.eval]
  linarith only [hs]

def sourceA90 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB90 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC90 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm90 : Integer.Sparse Master := [(Sum.inr 3154, 1), (Sum.inr 3389, 2), (Sum.inr 3495, 1), (Sum.inr 3549, 2), (Sum.inr 4085, -1)]

theorem sourceEq90 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm90 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA90 + difference 0 2) (sourceB90 + difference 2 0) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA90 + difference 0 2) (sourceB90 + difference 2 0) sourceC90) = raw4087 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4087; decide +kernel
    rw [ha]
    exact (canonical4087 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA90 + difference 1 2) (sourceB90 + difference 2 1) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA90 + difference 1 2) (sourceB90 + difference 2 1) sourceC90) = raw4095 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4095; decide +kernel
    rw [ha]
    exact (canonical4095 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA90 + difference 2 2) (sourceB90 + difference 2 2) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA90 + difference 2 2) (sourceB90 + difference 2 2) sourceC90) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA90 + difference 3 2) (sourceB90 + difference 2 3) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3495) := by
    have ha : (tripleCharges (sourceA90 + difference 3 2) (sourceB90 + difference 2 3) sourceC90) = raw4105 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4105; decide +kernel
    rw [ha]
    exact (canonical4105 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA90 + difference 4 2) (sourceB90 + difference 2 4) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3154) := by
    have ha : (tripleCharges (sourceA90 + difference 4 2) (sourceB90 + difference 2 4) sourceC90) = raw4106 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4106; decide +kernel
    rw [ha]
    exact (canonical4106 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA90 + difference 5 2) (sourceB90 + difference 2 5) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA90 + difference 5 2) (sourceB90 + difference 2 5) sourceC90) = raw4107 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4107; decide +kernel
    rw [ha]
    exact (canonical4107 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA90 + sourceB90) sourceC90) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA90 + sourceB90) sourceC90) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA90 sourceB90 sourceC90 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA90 sourceB90 sourceC90
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm90, Integer.Sparse.eval]
  linarith only [hs]

def sourceA91 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB91 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC91 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm91 : Integer.Sparse Master := [(Sum.inr 2063, 2), (Sum.inr 3154, 2), (Sum.inr 3160, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem sourceEq91 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm91 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA91 + difference 4 0) (sourceB91 + difference 0 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA91 + difference 4 0) (sourceB91 + difference 0 4) sourceC91) = raw4093 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4093; decide +kernel
    rw [ha]
    exact (canonical4093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA91 + difference 4 1) (sourceB91 + difference 1 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3160) := by
    have ha : (tripleCharges (sourceA91 + difference 4 1) (sourceB91 + difference 1 4) sourceC91) = raw4100 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4100; decide +kernel
    rw [ha]
    exact (canonical4100 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA91 + difference 4 2) (sourceB91 + difference 2 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3154) := by
    have ha : (tripleCharges (sourceA91 + difference 4 2) (sourceB91 + difference 2 4) sourceC91) = raw4106 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4106; decide +kernel
    rw [ha]
    exact (canonical4106 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA91 + difference 4 3) (sourceB91 + difference 3 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3154) := by
    have ha : (tripleCharges (sourceA91 + difference 4 3) (sourceB91 + difference 3 4) sourceC91) = raw4108 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4108; decide +kernel
    rw [ha]
    exact (canonical4108 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA91 + difference 4 4) (sourceB91 + difference 4 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA91 + difference 4 4) (sourceB91 + difference 4 4) sourceC91) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA91 + difference 4 5) (sourceB91 + difference 5 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA91 + difference 4 5) (sourceB91 + difference 5 4) sourceC91) = raw4109 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4109; decide +kernel
    rw [ha]
    exact (canonical4109 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA91 + sourceB91) sourceC91) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA91 + sourceB91) sourceC91) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA91 sourceB91 sourceC91 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA91 sourceB91 sourceC91
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm91, Integer.Sparse.eval]
  linarith only [hs]

def sourceA92 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB92 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC92 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm92 : Integer.Sparse Master := [(Sum.inr 4391, 1), (Sum.inr 4394, 1), (Sum.inr 4402, 2), (Sum.inr 4440, 1), (Sum.inr 4577, 1), (Sum.inr 4584, 1), (Sum.inr 4591, 2), (Sum.inr 4992, 1), (Sum.inr 5001, 2), (Sum.inr 5048, 2), (Sum.inr 5065, 1), (Sum.inr 5078, 2), (Sum.inr 5128, 2), (Sum.inr 5139, 2), (Sum.inr 5250, 1), (Sum.inr 5251, 1), (Sum.inr 5259, 2), (Sum.inr 5260, 2), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5439, 1)]

theorem sourceEq92 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm92 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA92 + difference 0 1) (sourceB92 + difference 1 0) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA92 + difference 0 1) (sourceB92 + difference 1 0) sourceC92) = raw4110 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4110; decide +kernel
    rw [ha]
    exact (canonical4110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA92 + difference 0 2) (sourceB92 + difference 2 0) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA92 + difference 0 2) (sourceB92 + difference 2 0) sourceC92) = raw4111 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4111; decide +kernel
    rw [ha]
    exact (canonical4111 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA92 + difference 0 3) (sourceB92 + difference 3 0) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA92 + difference 0 3) (sourceB92 + difference 3 0) sourceC92) = raw4112 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4112; decide +kernel
    rw [ha]
    exact (canonical4112 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA92 + difference 0 4) (sourceB92 + difference 4 0) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA92 + difference 0 4) (sourceB92 + difference 4 0) sourceC92) = raw4113 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4113; decide +kernel
    rw [ha]
    exact (canonical4113 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA92 + difference 0 5) (sourceB92 + difference 5 0) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA92 + difference 0 5) (sourceB92 + difference 5 0) sourceC92) = raw4114 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4114; decide +kernel
    rw [ha]
    exact (canonical4114 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA92 + difference 1 0) (sourceB92 + difference 0 1) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4584) := by
    have ha : (tripleCharges (sourceA92 + difference 1 0) (sourceB92 + difference 0 1) sourceC92) = raw4115 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4115; decide +kernel
    rw [ha]
    exact (canonical4115 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA92 + difference 1 2) (sourceB92 + difference 2 1) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4992) := by
    have ha : (tripleCharges (sourceA92 + difference 1 2) (sourceB92 + difference 2 1) sourceC92) = raw4116 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4116; decide +kernel
    rw [ha]
    exact (canonical4116 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA92 + difference 1 3) (sourceB92 + difference 3 1) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5001) := by
    have ha : (tripleCharges (sourceA92 + difference 1 3) (sourceB92 + difference 3 1) sourceC92) = raw4117 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4117; decide +kernel
    rw [ha]
    exact (canonical4117 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA92 + difference 1 4) (sourceB92 + difference 4 1) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5001) := by
    have ha : (tripleCharges (sourceA92 + difference 1 4) (sourceB92 + difference 4 1) sourceC92) = raw4118 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4118; decide +kernel
    rw [ha]
    exact (canonical4118 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA92 + difference 1 5) (sourceB92 + difference 5 1) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA92 + difference 1 5) (sourceB92 + difference 5 1) sourceC92) = raw4119 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4119; decide +kernel
    rw [ha]
    exact (canonical4119 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA92 + difference 2 0) (sourceB92 + difference 0 2) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4577) := by
    have ha : (tripleCharges (sourceA92 + difference 2 0) (sourceB92 + difference 0 2) sourceC92) = raw4120 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4120; decide +kernel
    rw [ha]
    exact (canonical4120 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA92 + difference 2 1) (sourceB92 + difference 1 2) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA92 + difference 2 1) (sourceB92 + difference 1 2) sourceC92) = raw4121 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4121; decide +kernel
    rw [ha]
    exact (canonical4121 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA92 + difference 2 3) (sourceB92 + difference 3 2) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5048) := by
    have ha : (tripleCharges (sourceA92 + difference 2 3) (sourceB92 + difference 3 2) sourceC92) = raw4122 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4122; decide +kernel
    rw [ha]
    exact (canonical4122 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA92 + difference 2 4) (sourceB92 + difference 4 2) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5048) := by
    have ha : (tripleCharges (sourceA92 + difference 2 4) (sourceB92 + difference 4 2) sourceC92) = raw4123 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4123; decide +kernel
    rw [ha]
    exact (canonical4123 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA92 + difference 2 5) (sourceB92 + difference 5 2) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA92 + difference 2 5) (sourceB92 + difference 5 2) sourceC92) = raw4124 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4124; decide +kernel
    rw [ha]
    exact (canonical4124 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA92 + difference 3 0) (sourceB92 + difference 0 3) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA92 + difference 3 0) (sourceB92 + difference 0 3) sourceC92) = raw4125 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4125; decide +kernel
    rw [ha]
    exact (canonical4125 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA92 + difference 3 1) (sourceB92 + difference 1 3) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA92 + difference 3 1) (sourceB92 + difference 1 3) sourceC92) = raw4126 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4126; decide +kernel
    rw [ha]
    exact (canonical4126 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA92 + difference 3 2) (sourceB92 + difference 2 3) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA92 + difference 3 2) (sourceB92 + difference 2 3) sourceC92) = raw4127 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4127; decide +kernel
    rw [ha]
    exact (canonical4127 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA92 + difference 3 4) (sourceB92 + difference 4 3) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA92 + difference 3 4) (sourceB92 + difference 4 3) sourceC92) = raw4128 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4128; decide +kernel
    rw [ha]
    exact (canonical4128 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA92 + difference 3 5) (sourceB92 + difference 5 3) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA92 + difference 3 5) (sourceB92 + difference 5 3) sourceC92) = raw4129 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4129; decide +kernel
    rw [ha]
    exact (canonical4129 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA92 + difference 4 0) (sourceB92 + difference 0 4) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA92 + difference 4 0) (sourceB92 + difference 0 4) sourceC92) = raw4130 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4130; decide +kernel
    rw [ha]
    exact (canonical4130 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA92 + difference 4 1) (sourceB92 + difference 1 4) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA92 + difference 4 1) (sourceB92 + difference 1 4) sourceC92) = raw4131 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4131; decide +kernel
    rw [ha]
    exact (canonical4131 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA92 + difference 4 2) (sourceB92 + difference 2 4) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA92 + difference 4 2) (sourceB92 + difference 2 4) sourceC92) = raw4132 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4132; decide +kernel
    rw [ha]
    exact (canonical4132 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA92 + difference 4 3) (sourceB92 + difference 3 4) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA92 + difference 4 3) (sourceB92 + difference 3 4) sourceC92) = raw4133 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4133; decide +kernel
    rw [ha]
    exact (canonical4133 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA92 + difference 4 5) (sourceB92 + difference 5 4) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA92 + difference 4 5) (sourceB92 + difference 5 4) sourceC92) = raw4134 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4134; decide +kernel
    rw [ha]
    exact (canonical4134 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA92 + difference 5 0) (sourceB92 + difference 0 5) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4394) := by
    have ha : (tripleCharges (sourceA92 + difference 5 0) (sourceB92 + difference 0 5) sourceC92) = raw4135 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4135; decide +kernel
    rw [ha]
    exact (canonical4135 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA92 + difference 5 1) (sourceB92 + difference 1 5) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA92 + difference 5 1) (sourceB92 + difference 1 5) sourceC92) = raw4136 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4136; decide +kernel
    rw [ha]
    exact (canonical4136 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA92 + difference 5 2) (sourceB92 + difference 2 5) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4391) := by
    have ha : (tripleCharges (sourceA92 + difference 5 2) (sourceB92 + difference 2 5) sourceC92) = raw4137 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4137; decide +kernel
    rw [ha]
    exact (canonical4137 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA92 + difference 5 3) (sourceB92 + difference 3 5) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA92 + difference 5 3) (sourceB92 + difference 3 5) sourceC92) = raw4138 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4138; decide +kernel
    rw [ha]
    exact (canonical4138 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA92 + difference 5 4) (sourceB92 + difference 4 5) sourceC92) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA92 + difference 5 4) (sourceB92 + difference 4 5) sourceC92) = raw4139 := by
      apply Matrix.ext; unfold tripleCharges sourceA92 sourceB92 sourceC92 difference raw4139; decide +kernel
    rw [ha]
    exact (canonical4139 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA92 sourceB92 sourceC92
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm92, Integer.Sparse.eval]
  linarith only [hs]

def sourceA93 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB93 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC93 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm93 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 975, 1), (Sum.inr 983, 2), (Sum.inr 1022, 1), (Sum.inr 1195, 1), (Sum.inr 1203, 1), (Sum.inr 1215, 2), (Sum.inr 2378, 1), (Sum.inr 2386, 2), (Sum.inr 2450, 2), (Sum.inr 2470, 1), (Sum.inr 2543, 2), (Sum.inr 2558, 2), (Sum.inr 2572, 2), (Sum.inr 2710, 1), (Sum.inr 2724, 2), (Sum.inr 2753, 1), (Sum.inr 3065, 1), (Sum.inr 3078, 1), (Sum.inr 3088, 2), (Sum.inr 4012, 1)]

theorem sourceEq93 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm93 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA93 + difference 0 1) (sourceB93 + difference 1 0) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA93 + difference 0 1) (sourceB93 + difference 1 0) sourceC93) = raw4140 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4140; decide +kernel
    rw [ha]
    exact (canonical4140 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA93 + difference 0 2) (sourceB93 + difference 2 0) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA93 + difference 0 2) (sourceB93 + difference 2 0) sourceC93) = raw4141 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4141; decide +kernel
    rw [ha]
    exact (canonical4141 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA93 + difference 0 3) (sourceB93 + difference 3 0) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA93 + difference 0 3) (sourceB93 + difference 3 0) sourceC93) = raw4142 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4142; decide +kernel
    rw [ha]
    exact (canonical4142 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA93 + difference 0 4) (sourceB93 + difference 4 0) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA93 + difference 0 4) (sourceB93 + difference 4 0) sourceC93) = raw4143 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4143; decide +kernel
    rw [ha]
    exact (canonical4143 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA93 + difference 0 5) (sourceB93 + difference 5 0) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA93 + difference 0 5) (sourceB93 + difference 5 0) sourceC93) = raw4144 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4144; decide +kernel
    rw [ha]
    exact (canonical4144 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA93 + difference 1 0) (sourceB93 + difference 0 1) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1203) := by
    have ha : (tripleCharges (sourceA93 + difference 1 0) (sourceB93 + difference 0 1) sourceC93) = raw4145 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4145; decide +kernel
    rw [ha]
    exact (canonical4145 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA93 + difference 1 2) (sourceB93 + difference 2 1) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2378) := by
    have ha : (tripleCharges (sourceA93 + difference 1 2) (sourceB93 + difference 2 1) sourceC93) = raw4146 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4146; decide +kernel
    rw [ha]
    exact (canonical4146 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA93 + difference 1 3) (sourceB93 + difference 3 1) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2386) := by
    have ha : (tripleCharges (sourceA93 + difference 1 3) (sourceB93 + difference 3 1) sourceC93) = raw4147 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4147; decide +kernel
    rw [ha]
    exact (canonical4147 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA93 + difference 1 4) (sourceB93 + difference 4 1) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2386) := by
    have ha : (tripleCharges (sourceA93 + difference 1 4) (sourceB93 + difference 4 1) sourceC93) = raw4148 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4148; decide +kernel
    rw [ha]
    exact (canonical4148 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA93 + difference 1 5) (sourceB93 + difference 5 1) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA93 + difference 1 5) (sourceB93 + difference 5 1) sourceC93) = raw4149 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4149; decide +kernel
    rw [ha]
    exact (canonical4149 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA93 + difference 2 0) (sourceB93 + difference 0 2) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1195) := by
    have ha : (tripleCharges (sourceA93 + difference 2 0) (sourceB93 + difference 0 2) sourceC93) = raw4150 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4150; decide +kernel
    rw [ha]
    exact (canonical4150 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA93 + difference 2 1) (sourceB93 + difference 1 2) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA93 + difference 2 1) (sourceB93 + difference 1 2) sourceC93) = raw4151 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4151; decide +kernel
    rw [ha]
    exact (canonical4151 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA93 + difference 2 3) (sourceB93 + difference 3 2) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2450) := by
    have ha : (tripleCharges (sourceA93 + difference 2 3) (sourceB93 + difference 3 2) sourceC93) = raw4152 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4152; decide +kernel
    rw [ha]
    exact (canonical4152 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA93 + difference 2 4) (sourceB93 + difference 4 2) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2450) := by
    have ha : (tripleCharges (sourceA93 + difference 2 4) (sourceB93 + difference 4 2) sourceC93) = raw4153 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4153; decide +kernel
    rw [ha]
    exact (canonical4153 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA93 + difference 2 5) (sourceB93 + difference 5 2) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA93 + difference 2 5) (sourceB93 + difference 5 2) sourceC93) = raw4154 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4154; decide +kernel
    rw [ha]
    exact (canonical4154 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA93 + difference 3 0) (sourceB93 + difference 0 3) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA93 + difference 3 0) (sourceB93 + difference 0 3) sourceC93) = raw4155 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4155; decide +kernel
    rw [ha]
    exact (canonical4155 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA93 + difference 3 1) (sourceB93 + difference 1 3) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA93 + difference 3 1) (sourceB93 + difference 1 3) sourceC93) = raw4156 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4156; decide +kernel
    rw [ha]
    exact (canonical4156 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA93 + difference 3 2) (sourceB93 + difference 2 3) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA93 + difference 3 2) (sourceB93 + difference 2 3) sourceC93) = raw4157 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4157; decide +kernel
    rw [ha]
    exact (canonical4157 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA93 + difference 3 4) (sourceB93 + difference 4 3) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA93 + difference 3 4) (sourceB93 + difference 4 3) sourceC93) = raw4158 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4158; decide +kernel
    rw [ha]
    exact (canonical4158 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA93 + difference 3 5) (sourceB93 + difference 5 3) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA93 + difference 3 5) (sourceB93 + difference 5 3) sourceC93) = raw4159 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4159; decide +kernel
    rw [ha]
    exact (canonical4159 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA93 + difference 4 0) (sourceB93 + difference 0 4) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA93 + difference 4 0) (sourceB93 + difference 0 4) sourceC93) = raw4160 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4160; decide +kernel
    rw [ha]
    exact (canonical4160 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA93 + difference 4 1) (sourceB93 + difference 1 4) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA93 + difference 4 1) (sourceB93 + difference 1 4) sourceC93) = raw4161 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4161; decide +kernel
    rw [ha]
    exact (canonical4161 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA93 + difference 4 2) (sourceB93 + difference 2 4) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA93 + difference 4 2) (sourceB93 + difference 2 4) sourceC93) = raw4162 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4162; decide +kernel
    rw [ha]
    exact (canonical4162 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA93 + difference 4 3) (sourceB93 + difference 3 4) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA93 + difference 4 3) (sourceB93 + difference 3 4) sourceC93) = raw4163 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4163; decide +kernel
    rw [ha]
    exact (canonical4163 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA93 + difference 4 5) (sourceB93 + difference 5 4) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA93 + difference 4 5) (sourceB93 + difference 5 4) sourceC93) = raw4164 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4164; decide +kernel
    rw [ha]
    exact (canonical4164 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA93 + difference 5 0) (sourceB93 + difference 0 5) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA93 + difference 5 0) (sourceB93 + difference 0 5) sourceC93) = raw4165 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4165; decide +kernel
    rw [ha]
    exact (canonical4165 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA93 + difference 5 1) (sourceB93 + difference 1 5) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA93 + difference 5 1) (sourceB93 + difference 1 5) sourceC93) = raw4166 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4166; decide +kernel
    rw [ha]
    exact (canonical4166 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA93 + difference 5 2) (sourceB93 + difference 2 5) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 972) := by
    have ha : (tripleCharges (sourceA93 + difference 5 2) (sourceB93 + difference 2 5) sourceC93) = raw4167 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4167; decide +kernel
    rw [ha]
    exact (canonical4167 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA93 + difference 5 3) (sourceB93 + difference 3 5) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA93 + difference 5 3) (sourceB93 + difference 3 5) sourceC93) = raw4168 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4168; decide +kernel
    rw [ha]
    exact (canonical4168 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA93 + difference 5 4) (sourceB93 + difference 4 5) sourceC93) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA93 + difference 5 4) (sourceB93 + difference 4 5) sourceC93) = raw4169 := by
      apply Matrix.ext; unfold tripleCharges sourceA93 sourceB93 sourceC93 difference raw4169; decide +kernel
    rw [ha]
    exact (canonical4169 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA93 sourceB93 sourceC93
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm93, Integer.Sparse.eval]
  linarith only [hs]

def sourceA94 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB94 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC94 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm94 : Integer.Sparse Master := [(Sum.inr 1613, 1), (Sum.inr 1615, 1), (Sum.inr 1619, 2), (Sum.inr 1723, 1), (Sum.inr 3279, 1), (Sum.inr 3283, 1), (Sum.inr 3291, 2), (Sum.inr 3350, 1), (Sum.inr 3355, 2), (Sum.inr 3434, 2), (Sum.inr 3466, 1), (Sum.inr 3481, 2), (Sum.inr 3519, 2), (Sum.inr 3523, 2), (Sum.inr 3531, 1), (Sum.inr 3539, 1), (Sum.inr 3540, 2), (Sum.inr 3544, 2), (Sum.inr 3580, 1), (Sum.inr 3625, 1), (Sum.inr 3858, 1)]

theorem sourceEq94 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm94 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA94 + difference 0 1) (sourceB94 + difference 1 0) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA94 + difference 0 1) (sourceB94 + difference 1 0) sourceC94) = raw4170 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4170; decide +kernel
    rw [ha]
    exact (canonical4170 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA94 + difference 0 2) (sourceB94 + difference 2 0) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA94 + difference 0 2) (sourceB94 + difference 2 0) sourceC94) = raw4171 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4171; decide +kernel
    rw [ha]
    exact (canonical4171 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA94 + difference 0 3) (sourceB94 + difference 3 0) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA94 + difference 0 3) (sourceB94 + difference 3 0) sourceC94) = raw4172 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4172; decide +kernel
    rw [ha]
    exact (canonical4172 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA94 + difference 0 4) (sourceB94 + difference 4 0) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA94 + difference 0 4) (sourceB94 + difference 4 0) sourceC94) = raw4173 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4173; decide +kernel
    rw [ha]
    exact (canonical4173 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA94 + difference 0 5) (sourceB94 + difference 5 0) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA94 + difference 0 5) (sourceB94 + difference 5 0) sourceC94) = raw4174 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4174; decide +kernel
    rw [ha]
    exact (canonical4174 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA94 + difference 1 0) (sourceB94 + difference 0 1) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3283) := by
    have ha : (tripleCharges (sourceA94 + difference 1 0) (sourceB94 + difference 0 1) sourceC94) = raw4175 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4175; decide +kernel
    rw [ha]
    exact (canonical4175 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA94 + difference 1 2) (sourceB94 + difference 2 1) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3350) := by
    have ha : (tripleCharges (sourceA94 + difference 1 2) (sourceB94 + difference 2 1) sourceC94) = raw4176 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4176; decide +kernel
    rw [ha]
    exact (canonical4176 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA94 + difference 1 3) (sourceB94 + difference 3 1) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3355) := by
    have ha : (tripleCharges (sourceA94 + difference 1 3) (sourceB94 + difference 3 1) sourceC94) = raw4177 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4177; decide +kernel
    rw [ha]
    exact (canonical4177 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA94 + difference 1 4) (sourceB94 + difference 4 1) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3355) := by
    have ha : (tripleCharges (sourceA94 + difference 1 4) (sourceB94 + difference 4 1) sourceC94) = raw4178 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4178; decide +kernel
    rw [ha]
    exact (canonical4178 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA94 + difference 1 5) (sourceB94 + difference 5 1) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA94 + difference 1 5) (sourceB94 + difference 5 1) sourceC94) = raw4179 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4179; decide +kernel
    rw [ha]
    exact (canonical4179 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA94 + difference 2 0) (sourceB94 + difference 0 2) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3279) := by
    have ha : (tripleCharges (sourceA94 + difference 2 0) (sourceB94 + difference 0 2) sourceC94) = raw4180 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4180; decide +kernel
    rw [ha]
    exact (canonical4180 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA94 + difference 2 1) (sourceB94 + difference 1 2) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA94 + difference 2 1) (sourceB94 + difference 1 2) sourceC94) = raw4181 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4181; decide +kernel
    rw [ha]
    exact (canonical4181 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA94 + difference 2 3) (sourceB94 + difference 3 2) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA94 + difference 2 3) (sourceB94 + difference 3 2) sourceC94) = raw4182 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4182; decide +kernel
    rw [ha]
    exact (canonical4182 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA94 + difference 2 4) (sourceB94 + difference 4 2) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA94 + difference 2 4) (sourceB94 + difference 4 2) sourceC94) = raw4183 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4183; decide +kernel
    rw [ha]
    exact (canonical4183 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA94 + difference 2 5) (sourceB94 + difference 5 2) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA94 + difference 2 5) (sourceB94 + difference 5 2) sourceC94) = raw4184 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4184; decide +kernel
    rw [ha]
    exact (canonical4184 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA94 + difference 3 0) (sourceB94 + difference 0 3) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA94 + difference 3 0) (sourceB94 + difference 0 3) sourceC94) = raw4185 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4185; decide +kernel
    rw [ha]
    exact (canonical4185 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA94 + difference 3 1) (sourceB94 + difference 1 3) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA94 + difference 3 1) (sourceB94 + difference 1 3) sourceC94) = raw4186 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4186; decide +kernel
    rw [ha]
    exact (canonical4186 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA94 + difference 3 2) (sourceB94 + difference 2 3) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA94 + difference 3 2) (sourceB94 + difference 2 3) sourceC94) = raw4187 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4187; decide +kernel
    rw [ha]
    exact (canonical4187 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA94 + difference 3 4) (sourceB94 + difference 4 3) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA94 + difference 3 4) (sourceB94 + difference 4 3) sourceC94) = raw4188 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4188; decide +kernel
    rw [ha]
    exact (canonical4188 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA94 + difference 3 5) (sourceB94 + difference 5 3) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA94 + difference 3 5) (sourceB94 + difference 5 3) sourceC94) = raw4189 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4189; decide +kernel
    rw [ha]
    exact (canonical4189 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA94 + difference 4 0) (sourceB94 + difference 0 4) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA94 + difference 4 0) (sourceB94 + difference 0 4) sourceC94) = raw4190 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4190; decide +kernel
    rw [ha]
    exact (canonical4190 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA94 + difference 4 1) (sourceB94 + difference 1 4) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA94 + difference 4 1) (sourceB94 + difference 1 4) sourceC94) = raw4191 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4191; decide +kernel
    rw [ha]
    exact (canonical4191 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA94 + difference 4 2) (sourceB94 + difference 2 4) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA94 + difference 4 2) (sourceB94 + difference 2 4) sourceC94) = raw4192 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4192; decide +kernel
    rw [ha]
    exact (canonical4192 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA94 + difference 4 3) (sourceB94 + difference 3 4) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA94 + difference 4 3) (sourceB94 + difference 3 4) sourceC94) = raw4193 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4193; decide +kernel
    rw [ha]
    exact (canonical4193 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA94 + difference 4 5) (sourceB94 + difference 5 4) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA94 + difference 4 5) (sourceB94 + difference 5 4) sourceC94) = raw4194 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4194; decide +kernel
    rw [ha]
    exact (canonical4194 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA94 + difference 5 0) (sourceB94 + difference 0 5) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1615) := by
    have ha : (tripleCharges (sourceA94 + difference 5 0) (sourceB94 + difference 0 5) sourceC94) = raw4195 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4195; decide +kernel
    rw [ha]
    exact (canonical4195 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA94 + difference 5 1) (sourceB94 + difference 1 5) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA94 + difference 5 1) (sourceB94 + difference 1 5) sourceC94) = raw4196 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4196; decide +kernel
    rw [ha]
    exact (canonical4196 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA94 + difference 5 2) (sourceB94 + difference 2 5) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1613) := by
    have ha : (tripleCharges (sourceA94 + difference 5 2) (sourceB94 + difference 2 5) sourceC94) = raw4197 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4197; decide +kernel
    rw [ha]
    exact (canonical4197 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA94 + difference 5 3) (sourceB94 + difference 3 5) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA94 + difference 5 3) (sourceB94 + difference 3 5) sourceC94) = raw4198 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4198; decide +kernel
    rw [ha]
    exact (canonical4198 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA94 + difference 5 4) (sourceB94 + difference 4 5) sourceC94) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA94 + difference 5 4) (sourceB94 + difference 4 5) sourceC94) = raw4199 := by
      apply Matrix.ext; unfold tripleCharges sourceA94 sourceB94 sourceC94 difference raw4199; decide +kernel
    rw [ha]
    exact (canonical4199 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA94 sourceB94 sourceC94
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm94, Integer.Sparse.eval]
  linarith only [hs]

def sourceA95 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB95 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC95 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm95 : Integer.Sparse Master := [(Sum.inr 2712, 1), (Sum.inr 3064, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 2), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

theorem sourceEq95 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm95 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA95 + difference 0 0) (sourceB95 + difference 0 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA95 + difference 0 0) (sourceB95 + difference 0 0) sourceC95) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA95 + difference 0 1) (sourceB95 + difference 1 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA95 + difference 0 1) (sourceB95 + difference 1 0) sourceC95) = raw4201 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4201; decide +kernel
    rw [ha]
    exact (canonical4201 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA95 + difference 0 2) (sourceB95 + difference 2 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA95 + difference 0 2) (sourceB95 + difference 2 0) sourceC95) = raw4202 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4202; decide +kernel
    rw [ha]
    exact (canonical4202 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA95 + difference 0 3) (sourceB95 + difference 3 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA95 + difference 0 3) (sourceB95 + difference 3 0) sourceC95) = raw4203 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4203; decide +kernel
    rw [ha]
    exact (canonical4203 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA95 + difference 0 4) (sourceB95 + difference 4 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA95 + difference 0 4) (sourceB95 + difference 4 0) sourceC95) = raw4204 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4204; decide +kernel
    rw [ha]
    exact (canonical4204 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA95 + difference 0 5) (sourceB95 + difference 5 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA95 + difference 0 5) (sourceB95 + difference 5 0) sourceC95) = raw4205 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4205; decide +kernel
    rw [ha]
    exact (canonical4205 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA95 + sourceB95) sourceC95) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA95 + sourceB95) sourceC95) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA95 sourceB95 sourceC95 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA95 sourceB95 sourceC95
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm95, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
