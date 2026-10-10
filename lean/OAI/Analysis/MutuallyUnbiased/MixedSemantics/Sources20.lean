import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical88

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA640 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB640 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC640 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceForm640 : Integer.Sparse Master := [(Sum.inr 1057, 2), (Sum.inr 1059, 1), (Sum.inr 1063, 1), (Sum.inr 1083, 1), (Sum.inr 2278, 1), (Sum.inr 4084, -1)]

theorem sourceEq640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm640 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA640 + difference 0 0) (sourceB640 + difference 0 0) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA640 + difference 0 0) (sourceB640 + difference 0 0) sourceC640) = raw10889 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10889; decide +kernel
    rw [ha]
    exact (canonical10889 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA640 + difference 1 0) (sourceB640 + difference 0 1) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA640 + difference 1 0) (sourceB640 + difference 0 1) sourceC640) = raw10890 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10890; decide +kernel
    rw [ha]
    exact (canonical10890 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA640 + difference 2 0) (sourceB640 + difference 0 2) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA640 + difference 2 0) (sourceB640 + difference 0 2) sourceC640) = raw10891 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10891; decide +kernel
    rw [ha]
    exact (canonical10891 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA640 + difference 3 0) (sourceB640 + difference 0 3) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA640 + difference 3 0) (sourceB640 + difference 0 3) sourceC640) = raw10892 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10892; decide +kernel
    rw [ha]
    exact (canonical10892 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA640 + difference 4 0) (sourceB640 + difference 0 4) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA640 + difference 4 0) (sourceB640 + difference 0 4) sourceC640) = raw10893 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10893; decide +kernel
    rw [ha]
    exact (canonical10893 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA640 + difference 5 0) (sourceB640 + difference 0 5) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA640 + difference 5 0) (sourceB640 + difference 0 5) sourceC640) = raw10894 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10894; decide +kernel
    rw [ha]
    exact (canonical10894 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA640 + sourceB640) sourceC640) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA640 + sourceB640) sourceC640) = raw10895 := by
      apply Matrix.ext; unfold doubleCharges sourceA640 sourceB640 sourceC640 raw10895; decide +kernel
    rw [ha]
    exact (canonical10895 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA640 sourceB640 sourceC640
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm640, Integer.Sparse.eval]
  linarith only [hs]

def sourceA641 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB641 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC641 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceForm641 : Integer.Sparse Master := [(Sum.inr 1083, 1), (Sum.inr 2054, 2), (Sum.inr 2278, 1), (Sum.inr 2291, 1), (Sum.inr 2293, 1), (Sum.inr 4084, -1)]

theorem sourceEq641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm641 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA641 + difference 1 0) (sourceB641 + difference 0 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA641 + difference 1 0) (sourceB641 + difference 0 1) sourceC641) = raw10890 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10890; decide +kernel
    rw [ha]
    exact (canonical10890 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA641 + difference 1 1) (sourceB641 + difference 1 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA641 + difference 1 1) (sourceB641 + difference 1 1) sourceC641) = raw10889 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10889; decide +kernel
    rw [ha]
    exact (canonical10889 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA641 + difference 1 2) (sourceB641 + difference 2 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA641 + difference 1 2) (sourceB641 + difference 2 1) sourceC641) = raw10896 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10896; decide +kernel
    rw [ha]
    exact (canonical10896 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA641 + difference 1 3) (sourceB641 + difference 3 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA641 + difference 1 3) (sourceB641 + difference 3 1) sourceC641) = raw10897 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10897; decide +kernel
    rw [ha]
    exact (canonical10897 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA641 + difference 1 4) (sourceB641 + difference 4 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA641 + difference 1 4) (sourceB641 + difference 4 1) sourceC641) = raw10898 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10898; decide +kernel
    rw [ha]
    exact (canonical10898 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA641 + difference 1 5) (sourceB641 + difference 5 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA641 + difference 1 5) (sourceB641 + difference 5 1) sourceC641) = raw10899 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10899; decide +kernel
    rw [ha]
    exact (canonical10899 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA641 + sourceB641) sourceC641) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA641 + sourceB641) sourceC641) = raw10895 := by
      apply Matrix.ext; unfold doubleCharges sourceA641 sourceB641 sourceC641 raw10895; decide +kernel
    rw [ha]
    exact (canonical10895 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA641 sourceB641 sourceC641
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm641, Integer.Sparse.eval]
  linarith only [hs]

def sourceA642 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB642 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC642 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceForm642 : Integer.Sparse Master := [(Sum.inr 4268, 2), (Sum.inr 4270, 1), (Sum.inr 4272, 1), (Sum.inr 4279, 1), (Sum.inr 4740, 2), (Sum.inr 4742, 2), (Sum.inr 4744, 2), (Sum.inr 4750, 2), (Sum.inr 4839, 2), (Sum.inr 4843, 1), (Sum.inr 4845, 1), (Sum.inr 4866, 2), (Sum.inr 4868, 1), (Sum.inr 4875, 1), (Sum.inr 4889, 2), (Sum.inr 4890, 1), (Sum.inr 4896, 1), (Sum.inr 5411, 2), (Sum.inr 5443, 1), (Sum.inr 5451, 1), (Sum.inr 5453, 1)]

theorem sourceEq642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm642 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA642 + difference 0 1) (sourceB642 + difference 1 0) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA642 + difference 0 1) (sourceB642 + difference 1 0) sourceC642) = raw10900 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10900; decide +kernel
    rw [ha]
    exact (canonical10900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA642 + difference 0 2) (sourceB642 + difference 2 0) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA642 + difference 0 2) (sourceB642 + difference 2 0) sourceC642) = raw10901 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10901; decide +kernel
    rw [ha]
    exact (canonical10901 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA642 + difference 0 3) (sourceB642 + difference 3 0) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA642 + difference 0 3) (sourceB642 + difference 3 0) sourceC642) = raw10902 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10902; decide +kernel
    rw [ha]
    exact (canonical10902 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA642 + difference 0 4) (sourceB642 + difference 4 0) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA642 + difference 0 4) (sourceB642 + difference 4 0) sourceC642) = raw10903 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10903; decide +kernel
    rw [ha]
    exact (canonical10903 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA642 + difference 0 5) (sourceB642 + difference 5 0) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA642 + difference 0 5) (sourceB642 + difference 5 0) sourceC642) = raw10904 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10904; decide +kernel
    rw [ha]
    exact (canonical10904 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA642 + difference 1 0) (sourceB642 + difference 0 1) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA642 + difference 1 0) (sourceB642 + difference 0 1) sourceC642) = raw10905 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10905; decide +kernel
    rw [ha]
    exact (canonical10905 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA642 + difference 1 2) (sourceB642 + difference 2 1) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA642 + difference 1 2) (sourceB642 + difference 2 1) sourceC642) = raw10906 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10906; decide +kernel
    rw [ha]
    exact (canonical10906 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA642 + difference 1 3) (sourceB642 + difference 3 1) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA642 + difference 1 3) (sourceB642 + difference 3 1) sourceC642) = raw10907 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10907; decide +kernel
    rw [ha]
    exact (canonical10907 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA642 + difference 1 4) (sourceB642 + difference 4 1) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA642 + difference 1 4) (sourceB642 + difference 4 1) sourceC642) = raw10908 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10908; decide +kernel
    rw [ha]
    exact (canonical10908 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA642 + difference 1 5) (sourceB642 + difference 5 1) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA642 + difference 1 5) (sourceB642 + difference 5 1) sourceC642) = raw10909 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10909; decide +kernel
    rw [ha]
    exact (canonical10909 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA642 + difference 2 0) (sourceB642 + difference 0 2) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA642 + difference 2 0) (sourceB642 + difference 0 2) sourceC642) = raw10910 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10910; decide +kernel
    rw [ha]
    exact (canonical10910 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA642 + difference 2 1) (sourceB642 + difference 1 2) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA642 + difference 2 1) (sourceB642 + difference 1 2) sourceC642) = raw10911 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10911; decide +kernel
    rw [ha]
    exact (canonical10911 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA642 + difference 2 3) (sourceB642 + difference 3 2) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA642 + difference 2 3) (sourceB642 + difference 3 2) sourceC642) = raw10912 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10912; decide +kernel
    rw [ha]
    exact (canonical10912 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA642 + difference 2 4) (sourceB642 + difference 4 2) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA642 + difference 2 4) (sourceB642 + difference 4 2) sourceC642) = raw10913 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10913; decide +kernel
    rw [ha]
    exact (canonical10913 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA642 + difference 2 5) (sourceB642 + difference 5 2) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA642 + difference 2 5) (sourceB642 + difference 5 2) sourceC642) = raw10914 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10914; decide +kernel
    rw [ha]
    exact (canonical10914 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA642 + difference 3 0) (sourceB642 + difference 0 3) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA642 + difference 3 0) (sourceB642 + difference 0 3) sourceC642) = raw10915 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10915; decide +kernel
    rw [ha]
    exact (canonical10915 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA642 + difference 3 1) (sourceB642 + difference 1 3) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA642 + difference 3 1) (sourceB642 + difference 1 3) sourceC642) = raw10916 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10916; decide +kernel
    rw [ha]
    exact (canonical10916 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA642 + difference 3 2) (sourceB642 + difference 2 3) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA642 + difference 3 2) (sourceB642 + difference 2 3) sourceC642) = raw10917 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10917; decide +kernel
    rw [ha]
    exact (canonical10917 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA642 + difference 3 4) (sourceB642 + difference 4 3) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA642 + difference 3 4) (sourceB642 + difference 4 3) sourceC642) = raw10918 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10918; decide +kernel
    rw [ha]
    exact (canonical10918 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA642 + difference 3 5) (sourceB642 + difference 5 3) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA642 + difference 3 5) (sourceB642 + difference 5 3) sourceC642) = raw10919 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10919; decide +kernel
    rw [ha]
    exact (canonical10919 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA642 + difference 4 0) (sourceB642 + difference 0 4) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4279) := by
    have ha : (tripleCharges (sourceA642 + difference 4 0) (sourceB642 + difference 0 4) sourceC642) = raw10920 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10920; decide +kernel
    rw [ha]
    exact (canonical10920 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA642 + difference 4 1) (sourceB642 + difference 1 4) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA642 + difference 4 1) (sourceB642 + difference 1 4) sourceC642) = raw10921 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10921; decide +kernel
    rw [ha]
    exact (canonical10921 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA642 + difference 4 2) (sourceB642 + difference 2 4) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA642 + difference 4 2) (sourceB642 + difference 2 4) sourceC642) = raw10922 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10922; decide +kernel
    rw [ha]
    exact (canonical10922 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA642 + difference 4 3) (sourceB642 + difference 3 4) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA642 + difference 4 3) (sourceB642 + difference 3 4) sourceC642) = raw10923 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10923; decide +kernel
    rw [ha]
    exact (canonical10923 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA642 + difference 4 5) (sourceB642 + difference 5 4) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA642 + difference 4 5) (sourceB642 + difference 5 4) sourceC642) = raw10924 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10924; decide +kernel
    rw [ha]
    exact (canonical10924 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA642 + difference 5 0) (sourceB642 + difference 0 5) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA642 + difference 5 0) (sourceB642 + difference 0 5) sourceC642) = raw10925 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10925; decide +kernel
    rw [ha]
    exact (canonical10925 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA642 + difference 5 1) (sourceB642 + difference 1 5) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA642 + difference 5 1) (sourceB642 + difference 1 5) sourceC642) = raw10926 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10926; decide +kernel
    rw [ha]
    exact (canonical10926 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA642 + difference 5 2) (sourceB642 + difference 2 5) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA642 + difference 5 2) (sourceB642 + difference 2 5) sourceC642) = raw10927 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10927; decide +kernel
    rw [ha]
    exact (canonical10927 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA642 + difference 5 3) (sourceB642 + difference 3 5) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA642 + difference 5 3) (sourceB642 + difference 3 5) sourceC642) = raw10928 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10928; decide +kernel
    rw [ha]
    exact (canonical10928 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA642 + difference 5 4) (sourceB642 + difference 4 5) sourceC642) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA642 + difference 5 4) (sourceB642 + difference 4 5) sourceC642) = raw10929 := by
      apply Matrix.ext; unfold tripleCharges sourceA642 sourceB642 sourceC642 difference raw10929; decide +kernel
    rw [ha]
    exact (canonical10929 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA642 sourceB642 sourceC642
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm642, Integer.Sparse.eval]
  linarith only [hs]

def sourceA643 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB643 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC643 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceForm643 : Integer.Sparse Master := [(Sum.inr 824, 2), (Sum.inr 826, 1), (Sum.inr 831, 1), (Sum.inr 853, 1), (Sum.inr 1922, 2), (Sum.inr 1924, 2), (Sum.inr 1929, 2), (Sum.inr 1946, 2), (Sum.inr 2107, 2), (Sum.inr 2109, 1), (Sum.inr 2116, 1), (Sum.inr 2216, 2), (Sum.inr 2218, 1), (Sum.inr 2230, 1), (Sum.inr 2277, 2), (Sum.inr 2278, 1), (Sum.inr 2290, 1), (Sum.inr 3813, 2), (Sum.inr 3888, 1), (Sum.inr 3907, 1), (Sum.inr 3915, 1)]

theorem sourceEq643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm643 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA643 + difference 0 1) (sourceB643 + difference 1 0) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA643 + difference 0 1) (sourceB643 + difference 1 0) sourceC643) = raw10930 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10930; decide +kernel
    rw [ha]
    exact (canonical10930 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA643 + difference 0 2) (sourceB643 + difference 2 0) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA643 + difference 0 2) (sourceB643 + difference 2 0) sourceC643) = raw10931 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10931; decide +kernel
    rw [ha]
    exact (canonical10931 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA643 + difference 0 3) (sourceB643 + difference 3 0) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA643 + difference 0 3) (sourceB643 + difference 3 0) sourceC643) = raw10932 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10932; decide +kernel
    rw [ha]
    exact (canonical10932 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA643 + difference 0 4) (sourceB643 + difference 4 0) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA643 + difference 0 4) (sourceB643 + difference 4 0) sourceC643) = raw10933 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10933; decide +kernel
    rw [ha]
    exact (canonical10933 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA643 + difference 0 5) (sourceB643 + difference 5 0) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3915) := by
    have ha : (tripleCharges (sourceA643 + difference 0 5) (sourceB643 + difference 5 0) sourceC643) = raw10934 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10934; decide +kernel
    rw [ha]
    exact (canonical10934 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA643 + difference 1 0) (sourceB643 + difference 0 1) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 853) := by
    have ha : (tripleCharges (sourceA643 + difference 1 0) (sourceB643 + difference 0 1) sourceC643) = raw10935 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10935; decide +kernel
    rw [ha]
    exact (canonical10935 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA643 + difference 1 2) (sourceB643 + difference 2 1) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1946) := by
    have ha : (tripleCharges (sourceA643 + difference 1 2) (sourceB643 + difference 2 1) sourceC643) = raw10936 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10936; decide +kernel
    rw [ha]
    exact (canonical10936 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA643 + difference 1 3) (sourceB643 + difference 3 1) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1946) := by
    have ha : (tripleCharges (sourceA643 + difference 1 3) (sourceB643 + difference 3 1) sourceC643) = raw10937 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10937; decide +kernel
    rw [ha]
    exact (canonical10937 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA643 + difference 1 4) (sourceB643 + difference 4 1) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA643 + difference 1 4) (sourceB643 + difference 4 1) sourceC643) = raw10938 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10938; decide +kernel
    rw [ha]
    exact (canonical10938 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA643 + difference 1 5) (sourceB643 + difference 5 1) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA643 + difference 1 5) (sourceB643 + difference 5 1) sourceC643) = raw10939 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10939; decide +kernel
    rw [ha]
    exact (canonical10939 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA643 + difference 2 0) (sourceB643 + difference 0 2) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA643 + difference 2 0) (sourceB643 + difference 0 2) sourceC643) = raw10940 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10940; decide +kernel
    rw [ha]
    exact (canonical10940 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA643 + difference 2 1) (sourceB643 + difference 1 2) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA643 + difference 2 1) (sourceB643 + difference 1 2) sourceC643) = raw10941 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10941; decide +kernel
    rw [ha]
    exact (canonical10941 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA643 + difference 2 3) (sourceB643 + difference 3 2) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1922) := by
    have ha : (tripleCharges (sourceA643 + difference 2 3) (sourceB643 + difference 3 2) sourceC643) = raw10942 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10942; decide +kernel
    rw [ha]
    exact (canonical10942 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA643 + difference 2 4) (sourceB643 + difference 4 2) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA643 + difference 2 4) (sourceB643 + difference 4 2) sourceC643) = raw10943 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10943; decide +kernel
    rw [ha]
    exact (canonical10943 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA643 + difference 2 5) (sourceB643 + difference 5 2) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA643 + difference 2 5) (sourceB643 + difference 5 2) sourceC643) = raw10944 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10944; decide +kernel
    rw [ha]
    exact (canonical10944 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA643 + difference 3 0) (sourceB643 + difference 0 3) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA643 + difference 3 0) (sourceB643 + difference 0 3) sourceC643) = raw10945 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10945; decide +kernel
    rw [ha]
    exact (canonical10945 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA643 + difference 3 1) (sourceB643 + difference 1 3) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA643 + difference 3 1) (sourceB643 + difference 1 3) sourceC643) = raw10946 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10946; decide +kernel
    rw [ha]
    exact (canonical10946 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA643 + difference 3 2) (sourceB643 + difference 2 3) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1922) := by
    have ha : (tripleCharges (sourceA643 + difference 3 2) (sourceB643 + difference 2 3) sourceC643) = raw10947 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10947; decide +kernel
    rw [ha]
    exact (canonical10947 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA643 + difference 3 4) (sourceB643 + difference 4 3) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA643 + difference 3 4) (sourceB643 + difference 4 3) sourceC643) = raw10948 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10948; decide +kernel
    rw [ha]
    exact (canonical10948 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA643 + difference 3 5) (sourceB643 + difference 5 3) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA643 + difference 3 5) (sourceB643 + difference 5 3) sourceC643) = raw10949 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10949; decide +kernel
    rw [ha]
    exact (canonical10949 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA643 + difference 4 0) (sourceB643 + difference 0 4) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 831) := by
    have ha : (tripleCharges (sourceA643 + difference 4 0) (sourceB643 + difference 0 4) sourceC643) = raw10950 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10950; decide +kernel
    rw [ha]
    exact (canonical10950 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA643 + difference 4 1) (sourceB643 + difference 1 4) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA643 + difference 4 1) (sourceB643 + difference 1 4) sourceC643) = raw10951 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10951; decide +kernel
    rw [ha]
    exact (canonical10951 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA643 + difference 4 2) (sourceB643 + difference 2 4) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1929) := by
    have ha : (tripleCharges (sourceA643 + difference 4 2) (sourceB643 + difference 2 4) sourceC643) = raw10952 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10952; decide +kernel
    rw [ha]
    exact (canonical10952 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA643 + difference 4 3) (sourceB643 + difference 3 4) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1929) := by
    have ha : (tripleCharges (sourceA643 + difference 4 3) (sourceB643 + difference 3 4) sourceC643) = raw10953 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10953; decide +kernel
    rw [ha]
    exact (canonical10953 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA643 + difference 4 5) (sourceB643 + difference 5 4) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA643 + difference 4 5) (sourceB643 + difference 5 4) sourceC643) = raw10954 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10954; decide +kernel
    rw [ha]
    exact (canonical10954 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA643 + difference 5 0) (sourceB643 + difference 0 5) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA643 + difference 5 0) (sourceB643 + difference 0 5) sourceC643) = raw10955 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10955; decide +kernel
    rw [ha]
    exact (canonical10955 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA643 + difference 5 1) (sourceB643 + difference 1 5) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA643 + difference 5 1) (sourceB643 + difference 1 5) sourceC643) = raw10956 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10956; decide +kernel
    rw [ha]
    exact (canonical10956 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA643 + difference 5 2) (sourceB643 + difference 2 5) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA643 + difference 5 2) (sourceB643 + difference 2 5) sourceC643) = raw10957 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10957; decide +kernel
    rw [ha]
    exact (canonical10957 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA643 + difference 5 3) (sourceB643 + difference 3 5) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA643 + difference 5 3) (sourceB643 + difference 3 5) sourceC643) = raw10958 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10958; decide +kernel
    rw [ha]
    exact (canonical10958 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA643 + difference 5 4) (sourceB643 + difference 4 5) sourceC643) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA643 + difference 5 4) (sourceB643 + difference 4 5) sourceC643) = raw10959 := by
      apply Matrix.ext; unfold tripleCharges sourceA643 sourceB643 sourceC643 difference raw10959; decide +kernel
    rw [ha]
    exact (canonical10959 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA643 sourceB643 sourceC643
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm643, Integer.Sparse.eval]
  linarith only [hs]

def sourceA644 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB644 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC644 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm644 : Integer.Sparse Master := [(Sum.inr 4459, 2), (Sum.inr 4464, 1), (Sum.inr 4466, 1), (Sum.inr 4503, 1), (Sum.inr 4803, 2), (Sum.inr 4808, 2), (Sum.inr 4810, 2), (Sum.inr 4839, 2), (Sum.inr 4867, 2), (Sum.inr 4872, 1), (Sum.inr 4874, 1), (Sum.inr 4888, 2), (Sum.inr 4891, 2), (Sum.inr 4892, 1), (Sum.inr 4894, 1), (Sum.inr 4895, 1), (Sum.inr 4898, 1), (Sum.inr 5266, 2), (Sum.inr 5293, 1), (Sum.inr 5300, 1), (Sum.inr 5302, 1)]

theorem sourceEq644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm644 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA644 + difference 0 1) (sourceB644 + difference 1 0) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA644 + difference 0 1) (sourceB644 + difference 1 0) sourceC644) = raw7923 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw7923; decide +kernel
    rw [ha]
    exact (canonical7923 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA644 + difference 0 2) (sourceB644 + difference 2 0) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA644 + difference 0 2) (sourceB644 + difference 2 0) sourceC644) = raw10960 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10960; decide +kernel
    rw [ha]
    exact (canonical10960 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA644 + difference 0 3) (sourceB644 + difference 3 0) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA644 + difference 0 3) (sourceB644 + difference 3 0) sourceC644) = raw9899 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw9899; decide +kernel
    rw [ha]
    exact (canonical9899 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA644 + difference 0 4) (sourceB644 + difference 4 0) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA644 + difference 0 4) (sourceB644 + difference 4 0) sourceC644) = raw9661 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw9661; decide +kernel
    rw [ha]
    exact (canonical9661 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA644 + difference 0 5) (sourceB644 + difference 5 0) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA644 + difference 0 5) (sourceB644 + difference 5 0) sourceC644) = raw10961 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10961; decide +kernel
    rw [ha]
    exact (canonical10961 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA644 + difference 1 0) (sourceB644 + difference 0 1) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA644 + difference 1 0) (sourceB644 + difference 0 1) sourceC644) = raw10962 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10962; decide +kernel
    rw [ha]
    exact (canonical10962 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA644 + difference 1 2) (sourceB644 + difference 2 1) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA644 + difference 1 2) (sourceB644 + difference 2 1) sourceC644) = raw10963 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10963; decide +kernel
    rw [ha]
    exact (canonical10963 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA644 + difference 1 3) (sourceB644 + difference 3 1) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA644 + difference 1 3) (sourceB644 + difference 3 1) sourceC644) = raw10964 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10964; decide +kernel
    rw [ha]
    exact (canonical10964 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA644 + difference 1 4) (sourceB644 + difference 4 1) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4872) := by
    have ha : (tripleCharges (sourceA644 + difference 1 4) (sourceB644 + difference 4 1) sourceC644) = raw10965 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10965; decide +kernel
    rw [ha]
    exact (canonical10965 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA644 + difference 1 5) (sourceB644 + difference 5 1) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA644 + difference 1 5) (sourceB644 + difference 5 1) sourceC644) = raw10966 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10966; decide +kernel
    rw [ha]
    exact (canonical10966 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA644 + difference 2 0) (sourceB644 + difference 0 2) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA644 + difference 2 0) (sourceB644 + difference 0 2) sourceC644) = raw10967 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10967; decide +kernel
    rw [ha]
    exact (canonical10967 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA644 + difference 2 1) (sourceB644 + difference 1 2) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA644 + difference 2 1) (sourceB644 + difference 1 2) sourceC644) = raw5686 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw5686; decide +kernel
    rw [ha]
    exact (canonical5686 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA644 + difference 2 3) (sourceB644 + difference 3 2) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA644 + difference 2 3) (sourceB644 + difference 3 2) sourceC644) = raw10968 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10968; decide +kernel
    rw [ha]
    exact (canonical10968 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA644 + difference 2 4) (sourceB644 + difference 4 2) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA644 + difference 2 4) (sourceB644 + difference 4 2) sourceC644) = raw10969 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10969; decide +kernel
    rw [ha]
    exact (canonical10969 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA644 + difference 2 5) (sourceB644 + difference 5 2) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA644 + difference 2 5) (sourceB644 + difference 5 2) sourceC644) = raw5665 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw5665; decide +kernel
    rw [ha]
    exact (canonical5665 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA644 + difference 3 0) (sourceB644 + difference 0 3) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA644 + difference 3 0) (sourceB644 + difference 0 3) sourceC644) = raw10970 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10970; decide +kernel
    rw [ha]
    exact (canonical10970 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA644 + difference 3 1) (sourceB644 + difference 1 3) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA644 + difference 3 1) (sourceB644 + difference 1 3) sourceC644) = raw5685 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw5685; decide +kernel
    rw [ha]
    exact (canonical5685 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA644 + difference 3 2) (sourceB644 + difference 2 3) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA644 + difference 3 2) (sourceB644 + difference 2 3) sourceC644) = raw10971 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10971; decide +kernel
    rw [ha]
    exact (canonical10971 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA644 + difference 3 4) (sourceB644 + difference 4 3) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA644 + difference 3 4) (sourceB644 + difference 4 3) sourceC644) = raw10972 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10972; decide +kernel
    rw [ha]
    exact (canonical10972 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA644 + difference 3 5) (sourceB644 + difference 5 3) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA644 + difference 3 5) (sourceB644 + difference 5 3) sourceC644) = raw5664 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw5664; decide +kernel
    rw [ha]
    exact (canonical5664 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA644 + difference 4 0) (sourceB644 + difference 0 4) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA644 + difference 4 0) (sourceB644 + difference 0 4) sourceC644) = raw10973 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10973; decide +kernel
    rw [ha]
    exact (canonical10973 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA644 + difference 4 1) (sourceB644 + difference 1 4) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA644 + difference 4 1) (sourceB644 + difference 1 4) sourceC644) = raw9906 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw9906; decide +kernel
    rw [ha]
    exact (canonical9906 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA644 + difference 4 2) (sourceB644 + difference 2 4) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA644 + difference 4 2) (sourceB644 + difference 2 4) sourceC644) = raw10974 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10974; decide +kernel
    rw [ha]
    exact (canonical10974 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA644 + difference 4 3) (sourceB644 + difference 3 4) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA644 + difference 4 3) (sourceB644 + difference 3 4) sourceC644) = raw9896 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw9896; decide +kernel
    rw [ha]
    exact (canonical9896 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA644 + difference 4 5) (sourceB644 + difference 5 4) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA644 + difference 4 5) (sourceB644 + difference 5 4) sourceC644) = raw10975 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10975; decide +kernel
    rw [ha]
    exact (canonical10975 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA644 + difference 5 0) (sourceB644 + difference 0 5) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA644 + difference 5 0) (sourceB644 + difference 0 5) sourceC644) = raw10976 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10976; decide +kernel
    rw [ha]
    exact (canonical10976 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA644 + difference 5 1) (sourceB644 + difference 1 5) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA644 + difference 5 1) (sourceB644 + difference 1 5) sourceC644) = raw9668 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw9668; decide +kernel
    rw [ha]
    exact (canonical9668 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA644 + difference 5 2) (sourceB644 + difference 2 5) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA644 + difference 5 2) (sourceB644 + difference 2 5) sourceC644) = raw10977 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10977; decide +kernel
    rw [ha]
    exact (canonical10977 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA644 + difference 5 3) (sourceB644 + difference 3 5) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA644 + difference 5 3) (sourceB644 + difference 3 5) sourceC644) = raw10148 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw10148; decide +kernel
    rw [ha]
    exact (canonical10148 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA644 + difference 5 4) (sourceB644 + difference 4 5) sourceC644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA644 + difference 5 4) (sourceB644 + difference 4 5) sourceC644) = raw9657 := by
      apply Matrix.ext; unfold tripleCharges sourceA644 sourceB644 sourceC644 difference raw9657; decide +kernel
    rw [ha]
    exact (canonical9657 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA644 sourceB644 sourceC644
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm644, Integer.Sparse.eval]
  linarith only [hs]

def sourceA645 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB645 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC645 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm645 : Integer.Sparse Master := [(Sum.inr 1714, 2), (Sum.inr 1738, 1), (Sum.inr 1739, 1), (Sum.inr 1745, 1), (Sum.inr 2195, 2), (Sum.inr 2215, 2), (Sum.inr 2216, 2), (Sum.inr 2220, 2), (Sum.inr 2244, 2), (Sum.inr 2251, 2), (Sum.inr 2253, 2), (Sum.inr 2264, 1), (Sum.inr 2265, 1), (Sum.inr 2276, 1), (Sum.inr 2279, 1), (Sum.inr 2282, 1), (Sum.inr 2284, 1), (Sum.inr 2731, 2), (Sum.inr 2767, 1), (Sum.inr 2774, 1), (Sum.inr 2776, 1)]

theorem sourceEq645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm645 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA645 + difference 0 1) (sourceB645 + difference 1 0) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA645 + difference 0 1) (sourceB645 + difference 1 0) sourceC645) = raw7936 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw7936; decide +kernel
    rw [ha]
    exact (canonical7936 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA645 + difference 0 2) (sourceB645 + difference 2 0) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA645 + difference 0 2) (sourceB645 + difference 2 0) sourceC645) = raw10978 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10978; decide +kernel
    rw [ha]
    exact (canonical10978 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA645 + difference 0 3) (sourceB645 + difference 3 0) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA645 + difference 0 3) (sourceB645 + difference 3 0) sourceC645) = raw9923 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw9923; decide +kernel
    rw [ha]
    exact (canonical9923 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA645 + difference 0 4) (sourceB645 + difference 4 0) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA645 + difference 0 4) (sourceB645 + difference 4 0) sourceC645) = raw9685 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw9685; decide +kernel
    rw [ha]
    exact (canonical9685 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA645 + difference 0 5) (sourceB645 + difference 5 0) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA645 + difference 0 5) (sourceB645 + difference 5 0) sourceC645) = raw10979 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10979; decide +kernel
    rw [ha]
    exact (canonical10979 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA645 + difference 1 0) (sourceB645 + difference 0 1) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA645 + difference 1 0) (sourceB645 + difference 0 1) sourceC645) = raw10980 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10980; decide +kernel
    rw [ha]
    exact (canonical10980 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA645 + difference 1 2) (sourceB645 + difference 2 1) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA645 + difference 1 2) (sourceB645 + difference 2 1) sourceC645) = raw10981 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10981; decide +kernel
    rw [ha]
    exact (canonical10981 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA645 + difference 1 3) (sourceB645 + difference 3 1) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA645 + difference 1 3) (sourceB645 + difference 3 1) sourceC645) = raw10982 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10982; decide +kernel
    rw [ha]
    exact (canonical10982 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA645 + difference 1 4) (sourceB645 + difference 4 1) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2282) := by
    have ha : (tripleCharges (sourceA645 + difference 1 4) (sourceB645 + difference 4 1) sourceC645) = raw10983 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10983; decide +kernel
    rw [ha]
    exact (canonical10983 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA645 + difference 1 5) (sourceB645 + difference 5 1) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA645 + difference 1 5) (sourceB645 + difference 5 1) sourceC645) = raw10984 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10984; decide +kernel
    rw [ha]
    exact (canonical10984 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA645 + difference 2 0) (sourceB645 + difference 0 2) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA645 + difference 2 0) (sourceB645 + difference 0 2) sourceC645) = raw10985 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10985; decide +kernel
    rw [ha]
    exact (canonical10985 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA645 + difference 2 1) (sourceB645 + difference 1 2) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA645 + difference 2 1) (sourceB645 + difference 1 2) sourceC645) = raw5716 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw5716; decide +kernel
    rw [ha]
    exact (canonical5716 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA645 + difference 2 3) (sourceB645 + difference 3 2) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA645 + difference 2 3) (sourceB645 + difference 3 2) sourceC645) = raw10986 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10986; decide +kernel
    rw [ha]
    exact (canonical10986 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA645 + difference 2 4) (sourceB645 + difference 4 2) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA645 + difference 2 4) (sourceB645 + difference 4 2) sourceC645) = raw10987 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10987; decide +kernel
    rw [ha]
    exact (canonical10987 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA645 + difference 2 5) (sourceB645 + difference 5 2) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA645 + difference 2 5) (sourceB645 + difference 5 2) sourceC645) = raw5695 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw5695; decide +kernel
    rw [ha]
    exact (canonical5695 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA645 + difference 3 0) (sourceB645 + difference 0 3) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA645 + difference 3 0) (sourceB645 + difference 0 3) sourceC645) = raw10988 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10988; decide +kernel
    rw [ha]
    exact (canonical10988 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA645 + difference 3 1) (sourceB645 + difference 1 3) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA645 + difference 3 1) (sourceB645 + difference 1 3) sourceC645) = raw5715 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw5715; decide +kernel
    rw [ha]
    exact (canonical5715 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA645 + difference 3 2) (sourceB645 + difference 2 3) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA645 + difference 3 2) (sourceB645 + difference 2 3) sourceC645) = raw10989 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10989; decide +kernel
    rw [ha]
    exact (canonical10989 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA645 + difference 3 4) (sourceB645 + difference 4 3) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA645 + difference 3 4) (sourceB645 + difference 4 3) sourceC645) = raw10990 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10990; decide +kernel
    rw [ha]
    exact (canonical10990 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA645 + difference 3 5) (sourceB645 + difference 5 3) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA645 + difference 3 5) (sourceB645 + difference 5 3) sourceC645) = raw5694 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw5694; decide +kernel
    rw [ha]
    exact (canonical5694 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA645 + difference 4 0) (sourceB645 + difference 0 4) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA645 + difference 4 0) (sourceB645 + difference 0 4) sourceC645) = raw10991 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10991; decide +kernel
    rw [ha]
    exact (canonical10991 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA645 + difference 4 1) (sourceB645 + difference 1 4) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA645 + difference 4 1) (sourceB645 + difference 1 4) sourceC645) = raw9930 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw9930; decide +kernel
    rw [ha]
    exact (canonical9930 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA645 + difference 4 2) (sourceB645 + difference 2 4) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA645 + difference 4 2) (sourceB645 + difference 2 4) sourceC645) = raw10992 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10992; decide +kernel
    rw [ha]
    exact (canonical10992 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA645 + difference 4 3) (sourceB645 + difference 3 4) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA645 + difference 4 3) (sourceB645 + difference 3 4) sourceC645) = raw9920 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw9920; decide +kernel
    rw [ha]
    exact (canonical9920 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA645 + difference 4 5) (sourceB645 + difference 5 4) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA645 + difference 4 5) (sourceB645 + difference 5 4) sourceC645) = raw10993 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10993; decide +kernel
    rw [ha]
    exact (canonical10993 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA645 + difference 5 0) (sourceB645 + difference 0 5) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA645 + difference 5 0) (sourceB645 + difference 0 5) sourceC645) = raw10994 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10994; decide +kernel
    rw [ha]
    exact (canonical10994 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA645 + difference 5 1) (sourceB645 + difference 1 5) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA645 + difference 5 1) (sourceB645 + difference 1 5) sourceC645) = raw9692 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw9692; decide +kernel
    rw [ha]
    exact (canonical9692 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA645 + difference 5 2) (sourceB645 + difference 2 5) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA645 + difference 5 2) (sourceB645 + difference 2 5) sourceC645) = raw10995 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10995; decide +kernel
    rw [ha]
    exact (canonical10995 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA645 + difference 5 3) (sourceB645 + difference 3 5) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA645 + difference 5 3) (sourceB645 + difference 3 5) sourceC645) = raw10163 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw10163; decide +kernel
    rw [ha]
    exact (canonical10163 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA645 + difference 5 4) (sourceB645 + difference 4 5) sourceC645) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA645 + difference 5 4) (sourceB645 + difference 4 5) sourceC645) = raw9681 := by
      apply Matrix.ext; unfold tripleCharges sourceA645 sourceB645 sourceC645 difference raw9681; decide +kernel
    rw [ha]
    exact (canonical9681 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA645 sourceB645 sourceC645
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm645, Integer.Sparse.eval]
  linarith only [hs]

def sourceA646 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB646 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC646 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm646 : Integer.Sparse Master := [(Sum.inr 1406, 2), (Sum.inr 1408, 1), (Sum.inr 1419, 1), (Sum.inr 1442, 1), (Sum.inr 2092, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 3039, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3102, 1), (Sum.inr 3180, 2), (Sum.inr 3187, 1), (Sum.inr 3202, 2), (Sum.inr 3206, 2), (Sum.inr 3210, 2), (Sum.inr 3222, 2), (Sum.inr 3224, 1), (Sum.inr 3227, 2), (Sum.inr 3229, 1), (Sum.inr 3230, 1)]

theorem sourceEq646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm646 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA646 + difference 0 1) (sourceB646 + difference 1 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA646 + difference 0 1) (sourceB646 + difference 1 0) sourceC646) = raw7949 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw7949; decide +kernel
    rw [ha]
    exact (canonical7949 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA646 + difference 0 2) (sourceB646 + difference 2 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA646 + difference 0 2) (sourceB646 + difference 2 0) sourceC646) = raw10996 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10996; decide +kernel
    rw [ha]
    exact (canonical10996 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA646 + difference 0 3) (sourceB646 + difference 3 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA646 + difference 0 3) (sourceB646 + difference 3 0) sourceC646) = raw9947 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9947; decide +kernel
    rw [ha]
    exact (canonical9947 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA646 + difference 0 4) (sourceB646 + difference 4 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA646 + difference 0 4) (sourceB646 + difference 4 0) sourceC646) = raw9709 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9709; decide +kernel
    rw [ha]
    exact (canonical9709 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA646 + difference 0 5) (sourceB646 + difference 5 0) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA646 + difference 0 5) (sourceB646 + difference 5 0) sourceC646) = raw10997 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10997; decide +kernel
    rw [ha]
    exact (canonical10997 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA646 + difference 1 0) (sourceB646 + difference 0 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA646 + difference 1 0) (sourceB646 + difference 0 1) sourceC646) = raw10998 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10998; decide +kernel
    rw [ha]
    exact (canonical10998 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA646 + difference 1 2) (sourceB646 + difference 2 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA646 + difference 1 2) (sourceB646 + difference 2 1) sourceC646) = raw10999 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10999; decide +kernel
    rw [ha]
    exact (canonical10999 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA646 + difference 1 3) (sourceB646 + difference 3 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA646 + difference 1 3) (sourceB646 + difference 3 1) sourceC646) = raw11000 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11000; decide +kernel
    rw [ha]
    exact (canonical11000 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA646 + difference 1 4) (sourceB646 + difference 4 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA646 + difference 1 4) (sourceB646 + difference 4 1) sourceC646) = raw11001 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11001; decide +kernel
    rw [ha]
    exact (canonical11001 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA646 + difference 1 5) (sourceB646 + difference 5 1) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA646 + difference 1 5) (sourceB646 + difference 5 1) sourceC646) = raw11002 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11002; decide +kernel
    rw [ha]
    exact (canonical11002 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA646 + difference 2 0) (sourceB646 + difference 0 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA646 + difference 2 0) (sourceB646 + difference 0 2) sourceC646) = raw11003 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11003; decide +kernel
    rw [ha]
    exact (canonical11003 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA646 + difference 2 1) (sourceB646 + difference 1 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA646 + difference 2 1) (sourceB646 + difference 1 2) sourceC646) = raw5746 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw5746; decide +kernel
    rw [ha]
    exact (canonical5746 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA646 + difference 2 3) (sourceB646 + difference 3 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA646 + difference 2 3) (sourceB646 + difference 3 2) sourceC646) = raw11004 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11004; decide +kernel
    rw [ha]
    exact (canonical11004 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA646 + difference 2 4) (sourceB646 + difference 4 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA646 + difference 2 4) (sourceB646 + difference 4 2) sourceC646) = raw11005 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11005; decide +kernel
    rw [ha]
    exact (canonical11005 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA646 + difference 2 5) (sourceB646 + difference 5 2) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA646 + difference 2 5) (sourceB646 + difference 5 2) sourceC646) = raw5725 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw5725; decide +kernel
    rw [ha]
    exact (canonical5725 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA646 + difference 3 0) (sourceB646 + difference 0 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA646 + difference 3 0) (sourceB646 + difference 0 3) sourceC646) = raw11006 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11006; decide +kernel
    rw [ha]
    exact (canonical11006 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA646 + difference 3 1) (sourceB646 + difference 1 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA646 + difference 3 1) (sourceB646 + difference 1 3) sourceC646) = raw5745 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw5745; decide +kernel
    rw [ha]
    exact (canonical5745 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA646 + difference 3 2) (sourceB646 + difference 2 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA646 + difference 3 2) (sourceB646 + difference 2 3) sourceC646) = raw11007 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11007; decide +kernel
    rw [ha]
    exact (canonical11007 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA646 + difference 3 4) (sourceB646 + difference 4 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA646 + difference 3 4) (sourceB646 + difference 4 3) sourceC646) = raw11008 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11008; decide +kernel
    rw [ha]
    exact (canonical11008 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA646 + difference 3 5) (sourceB646 + difference 5 3) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA646 + difference 3 5) (sourceB646 + difference 5 3) sourceC646) = raw5724 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw5724; decide +kernel
    rw [ha]
    exact (canonical5724 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA646 + difference 4 0) (sourceB646 + difference 0 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1442) := by
    have ha : (tripleCharges (sourceA646 + difference 4 0) (sourceB646 + difference 0 4) sourceC646) = raw11009 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11009; decide +kernel
    rw [ha]
    exact (canonical11009 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA646 + difference 4 1) (sourceB646 + difference 1 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA646 + difference 4 1) (sourceB646 + difference 1 4) sourceC646) = raw9954 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9954; decide +kernel
    rw [ha]
    exact (canonical9954 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA646 + difference 4 2) (sourceB646 + difference 2 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3210) := by
    have ha : (tripleCharges (sourceA646 + difference 4 2) (sourceB646 + difference 2 4) sourceC646) = raw11010 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11010; decide +kernel
    rw [ha]
    exact (canonical11010 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA646 + difference 4 3) (sourceB646 + difference 3 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3210) := by
    have ha : (tripleCharges (sourceA646 + difference 4 3) (sourceB646 + difference 3 4) sourceC646) = raw9944 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9944; decide +kernel
    rw [ha]
    exact (canonical9944 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA646 + difference 4 5) (sourceB646 + difference 5 4) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA646 + difference 4 5) (sourceB646 + difference 5 4) sourceC646) = raw11011 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11011; decide +kernel
    rw [ha]
    exact (canonical11011 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA646 + difference 5 0) (sourceB646 + difference 0 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA646 + difference 5 0) (sourceB646 + difference 0 5) sourceC646) = raw11012 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11012; decide +kernel
    rw [ha]
    exact (canonical11012 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA646 + difference 5 1) (sourceB646 + difference 1 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA646 + difference 5 1) (sourceB646 + difference 1 5) sourceC646) = raw9716 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9716; decide +kernel
    rw [ha]
    exact (canonical9716 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA646 + difference 5 2) (sourceB646 + difference 2 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA646 + difference 5 2) (sourceB646 + difference 2 5) sourceC646) = raw11013 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw11013; decide +kernel
    rw [ha]
    exact (canonical11013 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA646 + difference 5 3) (sourceB646 + difference 3 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA646 + difference 5 3) (sourceB646 + difference 3 5) sourceC646) = raw10178 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw10178; decide +kernel
    rw [ha]
    exact (canonical10178 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA646 + difference 5 4) (sourceB646 + difference 4 5) sourceC646) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA646 + difference 5 4) (sourceB646 + difference 4 5) sourceC646) = raw9705 := by
      apply Matrix.ext; unfold tripleCharges sourceA646 sourceB646 sourceC646 difference raw9705; decide +kernel
    rw [ha]
    exact (canonical9705 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA646 sourceB646 sourceC646
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm646, Integer.Sparse.eval]
  linarith only [hs]

def sourceA647 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB647 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC647 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm647 : Integer.Sparse Master := [(Sum.inr 1042, 2), (Sum.inr 1047, 1), (Sum.inr 1049, 1), (Sum.inr 1087, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

theorem sourceEq647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm647 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA647 + difference 0 0) (sourceB647 + difference 0 0) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA647 + difference 0 0) (sourceB647 + difference 0 0) sourceC647) = raw11014 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11014; decide +kernel
    rw [ha]
    exact (canonical11014 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA647 + difference 1 0) (sourceB647 + difference 0 1) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA647 + difference 1 0) (sourceB647 + difference 0 1) sourceC647) = raw11015 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11015; decide +kernel
    rw [ha]
    exact (canonical11015 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA647 + difference 2 0) (sourceB647 + difference 0 2) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA647 + difference 2 0) (sourceB647 + difference 0 2) sourceC647) = raw11016 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11016; decide +kernel
    rw [ha]
    exact (canonical11016 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA647 + difference 3 0) (sourceB647 + difference 0 3) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA647 + difference 3 0) (sourceB647 + difference 0 3) sourceC647) = raw11017 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11017; decide +kernel
    rw [ha]
    exact (canonical11017 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA647 + difference 4 0) (sourceB647 + difference 0 4) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA647 + difference 4 0) (sourceB647 + difference 0 4) sourceC647) = raw11018 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11018; decide +kernel
    rw [ha]
    exact (canonical11018 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA647 + difference 5 0) (sourceB647 + difference 0 5) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA647 + difference 5 0) (sourceB647 + difference 0 5) sourceC647) = raw11019 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11019; decide +kernel
    rw [ha]
    exact (canonical11019 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA647 + sourceB647) sourceC647) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA647 + sourceB647) sourceC647) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA647 sourceB647 sourceC647 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA647 sourceB647 sourceC647
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm647, Integer.Sparse.eval]
  linarith only [hs]

def sourceA648 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB648 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC648 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceForm648 : Integer.Sparse Master := [(Sum.inr 4439, 1), (Sum.inr 4442, 1), (Sum.inr 4444, 1), (Sum.inr 4461, 2), (Sum.inr 4793, 1), (Sum.inr 4795, 1), (Sum.inr 4805, 2), (Sum.inr 4808, 2), (Sum.inr 4852, 2), (Sum.inr 4856, 2), (Sum.inr 4869, 2), (Sum.inr 4885, 1), (Sum.inr 4886, 1), (Sum.inr 4887, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 2), (Sum.inr 4893, 2), (Sum.inr 5265, 1), (Sum.inr 5292, 1), (Sum.inr 5299, 2), (Sum.inr 5301, 1)]

theorem sourceEq648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm648 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA648 + difference 0 1) (sourceB648 + difference 1 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA648 + difference 0 1) (sourceB648 + difference 1 0) sourceC648) = raw11020 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11020; decide +kernel
    rw [ha]
    exact (canonical11020 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA648 + difference 0 2) (sourceB648 + difference 2 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA648 + difference 0 2) (sourceB648 + difference 2 0) sourceC648) = raw11021 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11021; decide +kernel
    rw [ha]
    exact (canonical11021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA648 + difference 0 3) (sourceB648 + difference 3 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA648 + difference 0 3) (sourceB648 + difference 3 0) sourceC648) = raw11022 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11022; decide +kernel
    rw [ha]
    exact (canonical11022 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA648 + difference 0 4) (sourceB648 + difference 4 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA648 + difference 0 4) (sourceB648 + difference 4 0) sourceC648) = raw11023 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11023; decide +kernel
    rw [ha]
    exact (canonical11023 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA648 + difference 0 5) (sourceB648 + difference 5 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA648 + difference 0 5) (sourceB648 + difference 5 0) sourceC648) = raw11024 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11024; decide +kernel
    rw [ha]
    exact (canonical11024 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA648 + difference 1 0) (sourceB648 + difference 0 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA648 + difference 1 0) (sourceB648 + difference 0 1) sourceC648) = raw11025 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11025; decide +kernel
    rw [ha]
    exact (canonical11025 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA648 + difference 1 2) (sourceB648 + difference 2 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA648 + difference 1 2) (sourceB648 + difference 2 1) sourceC648) = raw11026 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11026; decide +kernel
    rw [ha]
    exact (canonical11026 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA648 + difference 1 3) (sourceB648 + difference 3 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA648 + difference 1 3) (sourceB648 + difference 3 1) sourceC648) = raw11027 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11027; decide +kernel
    rw [ha]
    exact (canonical11027 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA648 + difference 1 4) (sourceB648 + difference 4 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA648 + difference 1 4) (sourceB648 + difference 4 1) sourceC648) = raw11028 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11028; decide +kernel
    rw [ha]
    exact (canonical11028 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA648 + difference 1 5) (sourceB648 + difference 5 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA648 + difference 1 5) (sourceB648 + difference 5 1) sourceC648) = raw11029 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11029; decide +kernel
    rw [ha]
    exact (canonical11029 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA648 + difference 2 0) (sourceB648 + difference 0 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA648 + difference 2 0) (sourceB648 + difference 0 2) sourceC648) = raw11030 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11030; decide +kernel
    rw [ha]
    exact (canonical11030 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA648 + difference 2 1) (sourceB648 + difference 1 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA648 + difference 2 1) (sourceB648 + difference 1 2) sourceC648) = raw11031 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11031; decide +kernel
    rw [ha]
    exact (canonical11031 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA648 + difference 2 3) (sourceB648 + difference 3 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA648 + difference 2 3) (sourceB648 + difference 3 2) sourceC648) = raw11032 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11032; decide +kernel
    rw [ha]
    exact (canonical11032 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA648 + difference 2 4) (sourceB648 + difference 4 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA648 + difference 2 4) (sourceB648 + difference 4 2) sourceC648) = raw11033 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11033; decide +kernel
    rw [ha]
    exact (canonical11033 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA648 + difference 2 5) (sourceB648 + difference 5 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA648 + difference 2 5) (sourceB648 + difference 5 2) sourceC648) = raw11034 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11034; decide +kernel
    rw [ha]
    exact (canonical11034 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA648 + difference 3 0) (sourceB648 + difference 0 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA648 + difference 3 0) (sourceB648 + difference 0 3) sourceC648) = raw11035 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11035; decide +kernel
    rw [ha]
    exact (canonical11035 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA648 + difference 3 1) (sourceB648 + difference 1 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA648 + difference 3 1) (sourceB648 + difference 1 3) sourceC648) = raw11036 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11036; decide +kernel
    rw [ha]
    exact (canonical11036 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA648 + difference 3 2) (sourceB648 + difference 2 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA648 + difference 3 2) (sourceB648 + difference 2 3) sourceC648) = raw11037 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11037; decide +kernel
    rw [ha]
    exact (canonical11037 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA648 + difference 3 4) (sourceB648 + difference 4 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA648 + difference 3 4) (sourceB648 + difference 4 3) sourceC648) = raw11038 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11038; decide +kernel
    rw [ha]
    exact (canonical11038 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA648 + difference 3 5) (sourceB648 + difference 5 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA648 + difference 3 5) (sourceB648 + difference 5 3) sourceC648) = raw11039 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11039; decide +kernel
    rw [ha]
    exact (canonical11039 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA648 + difference 4 0) (sourceB648 + difference 0 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA648 + difference 4 0) (sourceB648 + difference 0 4) sourceC648) = raw11040 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11040; decide +kernel
    rw [ha]
    exact (canonical11040 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA648 + difference 4 1) (sourceB648 + difference 1 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA648 + difference 4 1) (sourceB648 + difference 1 4) sourceC648) = raw11041 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11041; decide +kernel
    rw [ha]
    exact (canonical11041 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA648 + difference 4 2) (sourceB648 + difference 2 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA648 + difference 4 2) (sourceB648 + difference 2 4) sourceC648) = raw11042 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11042; decide +kernel
    rw [ha]
    exact (canonical11042 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA648 + difference 4 3) (sourceB648 + difference 3 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA648 + difference 4 3) (sourceB648 + difference 3 4) sourceC648) = raw11043 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11043; decide +kernel
    rw [ha]
    exact (canonical11043 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA648 + difference 4 5) (sourceB648 + difference 5 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA648 + difference 4 5) (sourceB648 + difference 5 4) sourceC648) = raw11044 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11044; decide +kernel
    rw [ha]
    exact (canonical11044 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA648 + difference 5 0) (sourceB648 + difference 0 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA648 + difference 5 0) (sourceB648 + difference 0 5) sourceC648) = raw11045 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11045; decide +kernel
    rw [ha]
    exact (canonical11045 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA648 + difference 5 1) (sourceB648 + difference 1 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA648 + difference 5 1) (sourceB648 + difference 1 5) sourceC648) = raw11046 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11046; decide +kernel
    rw [ha]
    exact (canonical11046 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA648 + difference 5 2) (sourceB648 + difference 2 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA648 + difference 5 2) (sourceB648 + difference 2 5) sourceC648) = raw11047 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11047; decide +kernel
    rw [ha]
    exact (canonical11047 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA648 + difference 5 3) (sourceB648 + difference 3 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA648 + difference 5 3) (sourceB648 + difference 3 5) sourceC648) = raw11048 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11048; decide +kernel
    rw [ha]
    exact (canonical11048 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA648 + difference 5 4) (sourceB648 + difference 4 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA648 + difference 5 4) (sourceB648 + difference 4 5) sourceC648) = raw11049 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11049; decide +kernel
    rw [ha]
    exact (canonical11049 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA648 sourceB648 sourceC648
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm648, Integer.Sparse.eval]
  linarith only [hs]

def sourceA649 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB649 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC649 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceForm649 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 1736, 1), (Sum.inr 1737, 2), (Sum.inr 1744, 1), (Sum.inr 2213, 1), (Sum.inr 2214, 2), (Sum.inr 2219, 1), (Sum.inr 2220, 2), (Sum.inr 2243, 1), (Sum.inr 2250, 2), (Sum.inr 2252, 1), (Sum.inr 2262, 1), (Sum.inr 2263, 2), (Sum.inr 2274, 2), (Sum.inr 2275, 2), (Sum.inr 2277, 2), (Sum.inr 2283, 1), (Sum.inr 2730, 1), (Sum.inr 2766, 1), (Sum.inr 2773, 2), (Sum.inr 2775, 1)]

theorem sourceEq649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm649 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA649 + difference 0 1) (sourceB649 + difference 1 0) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA649 + difference 0 1) (sourceB649 + difference 1 0) sourceC649) = raw11050 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11050; decide +kernel
    rw [ha]
    exact (canonical11050 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA649 + difference 0 2) (sourceB649 + difference 2 0) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA649 + difference 0 2) (sourceB649 + difference 2 0) sourceC649) = raw11051 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11051; decide +kernel
    rw [ha]
    exact (canonical11051 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA649 + difference 0 3) (sourceB649 + difference 3 0) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA649 + difference 0 3) (sourceB649 + difference 3 0) sourceC649) = raw11052 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11052; decide +kernel
    rw [ha]
    exact (canonical11052 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA649 + difference 0 4) (sourceB649 + difference 4 0) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2775) := by
    have ha : (tripleCharges (sourceA649 + difference 0 4) (sourceB649 + difference 4 0) sourceC649) = raw11053 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11053; decide +kernel
    rw [ha]
    exact (canonical11053 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA649 + difference 0 5) (sourceB649 + difference 5 0) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA649 + difference 0 5) (sourceB649 + difference 5 0) sourceC649) = raw11054 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11054; decide +kernel
    rw [ha]
    exact (canonical11054 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA649 + difference 1 0) (sourceB649 + difference 0 1) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA649 + difference 1 0) (sourceB649 + difference 0 1) sourceC649) = raw11055 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11055; decide +kernel
    rw [ha]
    exact (canonical11055 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA649 + difference 1 2) (sourceB649 + difference 2 1) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA649 + difference 1 2) (sourceB649 + difference 2 1) sourceC649) = raw11056 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11056; decide +kernel
    rw [ha]
    exact (canonical11056 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA649 + difference 1 3) (sourceB649 + difference 3 1) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA649 + difference 1 3) (sourceB649 + difference 3 1) sourceC649) = raw11057 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11057; decide +kernel
    rw [ha]
    exact (canonical11057 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA649 + difference 1 4) (sourceB649 + difference 4 1) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA649 + difference 1 4) (sourceB649 + difference 4 1) sourceC649) = raw11058 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11058; decide +kernel
    rw [ha]
    exact (canonical11058 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA649 + difference 1 5) (sourceB649 + difference 5 1) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA649 + difference 1 5) (sourceB649 + difference 5 1) sourceC649) = raw11059 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11059; decide +kernel
    rw [ha]
    exact (canonical11059 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA649 + difference 2 0) (sourceB649 + difference 0 2) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA649 + difference 2 0) (sourceB649 + difference 0 2) sourceC649) = raw11060 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11060; decide +kernel
    rw [ha]
    exact (canonical11060 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA649 + difference 2 1) (sourceB649 + difference 1 2) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA649 + difference 2 1) (sourceB649 + difference 1 2) sourceC649) = raw11061 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11061; decide +kernel
    rw [ha]
    exact (canonical11061 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA649 + difference 2 3) (sourceB649 + difference 3 2) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA649 + difference 2 3) (sourceB649 + difference 3 2) sourceC649) = raw11062 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11062; decide +kernel
    rw [ha]
    exact (canonical11062 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA649 + difference 2 4) (sourceB649 + difference 4 2) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA649 + difference 2 4) (sourceB649 + difference 4 2) sourceC649) = raw11063 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11063; decide +kernel
    rw [ha]
    exact (canonical11063 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA649 + difference 2 5) (sourceB649 + difference 5 2) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA649 + difference 2 5) (sourceB649 + difference 5 2) sourceC649) = raw11064 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11064; decide +kernel
    rw [ha]
    exact (canonical11064 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA649 + difference 3 0) (sourceB649 + difference 0 3) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA649 + difference 3 0) (sourceB649 + difference 0 3) sourceC649) = raw11065 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11065; decide +kernel
    rw [ha]
    exact (canonical11065 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA649 + difference 3 1) (sourceB649 + difference 1 3) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA649 + difference 3 1) (sourceB649 + difference 1 3) sourceC649) = raw11066 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11066; decide +kernel
    rw [ha]
    exact (canonical11066 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA649 + difference 3 2) (sourceB649 + difference 2 3) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA649 + difference 3 2) (sourceB649 + difference 2 3) sourceC649) = raw11067 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11067; decide +kernel
    rw [ha]
    exact (canonical11067 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA649 + difference 3 4) (sourceB649 + difference 4 3) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA649 + difference 3 4) (sourceB649 + difference 4 3) sourceC649) = raw11068 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11068; decide +kernel
    rw [ha]
    exact (canonical11068 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA649 + difference 3 5) (sourceB649 + difference 5 3) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA649 + difference 3 5) (sourceB649 + difference 5 3) sourceC649) = raw11069 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11069; decide +kernel
    rw [ha]
    exact (canonical11069 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA649 + difference 4 0) (sourceB649 + difference 0 4) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA649 + difference 4 0) (sourceB649 + difference 0 4) sourceC649) = raw11070 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11070; decide +kernel
    rw [ha]
    exact (canonical11070 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA649 + difference 4 1) (sourceB649 + difference 1 4) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA649 + difference 4 1) (sourceB649 + difference 1 4) sourceC649) = raw11071 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11071; decide +kernel
    rw [ha]
    exact (canonical11071 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA649 + difference 4 2) (sourceB649 + difference 2 4) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA649 + difference 4 2) (sourceB649 + difference 2 4) sourceC649) = raw11072 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11072; decide +kernel
    rw [ha]
    exact (canonical11072 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA649 + difference 4 3) (sourceB649 + difference 3 4) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA649 + difference 4 3) (sourceB649 + difference 3 4) sourceC649) = raw11073 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11073; decide +kernel
    rw [ha]
    exact (canonical11073 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA649 + difference 4 5) (sourceB649 + difference 5 4) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA649 + difference 4 5) (sourceB649 + difference 5 4) sourceC649) = raw11074 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11074; decide +kernel
    rw [ha]
    exact (canonical11074 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA649 + difference 5 0) (sourceB649 + difference 0 5) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA649 + difference 5 0) (sourceB649 + difference 0 5) sourceC649) = raw11075 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11075; decide +kernel
    rw [ha]
    exact (canonical11075 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA649 + difference 5 1) (sourceB649 + difference 1 5) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA649 + difference 5 1) (sourceB649 + difference 1 5) sourceC649) = raw11076 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11076; decide +kernel
    rw [ha]
    exact (canonical11076 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA649 + difference 5 2) (sourceB649 + difference 2 5) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA649 + difference 5 2) (sourceB649 + difference 2 5) sourceC649) = raw11077 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11077; decide +kernel
    rw [ha]
    exact (canonical11077 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA649 + difference 5 3) (sourceB649 + difference 3 5) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA649 + difference 5 3) (sourceB649 + difference 3 5) sourceC649) = raw11078 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11078; decide +kernel
    rw [ha]
    exact (canonical11078 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA649 + difference 5 4) (sourceB649 + difference 4 5) sourceC649) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA649 + difference 5 4) (sourceB649 + difference 4 5) sourceC649) = raw11079 := by
      apply Matrix.ext; unfold tripleCharges sourceA649 sourceB649 sourceC649 difference raw11079; decide +kernel
    rw [ha]
    exact (canonical11079 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA649 sourceB649 sourceC649
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm649, Integer.Sparse.eval]
  linarith only [hs]

def sourceA650 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB650 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC650 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceForm650 : Integer.Sparse Master := [(Sum.inr 2245, 1), (Sum.inr 3526, 1), (Sum.inr 3573, 2), (Sum.inr 3619, 1), (Sum.inr 3622, 1), (Sum.inr 4083, -1)]

theorem sourceEq650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm650 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA650 + difference 0 0) (sourceB650 + difference 0 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA650 + difference 0 0) (sourceB650 + difference 0 0) sourceC650) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA650 + difference 0 1) (sourceB650 + difference 1 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA650 + difference 0 1) (sourceB650 + difference 1 0) sourceC650) = raw11081 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11081; decide +kernel
    rw [ha]
    exact (canonical11081 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA650 + difference 0 2) (sourceB650 + difference 2 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA650 + difference 0 2) (sourceB650 + difference 2 0) sourceC650) = raw11082 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11082; decide +kernel
    rw [ha]
    exact (canonical11082 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA650 + difference 0 3) (sourceB650 + difference 3 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA650 + difference 0 3) (sourceB650 + difference 3 0) sourceC650) = raw11083 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11083; decide +kernel
    rw [ha]
    exact (canonical11083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA650 + difference 0 4) (sourceB650 + difference 4 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA650 + difference 0 4) (sourceB650 + difference 4 0) sourceC650) = raw11084 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11084; decide +kernel
    rw [ha]
    exact (canonical11084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA650 + difference 0 5) (sourceB650 + difference 5 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA650 + difference 0 5) (sourceB650 + difference 5 0) sourceC650) = raw11085 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11085; decide +kernel
    rw [ha]
    exact (canonical11085 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA650 + sourceB650) sourceC650) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA650 + sourceB650) sourceC650) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA650 sourceB650 sourceC650 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA650 sourceB650 sourceC650
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm650, Integer.Sparse.eval]
  linarith only [hs]

def sourceA651 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB651 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC651 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceForm651 : Integer.Sparse Master := [(Sum.inr 1044, 1), (Sum.inr 2023, 1), (Sum.inr 2110, 1), (Sum.inr 2245, 2), (Sum.inr 2263, 1), (Sum.inr 4083, -1)]

theorem sourceEq651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm651 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA651 + difference 1 0) (sourceB651 + difference 0 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA651 + difference 1 0) (sourceB651 + difference 0 1) sourceC651) = raw11087 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11087; decide +kernel
    rw [ha]
    exact (canonical11087 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA651 + difference 1 1) (sourceB651 + difference 1 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA651 + difference 1 1) (sourceB651 + difference 1 1) sourceC651) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA651 + difference 1 2) (sourceB651 + difference 2 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA651 + difference 1 2) (sourceB651 + difference 2 1) sourceC651) = raw11088 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11088; decide +kernel
    rw [ha]
    exact (canonical11088 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA651 + difference 1 3) (sourceB651 + difference 3 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA651 + difference 1 3) (sourceB651 + difference 3 1) sourceC651) = raw11089 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11089; decide +kernel
    rw [ha]
    exact (canonical11089 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA651 + difference 1 4) (sourceB651 + difference 4 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA651 + difference 1 4) (sourceB651 + difference 4 1) sourceC651) = raw11090 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11090; decide +kernel
    rw [ha]
    exact (canonical11090 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA651 + difference 1 5) (sourceB651 + difference 5 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA651 + difference 1 5) (sourceB651 + difference 5 1) sourceC651) = raw11091 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11091; decide +kernel
    rw [ha]
    exact (canonical11091 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA651 + sourceB651) sourceC651) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA651 + sourceB651) sourceC651) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA651 sourceB651 sourceC651 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA651 sourceB651 sourceC651
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm651, Integer.Sparse.eval]
  linarith only [hs]

def sourceA652 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB652 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC652 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceForm652 : Integer.Sparse Master := [(Sum.inr 2089, 1), (Sum.inr 2092, 1), (Sum.inr 2094, 1), (Sum.inr 2110, 1), (Sum.inr 2245, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem sourceEq652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm652 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA652 + difference 0 1) (sourceB652 + difference 1 0) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA652 + difference 0 1) (sourceB652 + difference 1 0) sourceC652) = raw11081 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11081; decide +kernel
    rw [ha]
    exact (canonical11081 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA652 + difference 1 1) (sourceB652 + difference 1 1) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA652 + difference 1 1) (sourceB652 + difference 1 1) sourceC652) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA652 + difference 2 1) (sourceB652 + difference 1 2) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA652 + difference 2 1) (sourceB652 + difference 1 2) sourceC652) = raw11092 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11092; decide +kernel
    rw [ha]
    exact (canonical11092 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA652 + difference 3 1) (sourceB652 + difference 1 3) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA652 + difference 3 1) (sourceB652 + difference 1 3) sourceC652) = raw11093 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11093; decide +kernel
    rw [ha]
    exact (canonical11093 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA652 + difference 4 1) (sourceB652 + difference 1 4) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA652 + difference 4 1) (sourceB652 + difference 1 4) sourceC652) = raw11094 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11094; decide +kernel
    rw [ha]
    exact (canonical11094 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA652 + difference 5 1) (sourceB652 + difference 1 5) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA652 + difference 5 1) (sourceB652 + difference 1 5) sourceC652) = raw11095 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11095; decide +kernel
    rw [ha]
    exact (canonical11095 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA652 + sourceB652) sourceC652) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA652 + sourceB652) sourceC652) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA652 sourceB652 sourceC652 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA652 sourceB652 sourceC652
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm652, Integer.Sparse.eval]
  linarith only [hs]

def sourceA653 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB653 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC653 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceForm653 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 2012, 1), (Sum.inr 2023, 2), (Sum.inr 2245, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

theorem sourceEq653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm653 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA653 + difference 0 3) (sourceB653 + difference 3 0) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA653 + difference 0 3) (sourceB653 + difference 3 0) sourceC653) = raw11083 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11083; decide +kernel
    rw [ha]
    exact (canonical11083 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA653 + difference 1 3) (sourceB653 + difference 3 1) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA653 + difference 1 3) (sourceB653 + difference 3 1) sourceC653) = raw11089 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11089; decide +kernel
    rw [ha]
    exact (canonical11089 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA653 + difference 2 3) (sourceB653 + difference 3 2) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA653 + difference 2 3) (sourceB653 + difference 3 2) sourceC653) = raw11096 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11096; decide +kernel
    rw [ha]
    exact (canonical11096 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA653 + difference 3 3) (sourceB653 + difference 3 3) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA653 + difference 3 3) (sourceB653 + difference 3 3) sourceC653) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA653 + difference 4 3) (sourceB653 + difference 3 4) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA653 + difference 4 3) (sourceB653 + difference 3 4) sourceC653) = raw11097 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11097; decide +kernel
    rw [ha]
    exact (canonical11097 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA653 + difference 5 3) (sourceB653 + difference 3 5) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA653 + difference 5 3) (sourceB653 + difference 3 5) sourceC653) = raw11098 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11098; decide +kernel
    rw [ha]
    exact (canonical11098 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA653 + sourceB653) sourceC653) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA653 + sourceB653) sourceC653) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA653 sourceB653 sourceC653 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA653 sourceB653 sourceC653
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm653, Integer.Sparse.eval]
  linarith only [hs]

def sourceA654 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB654 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC654 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceForm654 : Integer.Sparse Master := [(Sum.inr 1026, 1), (Sum.inr 2012, 1), (Sum.inr 2094, 2), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

theorem sourceEq654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm654 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA654 + difference 4 0) (sourceB654 + difference 0 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA654 + difference 4 0) (sourceB654 + difference 0 4) sourceC654) = raw11099 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11099; decide +kernel
    rw [ha]
    exact (canonical11099 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA654 + difference 4 1) (sourceB654 + difference 1 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA654 + difference 4 1) (sourceB654 + difference 1 4) sourceC654) = raw11094 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11094; decide +kernel
    rw [ha]
    exact (canonical11094 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA654 + difference 4 2) (sourceB654 + difference 2 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA654 + difference 4 2) (sourceB654 + difference 2 4) sourceC654) = raw11100 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11100; decide +kernel
    rw [ha]
    exact (canonical11100 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA654 + difference 4 3) (sourceB654 + difference 3 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA654 + difference 4 3) (sourceB654 + difference 3 4) sourceC654) = raw11097 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11097; decide +kernel
    rw [ha]
    exact (canonical11097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA654 + difference 4 4) (sourceB654 + difference 4 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA654 + difference 4 4) (sourceB654 + difference 4 4) sourceC654) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA654 + difference 4 5) (sourceB654 + difference 5 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA654 + difference 4 5) (sourceB654 + difference 5 4) sourceC654) = raw11101 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11101; decide +kernel
    rw [ha]
    exact (canonical11101 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA654 + sourceB654) sourceC654) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA654 + sourceB654) sourceC654) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA654 sourceB654 sourceC654 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA654 sourceB654 sourceC654
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm654, Integer.Sparse.eval]
  linarith only [hs]

def sourceA655 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB655 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC655 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceForm655 : Integer.Sparse Master := [(Sum.inr 4252, 1), (Sum.inr 4253, 1), (Sum.inr 4255, 1), (Sum.inr 4268, 2), (Sum.inr 4729, 1), (Sum.inr 4731, 1), (Sum.inr 4740, 2), (Sum.inr 4805, 2), (Sum.inr 4807, 2), (Sum.inr 4810, 2), (Sum.inr 4839, 2), (Sum.inr 4864, 1), (Sum.inr 4865, 1), (Sum.inr 4866, 2), (Sum.inr 4889, 1), (Sum.inr 4890, 1), (Sum.inr 4896, 2), (Sum.inr 5406, 1), (Sum.inr 5435, 2), (Sum.inr 5450, 1), (Sum.inr 5453, 1)]

theorem sourceEq655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm655 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA655 + difference 0 1) (sourceB655 + difference 1 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA655 + difference 0 1) (sourceB655 + difference 1 0) sourceC655) = raw11102 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11102; decide +kernel
    rw [ha]
    exact (canonical11102 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA655 + difference 0 2) (sourceB655 + difference 2 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA655 + difference 0 2) (sourceB655 + difference 2 0) sourceC655) = raw11103 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11103; decide +kernel
    rw [ha]
    exact (canonical11103 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA655 + difference 0 3) (sourceB655 + difference 3 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA655 + difference 0 3) (sourceB655 + difference 3 0) sourceC655) = raw11104 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11104; decide +kernel
    rw [ha]
    exact (canonical11104 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA655 + difference 0 4) (sourceB655 + difference 4 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA655 + difference 0 4) (sourceB655 + difference 4 0) sourceC655) = raw11105 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11105; decide +kernel
    rw [ha]
    exact (canonical11105 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA655 + difference 0 5) (sourceB655 + difference 5 0) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA655 + difference 0 5) (sourceB655 + difference 5 0) sourceC655) = raw11106 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11106; decide +kernel
    rw [ha]
    exact (canonical11106 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA655 + difference 1 0) (sourceB655 + difference 0 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA655 + difference 1 0) (sourceB655 + difference 0 1) sourceC655) = raw11107 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11107; decide +kernel
    rw [ha]
    exact (canonical11107 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA655 + difference 1 2) (sourceB655 + difference 2 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA655 + difference 1 2) (sourceB655 + difference 2 1) sourceC655) = raw11108 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11108; decide +kernel
    rw [ha]
    exact (canonical11108 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA655 + difference 1 3) (sourceB655 + difference 3 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA655 + difference 1 3) (sourceB655 + difference 3 1) sourceC655) = raw11109 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11109; decide +kernel
    rw [ha]
    exact (canonical11109 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA655 + difference 1 4) (sourceB655 + difference 4 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA655 + difference 1 4) (sourceB655 + difference 4 1) sourceC655) = raw11110 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11110; decide +kernel
    rw [ha]
    exact (canonical11110 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA655 + difference 1 5) (sourceB655 + difference 5 1) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA655 + difference 1 5) (sourceB655 + difference 5 1) sourceC655) = raw11111 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11111; decide +kernel
    rw [ha]
    exact (canonical11111 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA655 + difference 2 0) (sourceB655 + difference 0 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA655 + difference 2 0) (sourceB655 + difference 0 2) sourceC655) = raw11112 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11112; decide +kernel
    rw [ha]
    exact (canonical11112 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA655 + difference 2 1) (sourceB655 + difference 1 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA655 + difference 2 1) (sourceB655 + difference 1 2) sourceC655) = raw11113 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11113; decide +kernel
    rw [ha]
    exact (canonical11113 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA655 + difference 2 3) (sourceB655 + difference 3 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA655 + difference 2 3) (sourceB655 + difference 3 2) sourceC655) = raw11114 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11114; decide +kernel
    rw [ha]
    exact (canonical11114 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA655 + difference 2 4) (sourceB655 + difference 4 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA655 + difference 2 4) (sourceB655 + difference 4 2) sourceC655) = raw11115 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11115; decide +kernel
    rw [ha]
    exact (canonical11115 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA655 + difference 2 5) (sourceB655 + difference 5 2) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA655 + difference 2 5) (sourceB655 + difference 5 2) sourceC655) = raw11116 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11116; decide +kernel
    rw [ha]
    exact (canonical11116 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA655 + difference 3 0) (sourceB655 + difference 0 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA655 + difference 3 0) (sourceB655 + difference 0 3) sourceC655) = raw11117 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11117; decide +kernel
    rw [ha]
    exact (canonical11117 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA655 + difference 3 1) (sourceB655 + difference 1 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA655 + difference 3 1) (sourceB655 + difference 1 3) sourceC655) = raw11118 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11118; decide +kernel
    rw [ha]
    exact (canonical11118 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA655 + difference 3 2) (sourceB655 + difference 2 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA655 + difference 3 2) (sourceB655 + difference 2 3) sourceC655) = raw11119 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11119; decide +kernel
    rw [ha]
    exact (canonical11119 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA655 + difference 3 4) (sourceB655 + difference 4 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA655 + difference 3 4) (sourceB655 + difference 4 3) sourceC655) = raw11120 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11120; decide +kernel
    rw [ha]
    exact (canonical11120 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA655 + difference 3 5) (sourceB655 + difference 5 3) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA655 + difference 3 5) (sourceB655 + difference 5 3) sourceC655) = raw11121 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11121; decide +kernel
    rw [ha]
    exact (canonical11121 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA655 + difference 4 0) (sourceB655 + difference 0 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA655 + difference 4 0) (sourceB655 + difference 0 4) sourceC655) = raw11122 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11122; decide +kernel
    rw [ha]
    exact (canonical11122 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA655 + difference 4 1) (sourceB655 + difference 1 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA655 + difference 4 1) (sourceB655 + difference 1 4) sourceC655) = raw11123 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11123; decide +kernel
    rw [ha]
    exact (canonical11123 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA655 + difference 4 2) (sourceB655 + difference 2 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA655 + difference 4 2) (sourceB655 + difference 2 4) sourceC655) = raw11124 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11124; decide +kernel
    rw [ha]
    exact (canonical11124 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA655 + difference 4 3) (sourceB655 + difference 3 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA655 + difference 4 3) (sourceB655 + difference 3 4) sourceC655) = raw11125 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11125; decide +kernel
    rw [ha]
    exact (canonical11125 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA655 + difference 4 5) (sourceB655 + difference 5 4) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA655 + difference 4 5) (sourceB655 + difference 5 4) sourceC655) = raw11126 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11126; decide +kernel
    rw [ha]
    exact (canonical11126 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA655 + difference 5 0) (sourceB655 + difference 0 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA655 + difference 5 0) (sourceB655 + difference 0 5) sourceC655) = raw11127 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11127; decide +kernel
    rw [ha]
    exact (canonical11127 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA655 + difference 5 1) (sourceB655 + difference 1 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA655 + difference 5 1) (sourceB655 + difference 1 5) sourceC655) = raw11128 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11128; decide +kernel
    rw [ha]
    exact (canonical11128 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA655 + difference 5 2) (sourceB655 + difference 2 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA655 + difference 5 2) (sourceB655 + difference 2 5) sourceC655) = raw11129 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11129; decide +kernel
    rw [ha]
    exact (canonical11129 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA655 + difference 5 3) (sourceB655 + difference 3 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA655 + difference 5 3) (sourceB655 + difference 3 5) sourceC655) = raw11130 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11130; decide +kernel
    rw [ha]
    exact (canonical11130 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA655 + difference 5 4) (sourceB655 + difference 4 5) sourceC655) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA655 + difference 5 4) (sourceB655 + difference 4 5) sourceC655) = raw11131 := by
      apply Matrix.ext; unfold tripleCharges sourceA655 sourceB655 sourceC655 difference raw11131; decide +kernel
    rw [ha]
    exact (canonical11131 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA655 sourceB655 sourceC655
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm655, Integer.Sparse.eval]
  linarith only [hs]

def sourceA656 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB656 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC656 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceForm656 : Integer.Sparse Master := [(Sum.inr 786, 1), (Sum.inr 787, 1), (Sum.inr 789, 1), (Sum.inr 811, 2), (Sum.inr 1898, 1), (Sum.inr 1900, 1), (Sum.inr 1913, 2), (Sum.inr 2023, 2), (Sum.inr 2025, 2), (Sum.inr 2028, 2), (Sum.inr 2058, 2), (Sum.inr 2241, 1), (Sum.inr 2242, 1), (Sum.inr 2245, 1), (Sum.inr 2247, 1), (Sum.inr 2260, 2), (Sum.inr 2266, 2), (Sum.inr 3801, 1), (Sum.inr 3853, 2), (Sum.inr 3910, 1), (Sum.inr 3912, 1)]

theorem sourceEq656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm656 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA656 + difference 0 1) (sourceB656 + difference 1 0) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA656 + difference 0 1) (sourceB656 + difference 1 0) sourceC656) = raw11132 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11132; decide +kernel
    rw [ha]
    exact (canonical11132 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA656 + difference 0 2) (sourceB656 + difference 2 0) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA656 + difference 0 2) (sourceB656 + difference 2 0) sourceC656) = raw11133 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11133; decide +kernel
    rw [ha]
    exact (canonical11133 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA656 + difference 0 3) (sourceB656 + difference 3 0) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA656 + difference 0 3) (sourceB656 + difference 3 0) sourceC656) = raw11134 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11134; decide +kernel
    rw [ha]
    exact (canonical11134 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA656 + difference 0 4) (sourceB656 + difference 4 0) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA656 + difference 0 4) (sourceB656 + difference 4 0) sourceC656) = raw11135 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11135; decide +kernel
    rw [ha]
    exact (canonical11135 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA656 + difference 0 5) (sourceB656 + difference 5 0) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA656 + difference 0 5) (sourceB656 + difference 5 0) sourceC656) = raw11136 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11136; decide +kernel
    rw [ha]
    exact (canonical11136 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA656 + difference 1 0) (sourceB656 + difference 0 1) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA656 + difference 1 0) (sourceB656 + difference 0 1) sourceC656) = raw11137 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11137; decide +kernel
    rw [ha]
    exact (canonical11137 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA656 + difference 1 2) (sourceB656 + difference 2 1) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA656 + difference 1 2) (sourceB656 + difference 2 1) sourceC656) = raw11138 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11138; decide +kernel
    rw [ha]
    exact (canonical11138 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA656 + difference 1 3) (sourceB656 + difference 3 1) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1913) := by
    have ha : (tripleCharges (sourceA656 + difference 1 3) (sourceB656 + difference 3 1) sourceC656) = raw11139 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11139; decide +kernel
    rw [ha]
    exact (canonical11139 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA656 + difference 1 4) (sourceB656 + difference 4 1) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA656 + difference 1 4) (sourceB656 + difference 4 1) sourceC656) = raw11140 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11140; decide +kernel
    rw [ha]
    exact (canonical11140 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA656 + difference 1 5) (sourceB656 + difference 5 1) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA656 + difference 1 5) (sourceB656 + difference 5 1) sourceC656) = raw11141 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11141; decide +kernel
    rw [ha]
    exact (canonical11141 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA656 + difference 2 0) (sourceB656 + difference 0 2) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA656 + difference 2 0) (sourceB656 + difference 0 2) sourceC656) = raw11142 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11142; decide +kernel
    rw [ha]
    exact (canonical11142 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA656 + difference 2 1) (sourceB656 + difference 1 2) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA656 + difference 2 1) (sourceB656 + difference 1 2) sourceC656) = raw11143 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11143; decide +kernel
    rw [ha]
    exact (canonical11143 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA656 + difference 2 3) (sourceB656 + difference 3 2) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1913) := by
    have ha : (tripleCharges (sourceA656 + difference 2 3) (sourceB656 + difference 3 2) sourceC656) = raw11144 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11144; decide +kernel
    rw [ha]
    exact (canonical11144 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA656 + difference 2 4) (sourceB656 + difference 4 2) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA656 + difference 2 4) (sourceB656 + difference 4 2) sourceC656) = raw11145 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11145; decide +kernel
    rw [ha]
    exact (canonical11145 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA656 + difference 2 5) (sourceB656 + difference 5 2) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA656 + difference 2 5) (sourceB656 + difference 5 2) sourceC656) = raw11146 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11146; decide +kernel
    rw [ha]
    exact (canonical11146 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA656 + difference 3 0) (sourceB656 + difference 0 3) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA656 + difference 3 0) (sourceB656 + difference 0 3) sourceC656) = raw11147 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11147; decide +kernel
    rw [ha]
    exact (canonical11147 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA656 + difference 3 1) (sourceB656 + difference 1 3) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA656 + difference 3 1) (sourceB656 + difference 1 3) sourceC656) = raw11148 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11148; decide +kernel
    rw [ha]
    exact (canonical11148 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA656 + difference 3 2) (sourceB656 + difference 2 3) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA656 + difference 3 2) (sourceB656 + difference 2 3) sourceC656) = raw11149 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11149; decide +kernel
    rw [ha]
    exact (canonical11149 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA656 + difference 3 4) (sourceB656 + difference 4 3) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA656 + difference 3 4) (sourceB656 + difference 4 3) sourceC656) = raw11150 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11150; decide +kernel
    rw [ha]
    exact (canonical11150 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA656 + difference 3 5) (sourceB656 + difference 5 3) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA656 + difference 3 5) (sourceB656 + difference 5 3) sourceC656) = raw11151 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11151; decide +kernel
    rw [ha]
    exact (canonical11151 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA656 + difference 4 0) (sourceB656 + difference 0 4) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA656 + difference 4 0) (sourceB656 + difference 0 4) sourceC656) = raw11152 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11152; decide +kernel
    rw [ha]
    exact (canonical11152 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA656 + difference 4 1) (sourceB656 + difference 1 4) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA656 + difference 4 1) (sourceB656 + difference 1 4) sourceC656) = raw11153 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11153; decide +kernel
    rw [ha]
    exact (canonical11153 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA656 + difference 4 2) (sourceB656 + difference 2 4) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA656 + difference 4 2) (sourceB656 + difference 2 4) sourceC656) = raw11154 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11154; decide +kernel
    rw [ha]
    exact (canonical11154 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA656 + difference 4 3) (sourceB656 + difference 3 4) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1900) := by
    have ha : (tripleCharges (sourceA656 + difference 4 3) (sourceB656 + difference 3 4) sourceC656) = raw11155 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11155; decide +kernel
    rw [ha]
    exact (canonical11155 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA656 + difference 4 5) (sourceB656 + difference 5 4) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA656 + difference 4 5) (sourceB656 + difference 5 4) sourceC656) = raw11156 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11156; decide +kernel
    rw [ha]
    exact (canonical11156 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA656 + difference 5 0) (sourceB656 + difference 0 5) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA656 + difference 5 0) (sourceB656 + difference 0 5) sourceC656) = raw11157 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11157; decide +kernel
    rw [ha]
    exact (canonical11157 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA656 + difference 5 1) (sourceB656 + difference 1 5) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA656 + difference 5 1) (sourceB656 + difference 1 5) sourceC656) = raw11158 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11158; decide +kernel
    rw [ha]
    exact (canonical11158 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA656 + difference 5 2) (sourceB656 + difference 2 5) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA656 + difference 5 2) (sourceB656 + difference 2 5) sourceC656) = raw11159 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11159; decide +kernel
    rw [ha]
    exact (canonical11159 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA656 + difference 5 3) (sourceB656 + difference 3 5) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA656 + difference 5 3) (sourceB656 + difference 3 5) sourceC656) = raw11160 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11160; decide +kernel
    rw [ha]
    exact (canonical11160 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA656 + difference 5 4) (sourceB656 + difference 4 5) sourceC656) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA656 + difference 5 4) (sourceB656 + difference 4 5) sourceC656) = raw11161 := by
      apply Matrix.ext; unfold tripleCharges sourceA656 sourceB656 sourceC656 difference raw11161; decide +kernel
    rw [ha]
    exact (canonical11161 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA656 sourceB656 sourceC656
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm656, Integer.Sparse.eval]
  linarith only [hs]

def sourceA657 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB657 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC657 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm657 : Integer.Sparse Master := [(Sum.inr 4473, 1), (Sum.inr 4474, 1), (Sum.inr 4475, 2), (Sum.inr 4495, 1), (Sum.inr 4815, 1), (Sum.inr 4816, 2), (Sum.inr 4831, 1), (Sum.inr 4878, 1), (Sum.inr 4879, 1), (Sum.inr 4880, 2), (Sum.inr 4885, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 2), (Sum.inr 4891, 2), (Sum.inr 4895, 2), (Sum.inr 4896, 2), (Sum.inr 4898, 2), (Sum.inr 5251, 1), (Sum.inr 5270, 1), (Sum.inr 5284, 1), (Sum.inr 5294, 2)]

theorem sourceEq657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm657 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA657 + difference 0 1) (sourceB657 + difference 1 0) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA657 + difference 0 1) (sourceB657 + difference 1 0) sourceC657) = raw7527 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw7527; decide +kernel
    rw [ha]
    exact (canonical7527 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA657 + difference 0 2) (sourceB657 + difference 2 0) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA657 + difference 0 2) (sourceB657 + difference 2 0) sourceC657) = raw7651 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw7651; decide +kernel
    rw [ha]
    exact (canonical7651 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA657 + difference 0 3) (sourceB657 + difference 3 0) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA657 + difference 0 3) (sourceB657 + difference 3 0) sourceC657) = raw9905 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw9905; decide +kernel
    rw [ha]
    exact (canonical9905 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA657 + difference 0 4) (sourceB657 + difference 4 0) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA657 + difference 0 4) (sourceB657 + difference 4 0) sourceC657) = raw5660 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw5660; decide +kernel
    rw [ha]
    exact (canonical5660 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA657 + difference 0 5) (sourceB657 + difference 5 0) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA657 + difference 0 5) (sourceB657 + difference 5 0) sourceC657) = raw9478 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw9478; decide +kernel
    rw [ha]
    exact (canonical9478 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA657 + difference 1 0) (sourceB657 + difference 0 1) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA657 + difference 1 0) (sourceB657 + difference 0 1) sourceC657) = raw11162 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11162; decide +kernel
    rw [ha]
    exact (canonical11162 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA657 + difference 1 2) (sourceB657 + difference 2 1) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA657 + difference 1 2) (sourceB657 + difference 2 1) sourceC657) = raw10975 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw10975; decide +kernel
    rw [ha]
    exact (canonical10975 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA657 + difference 1 3) (sourceB657 + difference 3 1) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA657 + difference 1 3) (sourceB657 + difference 3 1) sourceC657) = raw11163 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11163; decide +kernel
    rw [ha]
    exact (canonical11163 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA657 + difference 1 4) (sourceB657 + difference 4 1) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA657 + difference 1 4) (sourceB657 + difference 4 1) sourceC657) = raw5665 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw5665; decide +kernel
    rw [ha]
    exact (canonical5665 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA657 + difference 1 5) (sourceB657 + difference 5 1) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA657 + difference 1 5) (sourceB657 + difference 5 1) sourceC657) = raw11164 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11164; decide +kernel
    rw [ha]
    exact (canonical11164 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA657 + difference 2 0) (sourceB657 + difference 0 2) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA657 + difference 2 0) (sourceB657 + difference 0 2) sourceC657) = raw11165 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11165; decide +kernel
    rw [ha]
    exact (canonical11165 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA657 + difference 2 1) (sourceB657 + difference 1 2) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA657 + difference 2 1) (sourceB657 + difference 1 2) sourceC657) = raw11166 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11166; decide +kernel
    rw [ha]
    exact (canonical11166 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA657 + difference 2 3) (sourceB657 + difference 3 2) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA657 + difference 2 3) (sourceB657 + difference 3 2) sourceC657) = raw11167 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11167; decide +kernel
    rw [ha]
    exact (canonical11167 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA657 + difference 2 4) (sourceB657 + difference 4 2) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA657 + difference 2 4) (sourceB657 + difference 4 2) sourceC657) = raw5670 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw5670; decide +kernel
    rw [ha]
    exact (canonical5670 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA657 + difference 2 5) (sourceB657 + difference 5 2) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA657 + difference 2 5) (sourceB657 + difference 5 2) sourceC657) = raw11168 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11168; decide +kernel
    rw [ha]
    exact (canonical11168 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA657 + difference 3 0) (sourceB657 + difference 0 3) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4473) := by
    have ha : (tripleCharges (sourceA657 + difference 3 0) (sourceB657 + difference 0 3) sourceC657) = raw5678 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw5678; decide +kernel
    rw [ha]
    exact (canonical5678 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA657 + difference 3 1) (sourceB657 + difference 1 3) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA657 + difference 3 1) (sourceB657 + difference 1 3) sourceC657) = raw5679 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw5679; decide +kernel
    rw [ha]
    exact (canonical5679 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA657 + difference 3 2) (sourceB657 + difference 2 3) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA657 + difference 3 2) (sourceB657 + difference 2 3) sourceC657) = raw5680 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw5680; decide +kernel
    rw [ha]
    exact (canonical5680 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA657 + difference 3 4) (sourceB657 + difference 4 3) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA657 + difference 3 4) (sourceB657 + difference 4 3) sourceC657) = raw9236 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw9236; decide +kernel
    rw [ha]
    exact (canonical9236 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA657 + difference 3 5) (sourceB657 + difference 5 3) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA657 + difference 3 5) (sourceB657 + difference 5 3) sourceC657) = raw5682 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw5682; decide +kernel
    rw [ha]
    exact (canonical5682 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA657 + difference 4 0) (sourceB657 + difference 0 4) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA657 + difference 4 0) (sourceB657 + difference 0 4) sourceC657) = raw11169 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11169; decide +kernel
    rw [ha]
    exact (canonical11169 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA657 + difference 4 1) (sourceB657 + difference 1 4) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA657 + difference 4 1) (sourceB657 + difference 1 4) sourceC657) = raw7653 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw7653; decide +kernel
    rw [ha]
    exact (canonical7653 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA657 + difference 4 2) (sourceB657 + difference 2 4) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA657 + difference 4 2) (sourceB657 + difference 2 4) sourceC657) = raw7648 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw7648; decide +kernel
    rw [ha]
    exact (canonical7648 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA657 + difference 4 3) (sourceB657 + difference 3 4) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA657 + difference 4 3) (sourceB657 + difference 3 4) sourceC657) = raw11170 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11170; decide +kernel
    rw [ha]
    exact (canonical11170 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA657 + difference 4 5) (sourceB657 + difference 5 4) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA657 + difference 4 5) (sourceB657 + difference 5 4) sourceC657) = raw11171 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11171; decide +kernel
    rw [ha]
    exact (canonical11171 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA657 + difference 5 0) (sourceB657 + difference 0 5) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA657 + difference 5 0) (sourceB657 + difference 0 5) sourceC657) = raw11172 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11172; decide +kernel
    rw [ha]
    exact (canonical11172 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA657 + difference 5 1) (sourceB657 + difference 1 5) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA657 + difference 5 1) (sourceB657 + difference 1 5) sourceC657) = raw11173 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw11173; decide +kernel
    rw [ha]
    exact (canonical11173 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA657 + difference 5 2) (sourceB657 + difference 2 5) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA657 + difference 5 2) (sourceB657 + difference 2 5) sourceC657) = raw9906 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw9906; decide +kernel
    rw [ha]
    exact (canonical9906 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA657 + difference 5 3) (sourceB657 + difference 3 5) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA657 + difference 5 3) (sourceB657 + difference 3 5) sourceC657) = raw9901 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw9901; decide +kernel
    rw [ha]
    exact (canonical9901 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA657 + difference 5 4) (sourceB657 + difference 4 5) sourceC657) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA657 + difference 5 4) (sourceB657 + difference 4 5) sourceC657) = raw5686 := by
      apply Matrix.ext; unfold tripleCharges sourceA657 sourceB657 sourceC657 difference raw5686; decide +kernel
    rw [ha]
    exact (canonical5686 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA657 sourceB657 sourceC657
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm657, Integer.Sparse.eval]
  linarith only [hs]

def sourceA658 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB658 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC658 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm658 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 1708, 1), (Sum.inr 1709, 1), (Sum.inr 1715, 2), (Sum.inr 2191, 1), (Sum.inr 2192, 1), (Sum.inr 2196, 2), (Sum.inr 2233, 1), (Sum.inr 2234, 1), (Sum.inr 2244, 1), (Sum.inr 2245, 2), (Sum.inr 2246, 1), (Sum.inr 2253, 2), (Sum.inr 2254, 2), (Sum.inr 2265, 2), (Sum.inr 2266, 2), (Sum.inr 2279, 2), (Sum.inr 2710, 1), (Sum.inr 2753, 1), (Sum.inr 2754, 1), (Sum.inr 2768, 2)]

theorem sourceEq658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm658 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA658 + difference 0 1) (sourceB658 + difference 1 0) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA658 + difference 0 1) (sourceB658 + difference 1 0) sourceC658) = raw7536 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw7536; decide +kernel
    rw [ha]
    exact (canonical7536 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA658 + difference 0 2) (sourceB658 + difference 2 0) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA658 + difference 0 2) (sourceB658 + difference 2 0) sourceC658) = raw7667 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw7667; decide +kernel
    rw [ha]
    exact (canonical7667 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA658 + difference 0 3) (sourceB658 + difference 3 0) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA658 + difference 0 3) (sourceB658 + difference 3 0) sourceC658) = raw9929 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw9929; decide +kernel
    rw [ha]
    exact (canonical9929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA658 + difference 0 4) (sourceB658 + difference 4 0) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA658 + difference 0 4) (sourceB658 + difference 4 0) sourceC658) = raw5690 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw5690; decide +kernel
    rw [ha]
    exact (canonical5690 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA658 + difference 0 5) (sourceB658 + difference 5 0) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA658 + difference 0 5) (sourceB658 + difference 5 0) sourceC658) = raw9487 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw9487; decide +kernel
    rw [ha]
    exact (canonical9487 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA658 + difference 1 0) (sourceB658 + difference 0 1) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA658 + difference 1 0) (sourceB658 + difference 0 1) sourceC658) = raw11174 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11174; decide +kernel
    rw [ha]
    exact (canonical11174 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA658 + difference 1 2) (sourceB658 + difference 2 1) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA658 + difference 1 2) (sourceB658 + difference 2 1) sourceC658) = raw10993 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw10993; decide +kernel
    rw [ha]
    exact (canonical10993 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA658 + difference 1 3) (sourceB658 + difference 3 1) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA658 + difference 1 3) (sourceB658 + difference 3 1) sourceC658) = raw11175 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11175; decide +kernel
    rw [ha]
    exact (canonical11175 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA658 + difference 1 4) (sourceB658 + difference 4 1) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA658 + difference 1 4) (sourceB658 + difference 4 1) sourceC658) = raw5695 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw5695; decide +kernel
    rw [ha]
    exact (canonical5695 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA658 + difference 1 5) (sourceB658 + difference 5 1) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA658 + difference 1 5) (sourceB658 + difference 5 1) sourceC658) = raw11176 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11176; decide +kernel
    rw [ha]
    exact (canonical11176 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA658 + difference 2 0) (sourceB658 + difference 0 2) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA658 + difference 2 0) (sourceB658 + difference 0 2) sourceC658) = raw11177 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11177; decide +kernel
    rw [ha]
    exact (canonical11177 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA658 + difference 2 1) (sourceB658 + difference 1 2) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA658 + difference 2 1) (sourceB658 + difference 1 2) sourceC658) = raw11178 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11178; decide +kernel
    rw [ha]
    exact (canonical11178 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA658 + difference 2 3) (sourceB658 + difference 3 2) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA658 + difference 2 3) (sourceB658 + difference 3 2) sourceC658) = raw11179 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11179; decide +kernel
    rw [ha]
    exact (canonical11179 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA658 + difference 2 4) (sourceB658 + difference 4 2) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA658 + difference 2 4) (sourceB658 + difference 4 2) sourceC658) = raw5700 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw5700; decide +kernel
    rw [ha]
    exact (canonical5700 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA658 + difference 2 5) (sourceB658 + difference 5 2) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA658 + difference 2 5) (sourceB658 + difference 5 2) sourceC658) = raw11180 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11180; decide +kernel
    rw [ha]
    exact (canonical11180 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA658 + difference 3 0) (sourceB658 + difference 0 3) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA658 + difference 3 0) (sourceB658 + difference 0 3) sourceC658) = raw5708 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw5708; decide +kernel
    rw [ha]
    exact (canonical5708 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA658 + difference 3 1) (sourceB658 + difference 1 3) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA658 + difference 3 1) (sourceB658 + difference 1 3) sourceC658) = raw5709 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw5709; decide +kernel
    rw [ha]
    exact (canonical5709 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA658 + difference 3 2) (sourceB658 + difference 2 3) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA658 + difference 3 2) (sourceB658 + difference 2 3) sourceC658) = raw5710 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw5710; decide +kernel
    rw [ha]
    exact (canonical5710 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA658 + difference 3 4) (sourceB658 + difference 4 3) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA658 + difference 3 4) (sourceB658 + difference 4 3) sourceC658) = raw9241 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw9241; decide +kernel
    rw [ha]
    exact (canonical9241 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA658 + difference 3 5) (sourceB658 + difference 5 3) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA658 + difference 3 5) (sourceB658 + difference 5 3) sourceC658) = raw5712 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw5712; decide +kernel
    rw [ha]
    exact (canonical5712 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA658 + difference 4 0) (sourceB658 + difference 0 4) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA658 + difference 4 0) (sourceB658 + difference 0 4) sourceC658) = raw11181 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11181; decide +kernel
    rw [ha]
    exact (canonical11181 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA658 + difference 4 1) (sourceB658 + difference 1 4) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA658 + difference 4 1) (sourceB658 + difference 1 4) sourceC658) = raw7669 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw7669; decide +kernel
    rw [ha]
    exact (canonical7669 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA658 + difference 4 2) (sourceB658 + difference 2 4) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA658 + difference 4 2) (sourceB658 + difference 2 4) sourceC658) = raw7664 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw7664; decide +kernel
    rw [ha]
    exact (canonical7664 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA658 + difference 4 3) (sourceB658 + difference 3 4) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA658 + difference 4 3) (sourceB658 + difference 3 4) sourceC658) = raw11182 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11182; decide +kernel
    rw [ha]
    exact (canonical11182 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA658 + difference 4 5) (sourceB658 + difference 5 4) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA658 + difference 4 5) (sourceB658 + difference 5 4) sourceC658) = raw11183 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11183; decide +kernel
    rw [ha]
    exact (canonical11183 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA658 + difference 5 0) (sourceB658 + difference 0 5) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA658 + difference 5 0) (sourceB658 + difference 0 5) sourceC658) = raw11184 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11184; decide +kernel
    rw [ha]
    exact (canonical11184 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA658 + difference 5 1) (sourceB658 + difference 1 5) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA658 + difference 5 1) (sourceB658 + difference 1 5) sourceC658) = raw11185 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw11185; decide +kernel
    rw [ha]
    exact (canonical11185 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA658 + difference 5 2) (sourceB658 + difference 2 5) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA658 + difference 5 2) (sourceB658 + difference 2 5) sourceC658) = raw9930 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw9930; decide +kernel
    rw [ha]
    exact (canonical9930 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA658 + difference 5 3) (sourceB658 + difference 3 5) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA658 + difference 5 3) (sourceB658 + difference 3 5) sourceC658) = raw9925 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw9925; decide +kernel
    rw [ha]
    exact (canonical9925 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA658 + difference 5 4) (sourceB658 + difference 4 5) sourceC658) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA658 + difference 5 4) (sourceB658 + difference 4 5) sourceC658) = raw5716 := by
      apply Matrix.ext; unfold tripleCharges sourceA658 sourceB658 sourceC658 difference raw5716; decide +kernel
    rw [ha]
    exact (canonical5716 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA658 sourceB658 sourceC658
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm658, Integer.Sparse.eval]
  linarith only [hs]

def sourceA659 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB659 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC659 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm659 : Integer.Sparse Master := [(Sum.inr 1366, 1), (Sum.inr 1367, 2), (Sum.inr 1370, 1), (Sum.inr 1441, 1), (Sum.inr 3064, 1), (Sum.inr 3075, 1), (Sum.inr 3077, 1), (Sum.inr 3101, 2), (Sum.inr 3155, 1), (Sum.inr 3156, 2), (Sum.inr 3158, 1), (Sum.inr 3196, 2), (Sum.inr 3197, 1), (Sum.inr 3209, 1), (Sum.inr 3221, 1), (Sum.inr 3222, 2), (Sum.inr 3223, 2), (Sum.inr 3224, 2), (Sum.inr 3225, 2), (Sum.inr 3227, 1), (Sum.inr 3229, 2)]

theorem sourceEq659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm659 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA659 + difference 0 1) (sourceB659 + difference 1 0) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA659 + difference 0 1) (sourceB659 + difference 1 0) sourceC659) = raw7545 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw7545; decide +kernel
    rw [ha]
    exact (canonical7545 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA659 + difference 0 2) (sourceB659 + difference 2 0) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA659 + difference 0 2) (sourceB659 + difference 2 0) sourceC659) = raw7683 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw7683; decide +kernel
    rw [ha]
    exact (canonical7683 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA659 + difference 0 3) (sourceB659 + difference 3 0) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA659 + difference 0 3) (sourceB659 + difference 3 0) sourceC659) = raw9953 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw9953; decide +kernel
    rw [ha]
    exact (canonical9953 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA659 + difference 0 4) (sourceB659 + difference 4 0) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA659 + difference 0 4) (sourceB659 + difference 4 0) sourceC659) = raw5720 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw5720; decide +kernel
    rw [ha]
    exact (canonical5720 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA659 + difference 0 5) (sourceB659 + difference 5 0) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA659 + difference 0 5) (sourceB659 + difference 5 0) sourceC659) = raw9496 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw9496; decide +kernel
    rw [ha]
    exact (canonical9496 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA659 + difference 1 0) (sourceB659 + difference 0 1) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA659 + difference 1 0) (sourceB659 + difference 0 1) sourceC659) = raw11186 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11186; decide +kernel
    rw [ha]
    exact (canonical11186 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA659 + difference 1 2) (sourceB659 + difference 2 1) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA659 + difference 1 2) (sourceB659 + difference 2 1) sourceC659) = raw11011 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11011; decide +kernel
    rw [ha]
    exact (canonical11011 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA659 + difference 1 3) (sourceB659 + difference 3 1) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA659 + difference 1 3) (sourceB659 + difference 3 1) sourceC659) = raw11187 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11187; decide +kernel
    rw [ha]
    exact (canonical11187 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA659 + difference 1 4) (sourceB659 + difference 4 1) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA659 + difference 1 4) (sourceB659 + difference 4 1) sourceC659) = raw5725 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw5725; decide +kernel
    rw [ha]
    exact (canonical5725 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA659 + difference 1 5) (sourceB659 + difference 5 1) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA659 + difference 1 5) (sourceB659 + difference 5 1) sourceC659) = raw11188 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11188; decide +kernel
    rw [ha]
    exact (canonical11188 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA659 + difference 2 0) (sourceB659 + difference 0 2) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA659 + difference 2 0) (sourceB659 + difference 0 2) sourceC659) = raw11189 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11189; decide +kernel
    rw [ha]
    exact (canonical11189 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA659 + difference 2 1) (sourceB659 + difference 1 2) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA659 + difference 2 1) (sourceB659 + difference 1 2) sourceC659) = raw11190 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11190; decide +kernel
    rw [ha]
    exact (canonical11190 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA659 + difference 2 3) (sourceB659 + difference 3 2) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA659 + difference 2 3) (sourceB659 + difference 3 2) sourceC659) = raw11191 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11191; decide +kernel
    rw [ha]
    exact (canonical11191 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA659 + difference 2 4) (sourceB659 + difference 4 2) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA659 + difference 2 4) (sourceB659 + difference 4 2) sourceC659) = raw5730 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw5730; decide +kernel
    rw [ha]
    exact (canonical5730 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA659 + difference 2 5) (sourceB659 + difference 5 2) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA659 + difference 2 5) (sourceB659 + difference 5 2) sourceC659) = raw11192 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11192; decide +kernel
    rw [ha]
    exact (canonical11192 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA659 + difference 3 0) (sourceB659 + difference 0 3) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1366) := by
    have ha : (tripleCharges (sourceA659 + difference 3 0) (sourceB659 + difference 0 3) sourceC659) = raw5738 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw5738; decide +kernel
    rw [ha]
    exact (canonical5738 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA659 + difference 3 1) (sourceB659 + difference 1 3) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA659 + difference 3 1) (sourceB659 + difference 1 3) sourceC659) = raw5739 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw5739; decide +kernel
    rw [ha]
    exact (canonical5739 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA659 + difference 3 2) (sourceB659 + difference 2 3) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA659 + difference 3 2) (sourceB659 + difference 2 3) sourceC659) = raw5740 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw5740; decide +kernel
    rw [ha]
    exact (canonical5740 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA659 + difference 3 4) (sourceB659 + difference 4 3) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA659 + difference 3 4) (sourceB659 + difference 4 3) sourceC659) = raw9247 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw9247; decide +kernel
    rw [ha]
    exact (canonical9247 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA659 + difference 3 5) (sourceB659 + difference 5 3) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA659 + difference 3 5) (sourceB659 + difference 5 3) sourceC659) = raw5742 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw5742; decide +kernel
    rw [ha]
    exact (canonical5742 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA659 + difference 4 0) (sourceB659 + difference 0 4) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA659 + difference 4 0) (sourceB659 + difference 0 4) sourceC659) = raw11193 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11193; decide +kernel
    rw [ha]
    exact (canonical11193 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA659 + difference 4 1) (sourceB659 + difference 1 4) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA659 + difference 4 1) (sourceB659 + difference 1 4) sourceC659) = raw7685 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw7685; decide +kernel
    rw [ha]
    exact (canonical7685 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA659 + difference 4 2) (sourceB659 + difference 2 4) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA659 + difference 4 2) (sourceB659 + difference 2 4) sourceC659) = raw7680 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw7680; decide +kernel
    rw [ha]
    exact (canonical7680 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA659 + difference 4 3) (sourceB659 + difference 3 4) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA659 + difference 4 3) (sourceB659 + difference 3 4) sourceC659) = raw11194 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11194; decide +kernel
    rw [ha]
    exact (canonical11194 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA659 + difference 4 5) (sourceB659 + difference 5 4) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA659 + difference 4 5) (sourceB659 + difference 5 4) sourceC659) = raw11195 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11195; decide +kernel
    rw [ha]
    exact (canonical11195 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA659 + difference 5 0) (sourceB659 + difference 0 5) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1441) := by
    have ha : (tripleCharges (sourceA659 + difference 5 0) (sourceB659 + difference 0 5) sourceC659) = raw11196 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11196; decide +kernel
    rw [ha]
    exact (canonical11196 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA659 + difference 5 1) (sourceB659 + difference 1 5) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA659 + difference 5 1) (sourceB659 + difference 1 5) sourceC659) = raw11197 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw11197; decide +kernel
    rw [ha]
    exact (canonical11197 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA659 + difference 5 2) (sourceB659 + difference 2 5) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA659 + difference 5 2) (sourceB659 + difference 2 5) sourceC659) = raw9954 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw9954; decide +kernel
    rw [ha]
    exact (canonical9954 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA659 + difference 5 3) (sourceB659 + difference 3 5) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3209) := by
    have ha : (tripleCharges (sourceA659 + difference 5 3) (sourceB659 + difference 3 5) sourceC659) = raw9949 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw9949; decide +kernel
    rw [ha]
    exact (canonical9949 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA659 + difference 5 4) (sourceB659 + difference 4 5) sourceC659) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA659 + difference 5 4) (sourceB659 + difference 4 5) sourceC659) = raw5746 := by
      apply Matrix.ext; unfold tripleCharges sourceA659 sourceB659 sourceC659 difference raw5746; decide +kernel
    rw [ha]
    exact (canonical5746 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA659 sourceB659 sourceC659
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm659, Integer.Sparse.eval]
  linarith only [hs]

def sourceA660 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB660 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC660 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm660 : Integer.Sparse Master := [(Sum.inr 1056, 1), (Sum.inr 1057, 1), (Sum.inr 1058, 2), (Sum.inr 1079, 1), (Sum.inr 2277, 1), (Sum.inr 4084, -1)]

theorem sourceEq660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm660 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA660 + difference 0 0) (sourceB660 + difference 0 0) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA660 + difference 0 0) (sourceB660 + difference 0 0) sourceC660) = raw5762 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw5762; decide +kernel
    rw [ha]
    exact (canonical5762 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA660 + difference 1 0) (sourceB660 + difference 0 1) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA660 + difference 1 0) (sourceB660 + difference 0 1) sourceC660) = raw11198 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw11198; decide +kernel
    rw [ha]
    exact (canonical11198 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA660 + difference 2 0) (sourceB660 + difference 0 2) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA660 + difference 2 0) (sourceB660 + difference 0 2) sourceC660) = raw11199 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw11199; decide +kernel
    rw [ha]
    exact (canonical11199 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA660 + difference 3 0) (sourceB660 + difference 0 3) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1056) := by
    have ha : (tripleCharges (sourceA660 + difference 3 0) (sourceB660 + difference 0 3) sourceC660) = raw5758 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw5758; decide +kernel
    rw [ha]
    exact (canonical5758 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA660 + difference 4 0) (sourceB660 + difference 0 4) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA660 + difference 4 0) (sourceB660 + difference 0 4) sourceC660) = raw11200 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw11200; decide +kernel
    rw [ha]
    exact (canonical11200 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA660 + difference 5 0) (sourceB660 + difference 0 5) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA660 + difference 5 0) (sourceB660 + difference 0 5) sourceC660) = raw11201 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw11201; decide +kernel
    rw [ha]
    exact (canonical11201 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA660 + sourceB660) sourceC660) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA660 + sourceB660) sourceC660) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA660 sourceB660 sourceC660 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA660 sourceB660 sourceC660
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm660, Integer.Sparse.eval]
  linarith only [hs]

def sourceA661 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB661 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC661 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm661 : Integer.Sparse Master := [(Sum.inr 4438, 1), (Sum.inr 4440, 1), (Sum.inr 4444, 1), (Sum.inr 4458, 2), (Sum.inr 4792, 1), (Sum.inr 4795, 1), (Sum.inr 4802, 2), (Sum.inr 4851, 2), (Sum.inr 4853, 2), (Sum.inr 4856, 2), (Sum.inr 4866, 2), (Sum.inr 4887, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4890, 1), (Sum.inr 4893, 2), (Sum.inr 4895, 2), (Sum.inr 5256, 1), (Sum.inr 5289, 2), (Sum.inr 5292, 1), (Sum.inr 5306, 1)]

theorem sourceEq661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm661 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA661 + difference 0 1) (sourceB661 + difference 1 0) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA661 + difference 0 1) (sourceB661 + difference 1 0) sourceC661) = raw11202 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11202; decide +kernel
    rw [ha]
    exact (canonical11202 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA661 + difference 0 2) (sourceB661 + difference 2 0) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA661 + difference 0 2) (sourceB661 + difference 2 0) sourceC661) = raw11203 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11203; decide +kernel
    rw [ha]
    exact (canonical11203 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA661 + difference 0 3) (sourceB661 + difference 3 0) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA661 + difference 0 3) (sourceB661 + difference 3 0) sourceC661) = raw11204 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11204; decide +kernel
    rw [ha]
    exact (canonical11204 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA661 + difference 0 4) (sourceB661 + difference 4 0) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA661 + difference 0 4) (sourceB661 + difference 4 0) sourceC661) = raw11205 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11205; decide +kernel
    rw [ha]
    exact (canonical11205 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA661 + difference 0 5) (sourceB661 + difference 5 0) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA661 + difference 0 5) (sourceB661 + difference 5 0) sourceC661) = raw11206 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11206; decide +kernel
    rw [ha]
    exact (canonical11206 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA661 + difference 1 0) (sourceB661 + difference 0 1) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA661 + difference 1 0) (sourceB661 + difference 0 1) sourceC661) = raw11207 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11207; decide +kernel
    rw [ha]
    exact (canonical11207 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA661 + difference 1 2) (sourceB661 + difference 2 1) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA661 + difference 1 2) (sourceB661 + difference 2 1) sourceC661) = raw11208 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11208; decide +kernel
    rw [ha]
    exact (canonical11208 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA661 + difference 1 3) (sourceB661 + difference 3 1) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA661 + difference 1 3) (sourceB661 + difference 3 1) sourceC661) = raw11209 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11209; decide +kernel
    rw [ha]
    exact (canonical11209 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA661 + difference 1 4) (sourceB661 + difference 4 1) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA661 + difference 1 4) (sourceB661 + difference 4 1) sourceC661) = raw11210 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11210; decide +kernel
    rw [ha]
    exact (canonical11210 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA661 + difference 1 5) (sourceB661 + difference 5 1) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA661 + difference 1 5) (sourceB661 + difference 5 1) sourceC661) = raw11211 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11211; decide +kernel
    rw [ha]
    exact (canonical11211 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA661 + difference 2 0) (sourceB661 + difference 0 2) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA661 + difference 2 0) (sourceB661 + difference 0 2) sourceC661) = raw11212 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11212; decide +kernel
    rw [ha]
    exact (canonical11212 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA661 + difference 2 1) (sourceB661 + difference 1 2) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA661 + difference 2 1) (sourceB661 + difference 1 2) sourceC661) = raw11213 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11213; decide +kernel
    rw [ha]
    exact (canonical11213 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA661 + difference 2 3) (sourceB661 + difference 3 2) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA661 + difference 2 3) (sourceB661 + difference 3 2) sourceC661) = raw11214 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11214; decide +kernel
    rw [ha]
    exact (canonical11214 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA661 + difference 2 4) (sourceB661 + difference 4 2) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA661 + difference 2 4) (sourceB661 + difference 4 2) sourceC661) = raw11215 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11215; decide +kernel
    rw [ha]
    exact (canonical11215 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA661 + difference 2 5) (sourceB661 + difference 5 2) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA661 + difference 2 5) (sourceB661 + difference 5 2) sourceC661) = raw11216 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11216; decide +kernel
    rw [ha]
    exact (canonical11216 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA661 + difference 3 0) (sourceB661 + difference 0 3) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA661 + difference 3 0) (sourceB661 + difference 0 3) sourceC661) = raw11217 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11217; decide +kernel
    rw [ha]
    exact (canonical11217 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA661 + difference 3 1) (sourceB661 + difference 1 3) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA661 + difference 3 1) (sourceB661 + difference 1 3) sourceC661) = raw11218 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11218; decide +kernel
    rw [ha]
    exact (canonical11218 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA661 + difference 3 2) (sourceB661 + difference 2 3) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA661 + difference 3 2) (sourceB661 + difference 2 3) sourceC661) = raw11219 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11219; decide +kernel
    rw [ha]
    exact (canonical11219 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA661 + difference 3 4) (sourceB661 + difference 4 3) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA661 + difference 3 4) (sourceB661 + difference 4 3) sourceC661) = raw11220 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11220; decide +kernel
    rw [ha]
    exact (canonical11220 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA661 + difference 3 5) (sourceB661 + difference 5 3) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA661 + difference 3 5) (sourceB661 + difference 5 3) sourceC661) = raw11221 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11221; decide +kernel
    rw [ha]
    exact (canonical11221 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA661 + difference 4 0) (sourceB661 + difference 0 4) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA661 + difference 4 0) (sourceB661 + difference 0 4) sourceC661) = raw11222 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11222; decide +kernel
    rw [ha]
    exact (canonical11222 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA661 + difference 4 1) (sourceB661 + difference 1 4) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA661 + difference 4 1) (sourceB661 + difference 1 4) sourceC661) = raw11223 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11223; decide +kernel
    rw [ha]
    exact (canonical11223 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA661 + difference 4 2) (sourceB661 + difference 2 4) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA661 + difference 4 2) (sourceB661 + difference 2 4) sourceC661) = raw11224 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11224; decide +kernel
    rw [ha]
    exact (canonical11224 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA661 + difference 4 3) (sourceB661 + difference 3 4) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA661 + difference 4 3) (sourceB661 + difference 3 4) sourceC661) = raw11225 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11225; decide +kernel
    rw [ha]
    exact (canonical11225 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA661 + difference 4 5) (sourceB661 + difference 5 4) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA661 + difference 4 5) (sourceB661 + difference 5 4) sourceC661) = raw11226 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11226; decide +kernel
    rw [ha]
    exact (canonical11226 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA661 + difference 5 0) (sourceB661 + difference 0 5) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA661 + difference 5 0) (sourceB661 + difference 0 5) sourceC661) = raw11227 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11227; decide +kernel
    rw [ha]
    exact (canonical11227 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA661 + difference 5 1) (sourceB661 + difference 1 5) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA661 + difference 5 1) (sourceB661 + difference 1 5) sourceC661) = raw11228 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11228; decide +kernel
    rw [ha]
    exact (canonical11228 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA661 + difference 5 2) (sourceB661 + difference 2 5) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA661 + difference 5 2) (sourceB661 + difference 2 5) sourceC661) = raw11229 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11229; decide +kernel
    rw [ha]
    exact (canonical11229 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA661 + difference 5 3) (sourceB661 + difference 3 5) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA661 + difference 5 3) (sourceB661 + difference 3 5) sourceC661) = raw11230 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11230; decide +kernel
    rw [ha]
    exact (canonical11230 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA661 + difference 5 4) (sourceB661 + difference 4 5) sourceC661) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA661 + difference 5 4) (sourceB661 + difference 4 5) sourceC661) = raw11231 := by
      apply Matrix.ext; unfold tripleCharges sourceA661 sourceB661 sourceC661 difference raw11231; decide +kernel
    rw [ha]
    exact (canonical11231 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA661 sourceB661 sourceC661
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm661, Integer.Sparse.eval]
  linarith only [hs]

def sourceA662 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB662 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC662 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm662 : Integer.Sparse Master := [(Sum.inr 1386, 1), (Sum.inr 1388, 1), (Sum.inr 1391, 1), (Sum.inr 1411, 2), (Sum.inr 2471, 1), (Sum.inr 2486, 2), (Sum.inr 2755, 1), (Sum.inr 3085, 1), (Sum.inr 3097, 2), (Sum.inr 3100, 1), (Sum.inr 3120, 1), (Sum.inr 3172, 2), (Sum.inr 3174, 2), (Sum.inr 3184, 2), (Sum.inr 3199, 1), (Sum.inr 3204, 2), (Sum.inr 3223, 1), (Sum.inr 3226, 1), (Sum.inr 3227, 1), (Sum.inr 3228, 2), (Sum.inr 3229, 2)]

theorem sourceEq662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm662 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA662 + difference 0 1) (sourceB662 + difference 1 0) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA662 + difference 0 1) (sourceB662 + difference 1 0) sourceC662) = raw11232 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11232; decide +kernel
    rw [ha]
    exact (canonical11232 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA662 + difference 0 2) (sourceB662 + difference 2 0) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA662 + difference 0 2) (sourceB662 + difference 2 0) sourceC662) = raw11233 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11233; decide +kernel
    rw [ha]
    exact (canonical11233 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA662 + difference 0 3) (sourceB662 + difference 3 0) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA662 + difference 0 3) (sourceB662 + difference 3 0) sourceC662) = raw11234 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11234; decide +kernel
    rw [ha]
    exact (canonical11234 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA662 + difference 0 4) (sourceB662 + difference 4 0) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA662 + difference 0 4) (sourceB662 + difference 4 0) sourceC662) = raw11235 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11235; decide +kernel
    rw [ha]
    exact (canonical11235 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA662 + difference 0 5) (sourceB662 + difference 5 0) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA662 + difference 0 5) (sourceB662 + difference 5 0) sourceC662) = raw11236 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11236; decide +kernel
    rw [ha]
    exact (canonical11236 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA662 + difference 1 0) (sourceB662 + difference 0 1) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA662 + difference 1 0) (sourceB662 + difference 0 1) sourceC662) = raw11237 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11237; decide +kernel
    rw [ha]
    exact (canonical11237 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA662 + difference 1 2) (sourceB662 + difference 2 1) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3184) := by
    have ha : (tripleCharges (sourceA662 + difference 1 2) (sourceB662 + difference 2 1) sourceC662) = raw11238 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11238; decide +kernel
    rw [ha]
    exact (canonical11238 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA662 + difference 1 3) (sourceB662 + difference 3 1) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA662 + difference 1 3) (sourceB662 + difference 3 1) sourceC662) = raw11239 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11239; decide +kernel
    rw [ha]
    exact (canonical11239 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA662 + difference 1 4) (sourceB662 + difference 4 1) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA662 + difference 1 4) (sourceB662 + difference 4 1) sourceC662) = raw11240 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11240; decide +kernel
    rw [ha]
    exact (canonical11240 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA662 + difference 1 5) (sourceB662 + difference 5 1) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3228) := by
    have ha : (tripleCharges (sourceA662 + difference 1 5) (sourceB662 + difference 5 1) sourceC662) = raw11241 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11241; decide +kernel
    rw [ha]
    exact (canonical11241 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA662 + difference 2 0) (sourceB662 + difference 0 2) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA662 + difference 2 0) (sourceB662 + difference 0 2) sourceC662) = raw11242 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11242; decide +kernel
    rw [ha]
    exact (canonical11242 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA662 + difference 2 1) (sourceB662 + difference 1 2) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3184) := by
    have ha : (tripleCharges (sourceA662 + difference 2 1) (sourceB662 + difference 1 2) sourceC662) = raw11243 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11243; decide +kernel
    rw [ha]
    exact (canonical11243 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA662 + difference 2 3) (sourceB662 + difference 3 2) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA662 + difference 2 3) (sourceB662 + difference 3 2) sourceC662) = raw11244 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11244; decide +kernel
    rw [ha]
    exact (canonical11244 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA662 + difference 2 4) (sourceB662 + difference 4 2) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA662 + difference 2 4) (sourceB662 + difference 4 2) sourceC662) = raw11245 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11245; decide +kernel
    rw [ha]
    exact (canonical11245 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA662 + difference 2 5) (sourceB662 + difference 5 2) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3228) := by
    have ha : (tripleCharges (sourceA662 + difference 2 5) (sourceB662 + difference 5 2) sourceC662) = raw11246 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11246; decide +kernel
    rw [ha]
    exact (canonical11246 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA662 + difference 3 0) (sourceB662 + difference 0 3) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1386) := by
    have ha : (tripleCharges (sourceA662 + difference 3 0) (sourceB662 + difference 0 3) sourceC662) = raw11247 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11247; decide +kernel
    rw [ha]
    exact (canonical11247 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA662 + difference 3 1) (sourceB662 + difference 1 3) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA662 + difference 3 1) (sourceB662 + difference 1 3) sourceC662) = raw11248 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11248; decide +kernel
    rw [ha]
    exact (canonical11248 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA662 + difference 3 2) (sourceB662 + difference 2 3) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA662 + difference 3 2) (sourceB662 + difference 2 3) sourceC662) = raw11249 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11249; decide +kernel
    rw [ha]
    exact (canonical11249 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA662 + difference 3 4) (sourceB662 + difference 4 3) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA662 + difference 3 4) (sourceB662 + difference 4 3) sourceC662) = raw11250 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11250; decide +kernel
    rw [ha]
    exact (canonical11250 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA662 + difference 3 5) (sourceB662 + difference 5 3) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA662 + difference 3 5) (sourceB662 + difference 5 3) sourceC662) = raw11251 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11251; decide +kernel
    rw [ha]
    exact (canonical11251 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA662 + difference 4 0) (sourceB662 + difference 0 4) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA662 + difference 4 0) (sourceB662 + difference 0 4) sourceC662) = raw11252 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11252; decide +kernel
    rw [ha]
    exact (canonical11252 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA662 + difference 4 1) (sourceB662 + difference 1 4) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA662 + difference 4 1) (sourceB662 + difference 1 4) sourceC662) = raw11253 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11253; decide +kernel
    rw [ha]
    exact (canonical11253 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA662 + difference 4 2) (sourceB662 + difference 2 4) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA662 + difference 4 2) (sourceB662 + difference 2 4) sourceC662) = raw11254 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11254; decide +kernel
    rw [ha]
    exact (canonical11254 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA662 + difference 4 3) (sourceB662 + difference 3 4) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA662 + difference 4 3) (sourceB662 + difference 3 4) sourceC662) = raw11255 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11255; decide +kernel
    rw [ha]
    exact (canonical11255 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA662 + difference 4 5) (sourceB662 + difference 5 4) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA662 + difference 4 5) (sourceB662 + difference 5 4) sourceC662) = raw11256 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11256; decide +kernel
    rw [ha]
    exact (canonical11256 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA662 + difference 5 0) (sourceB662 + difference 0 5) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA662 + difference 5 0) (sourceB662 + difference 0 5) sourceC662) = raw11257 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11257; decide +kernel
    rw [ha]
    exact (canonical11257 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA662 + difference 5 1) (sourceB662 + difference 1 5) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA662 + difference 5 1) (sourceB662 + difference 1 5) sourceC662) = raw11258 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11258; decide +kernel
    rw [ha]
    exact (canonical11258 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA662 + difference 5 2) (sourceB662 + difference 2 5) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA662 + difference 5 2) (sourceB662 + difference 2 5) sourceC662) = raw11259 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11259; decide +kernel
    rw [ha]
    exact (canonical11259 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA662 + difference 5 3) (sourceB662 + difference 3 5) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA662 + difference 5 3) (sourceB662 + difference 3 5) sourceC662) = raw11260 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11260; decide +kernel
    rw [ha]
    exact (canonical11260 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA662 + difference 5 4) (sourceB662 + difference 4 5) sourceC662) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA662 + difference 5 4) (sourceB662 + difference 4 5) sourceC662) = raw11261 := by
      apply Matrix.ext; unfold tripleCharges sourceA662 sourceB662 sourceC662 difference raw11261; decide +kernel
    rw [ha]
    exact (canonical11261 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA662 sourceB662 sourceC662
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm662, Integer.Sparse.eval]
  linarith only [hs]

def sourceA663 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB663 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC663 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm663 : Integer.Sparse Master := [(Sum.inr 1705, 1), (Sum.inr 1723, 1), (Sum.inr 1724, 2), (Sum.inr 1736, 1), (Sum.inr 2201, 1), (Sum.inr 2202, 2), (Sum.inr 2213, 1), (Sum.inr 2240, 2), (Sum.inr 2243, 1), (Sum.inr 2259, 2), (Sum.inr 2260, 2), (Sum.inr 2262, 1), (Sum.inr 2263, 2), (Sum.inr 2274, 2), (Sum.inr 2277, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 2), (Sum.inr 2720, 1), (Sum.inr 2763, 2), (Sum.inr 2766, 1), (Sum.inr 2784, 1)]

theorem sourceEq663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm663 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA663 + difference 0 1) (sourceB663 + difference 1 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA663 + difference 0 1) (sourceB663 + difference 1 0) sourceC663) = raw11262 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11262; decide +kernel
    rw [ha]
    exact (canonical11262 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA663 + difference 0 2) (sourceB663 + difference 2 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA663 + difference 0 2) (sourceB663 + difference 2 0) sourceC663) = raw11263 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11263; decide +kernel
    rw [ha]
    exact (canonical11263 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA663 + difference 0 3) (sourceB663 + difference 3 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA663 + difference 0 3) (sourceB663 + difference 3 0) sourceC663) = raw11264 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11264; decide +kernel
    rw [ha]
    exact (canonical11264 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA663 + difference 0 4) (sourceB663 + difference 4 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA663 + difference 0 4) (sourceB663 + difference 4 0) sourceC663) = raw11265 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11265; decide +kernel
    rw [ha]
    exact (canonical11265 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA663 + difference 0 5) (sourceB663 + difference 5 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA663 + difference 0 5) (sourceB663 + difference 5 0) sourceC663) = raw11266 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11266; decide +kernel
    rw [ha]
    exact (canonical11266 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA663 + difference 1 0) (sourceB663 + difference 0 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA663 + difference 1 0) (sourceB663 + difference 0 1) sourceC663) = raw11267 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11267; decide +kernel
    rw [ha]
    exact (canonical11267 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA663 + difference 1 2) (sourceB663 + difference 2 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA663 + difference 1 2) (sourceB663 + difference 2 1) sourceC663) = raw11268 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11268; decide +kernel
    rw [ha]
    exact (canonical11268 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA663 + difference 1 3) (sourceB663 + difference 3 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA663 + difference 1 3) (sourceB663 + difference 3 1) sourceC663) = raw11269 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11269; decide +kernel
    rw [ha]
    exact (canonical11269 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA663 + difference 1 4) (sourceB663 + difference 4 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA663 + difference 1 4) (sourceB663 + difference 4 1) sourceC663) = raw11270 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11270; decide +kernel
    rw [ha]
    exact (canonical11270 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA663 + difference 1 5) (sourceB663 + difference 5 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA663 + difference 1 5) (sourceB663 + difference 5 1) sourceC663) = raw11271 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11271; decide +kernel
    rw [ha]
    exact (canonical11271 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA663 + difference 2 0) (sourceB663 + difference 0 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA663 + difference 2 0) (sourceB663 + difference 0 2) sourceC663) = raw11272 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11272; decide +kernel
    rw [ha]
    exact (canonical11272 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA663 + difference 2 1) (sourceB663 + difference 1 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA663 + difference 2 1) (sourceB663 + difference 1 2) sourceC663) = raw11273 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11273; decide +kernel
    rw [ha]
    exact (canonical11273 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA663 + difference 2 3) (sourceB663 + difference 3 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA663 + difference 2 3) (sourceB663 + difference 3 2) sourceC663) = raw11274 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11274; decide +kernel
    rw [ha]
    exact (canonical11274 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA663 + difference 2 4) (sourceB663 + difference 4 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA663 + difference 2 4) (sourceB663 + difference 4 2) sourceC663) = raw11275 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11275; decide +kernel
    rw [ha]
    exact (canonical11275 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA663 + difference 2 5) (sourceB663 + difference 5 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA663 + difference 2 5) (sourceB663 + difference 5 2) sourceC663) = raw11276 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11276; decide +kernel
    rw [ha]
    exact (canonical11276 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA663 + difference 3 0) (sourceB663 + difference 0 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA663 + difference 3 0) (sourceB663 + difference 0 3) sourceC663) = raw11277 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11277; decide +kernel
    rw [ha]
    exact (canonical11277 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA663 + difference 3 1) (sourceB663 + difference 1 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA663 + difference 3 1) (sourceB663 + difference 1 3) sourceC663) = raw11278 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11278; decide +kernel
    rw [ha]
    exact (canonical11278 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA663 + difference 3 2) (sourceB663 + difference 2 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA663 + difference 3 2) (sourceB663 + difference 2 3) sourceC663) = raw11279 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11279; decide +kernel
    rw [ha]
    exact (canonical11279 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA663 + difference 3 4) (sourceB663 + difference 4 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA663 + difference 3 4) (sourceB663 + difference 4 3) sourceC663) = raw11280 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11280; decide +kernel
    rw [ha]
    exact (canonical11280 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA663 + difference 3 5) (sourceB663 + difference 5 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA663 + difference 3 5) (sourceB663 + difference 5 3) sourceC663) = raw11281 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11281; decide +kernel
    rw [ha]
    exact (canonical11281 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA663 + difference 4 0) (sourceB663 + difference 0 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA663 + difference 4 0) (sourceB663 + difference 0 4) sourceC663) = raw11282 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11282; decide +kernel
    rw [ha]
    exact (canonical11282 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA663 + difference 4 1) (sourceB663 + difference 1 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA663 + difference 4 1) (sourceB663 + difference 1 4) sourceC663) = raw11283 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11283; decide +kernel
    rw [ha]
    exact (canonical11283 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA663 + difference 4 2) (sourceB663 + difference 2 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA663 + difference 4 2) (sourceB663 + difference 2 4) sourceC663) = raw11284 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11284; decide +kernel
    rw [ha]
    exact (canonical11284 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA663 + difference 4 3) (sourceB663 + difference 3 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA663 + difference 4 3) (sourceB663 + difference 3 4) sourceC663) = raw11285 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11285; decide +kernel
    rw [ha]
    exact (canonical11285 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA663 + difference 4 5) (sourceB663 + difference 5 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA663 + difference 4 5) (sourceB663 + difference 5 4) sourceC663) = raw11286 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11286; decide +kernel
    rw [ha]
    exact (canonical11286 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA663 + difference 5 0) (sourceB663 + difference 0 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA663 + difference 5 0) (sourceB663 + difference 0 5) sourceC663) = raw11287 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11287; decide +kernel
    rw [ha]
    exact (canonical11287 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA663 + difference 5 1) (sourceB663 + difference 1 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA663 + difference 5 1) (sourceB663 + difference 1 5) sourceC663) = raw11288 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11288; decide +kernel
    rw [ha]
    exact (canonical11288 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA663 + difference 5 2) (sourceB663 + difference 2 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA663 + difference 5 2) (sourceB663 + difference 2 5) sourceC663) = raw11289 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11289; decide +kernel
    rw [ha]
    exact (canonical11289 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA663 + difference 5 3) (sourceB663 + difference 3 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA663 + difference 5 3) (sourceB663 + difference 3 5) sourceC663) = raw11290 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11290; decide +kernel
    rw [ha]
    exact (canonical11290 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA663 + difference 5 4) (sourceB663 + difference 4 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA663 + difference 5 4) (sourceB663 + difference 4 5) sourceC663) = raw11291 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11291; decide +kernel
    rw [ha]
    exact (canonical11291 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA663 sourceB663 sourceC663
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm663, Integer.Sparse.eval]
  linarith only [hs]

def sourceA664 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB664 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC664 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm664 : Integer.Sparse Master := [(Sum.inr 2244, 1), (Sum.inr 3525, 1), (Sum.inr 3572, 2), (Sum.inr 3622, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

theorem sourceEq664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm664 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA664 + difference 0 0) (sourceB664 + difference 0 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA664 + difference 0 0) (sourceB664 + difference 0 0) sourceC664) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA664 + difference 0 1) (sourceB664 + difference 1 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA664 + difference 0 1) (sourceB664 + difference 1 0) sourceC664) = raw11293 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11293; decide +kernel
    rw [ha]
    exact (canonical11293 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA664 + difference 0 2) (sourceB664 + difference 2 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA664 + difference 0 2) (sourceB664 + difference 2 0) sourceC664) = raw11294 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11294; decide +kernel
    rw [ha]
    exact (canonical11294 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA664 + difference 0 3) (sourceB664 + difference 3 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA664 + difference 0 3) (sourceB664 + difference 3 0) sourceC664) = raw11295 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11295; decide +kernel
    rw [ha]
    exact (canonical11295 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA664 + difference 0 4) (sourceB664 + difference 4 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA664 + difference 0 4) (sourceB664 + difference 4 0) sourceC664) = raw11296 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11296; decide +kernel
    rw [ha]
    exact (canonical11296 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA664 + difference 0 5) (sourceB664 + difference 5 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA664 + difference 0 5) (sourceB664 + difference 5 0) sourceC664) = raw11297 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11297; decide +kernel
    rw [ha]
    exact (canonical11297 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA664 + sourceB664) sourceC664) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA664 + sourceB664) sourceC664) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA664 sourceB664 sourceC664 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA664 sourceB664 sourceC664
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm664, Integer.Sparse.eval]
  linarith only [hs]

def sourceA665 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB665 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC665 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm665 : Integer.Sparse Master := [(Sum.inr 1020, 1), (Sum.inr 1022, 1), (Sum.inr 1026, 1), (Sum.inr 1041, 2), (Sum.inr 2244, 1), (Sum.inr 4083, -1)]

theorem sourceEq665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm665 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA665 + difference 0 0) (sourceB665 + difference 0 0) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA665 + difference 0 0) (sourceB665 + difference 0 0) sourceC665) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA665 + difference 1 0) (sourceB665 + difference 0 1) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA665 + difference 1 0) (sourceB665 + difference 0 1) sourceC665) = raw11299 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11299; decide +kernel
    rw [ha]
    exact (canonical11299 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA665 + difference 2 0) (sourceB665 + difference 0 2) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA665 + difference 2 0) (sourceB665 + difference 0 2) sourceC665) = raw11300 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11300; decide +kernel
    rw [ha]
    exact (canonical11300 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA665 + difference 3 0) (sourceB665 + difference 0 3) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1020) := by
    have ha : (tripleCharges (sourceA665 + difference 3 0) (sourceB665 + difference 0 3) sourceC665) = raw11301 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11301; decide +kernel
    rw [ha]
    exact (canonical11301 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA665 + difference 4 0) (sourceB665 + difference 0 4) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA665 + difference 4 0) (sourceB665 + difference 0 4) sourceC665) = raw11302 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11302; decide +kernel
    rw [ha]
    exact (canonical11302 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA665 + difference 5 0) (sourceB665 + difference 0 5) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA665 + difference 5 0) (sourceB665 + difference 0 5) sourceC665) = raw11303 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11303; decide +kernel
    rw [ha]
    exact (canonical11303 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA665 + sourceB665) sourceC665) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA665 + sourceB665) sourceC665) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA665 sourceB665 sourceC665 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA665 sourceB665 sourceC665
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm665, Integer.Sparse.eval]
  linarith only [hs]

def sourceA666 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB666 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC666 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm666 : Integer.Sparse Master := [(Sum.inr 1041, 1), (Sum.inr 2020, 1), (Sum.inr 2107, 1), (Sum.inr 2244, 1), (Sum.inr 2263, 1), (Sum.inr 2265, 1), (Sum.inr 4083, -1)]

theorem sourceEq666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm666 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA666 + difference 1 0) (sourceB666 + difference 0 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA666 + difference 1 0) (sourceB666 + difference 0 1) sourceC666) = raw11299 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11299; decide +kernel
    rw [ha]
    exact (canonical11299 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA666 + difference 1 1) (sourceB666 + difference 1 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA666 + difference 1 1) (sourceB666 + difference 1 1) sourceC666) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA666 + difference 1 2) (sourceB666 + difference 2 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA666 + difference 1 2) (sourceB666 + difference 2 1) sourceC666) = raw11304 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11304; decide +kernel
    rw [ha]
    exact (canonical11304 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA666 + difference 1 3) (sourceB666 + difference 3 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA666 + difference 1 3) (sourceB666 + difference 3 1) sourceC666) = raw11305 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11305; decide +kernel
    rw [ha]
    exact (canonical11305 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA666 + difference 1 4) (sourceB666 + difference 4 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA666 + difference 1 4) (sourceB666 + difference 4 1) sourceC666) = raw11306 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11306; decide +kernel
    rw [ha]
    exact (canonical11306 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA666 + difference 1 5) (sourceB666 + difference 5 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA666 + difference 1 5) (sourceB666 + difference 5 1) sourceC666) = raw11307 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11307; decide +kernel
    rw [ha]
    exact (canonical11307 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA666 + sourceB666) sourceC666) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA666 + sourceB666) sourceC666) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA666 sourceB666 sourceC666 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA666 sourceB666 sourceC666
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm666, Integer.Sparse.eval]
  linarith only [hs]

def sourceA667 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB667 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC667 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm667 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2090, 1), (Sum.inr 2094, 1), (Sum.inr 2107, 1), (Sum.inr 2244, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

theorem sourceEq667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm667 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA667 + difference 0 1) (sourceB667 + difference 1 0) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA667 + difference 0 1) (sourceB667 + difference 1 0) sourceC667) = raw11293 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11293; decide +kernel
    rw [ha]
    exact (canonical11293 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA667 + difference 1 1) (sourceB667 + difference 1 1) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA667 + difference 1 1) (sourceB667 + difference 1 1) sourceC667) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA667 + difference 2 1) (sourceB667 + difference 1 2) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA667 + difference 2 1) (sourceB667 + difference 1 2) sourceC667) = raw11308 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11308; decide +kernel
    rw [ha]
    exact (canonical11308 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA667 + difference 3 1) (sourceB667 + difference 1 3) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA667 + difference 3 1) (sourceB667 + difference 1 3) sourceC667) = raw11309 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11309; decide +kernel
    rw [ha]
    exact (canonical11309 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA667 + difference 4 1) (sourceB667 + difference 1 4) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA667 + difference 4 1) (sourceB667 + difference 1 4) sourceC667) = raw11310 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11310; decide +kernel
    rw [ha]
    exact (canonical11310 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA667 + difference 5 1) (sourceB667 + difference 1 5) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA667 + difference 5 1) (sourceB667 + difference 1 5) sourceC667) = raw11311 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11311; decide +kernel
    rw [ha]
    exact (canonical11311 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA667 + sourceB667) sourceC667) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA667 + sourceB667) sourceC667) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA667 sourceB667 sourceC667 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA667 sourceB667 sourceC667
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm667, Integer.Sparse.eval]
  linarith only [hs]

def sourceA668 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB668 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC668 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm668 : Integer.Sparse Master := [(Sum.inr 1020, 1), (Sum.inr 2088, 2), (Sum.inr 2243, 1), (Sum.inr 2244, 2), (Sum.inr 4083, -1)]

theorem sourceEq668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm668 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA668 + difference 3 0) (sourceB668 + difference 0 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1020) := by
    have ha : (tripleCharges (sourceA668 + difference 3 0) (sourceB668 + difference 0 3) sourceC668) = raw11301 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11301; decide +kernel
    rw [ha]
    exact (canonical11301 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA668 + difference 3 1) (sourceB668 + difference 1 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA668 + difference 3 1) (sourceB668 + difference 1 3) sourceC668) = raw11309 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11309; decide +kernel
    rw [ha]
    exact (canonical11309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA668 + difference 3 2) (sourceB668 + difference 2 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA668 + difference 3 2) (sourceB668 + difference 2 3) sourceC668) = raw11312 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11312; decide +kernel
    rw [ha]
    exact (canonical11312 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA668 + difference 3 3) (sourceB668 + difference 3 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA668 + difference 3 3) (sourceB668 + difference 3 3) sourceC668) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA668 + difference 3 4) (sourceB668 + difference 4 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA668 + difference 3 4) (sourceB668 + difference 4 3) sourceC668) = raw11313 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11313; decide +kernel
    rw [ha]
    exact (canonical11313 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA668 + difference 3 5) (sourceB668 + difference 5 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA668 + difference 3 5) (sourceB668 + difference 5 3) sourceC668) = raw11314 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11314; decide +kernel
    rw [ha]
    exact (canonical11314 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA668 + sourceB668) sourceC668) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA668 + sourceB668) sourceC668) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA668 sourceB668 sourceC668 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA668 sourceB668 sourceC668
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm668, Integer.Sparse.eval]
  linarith only [hs]

def sourceA669 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB669 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC669 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceForm669 : Integer.Sparse Master := [(Sum.inr 4249, 1), (Sum.inr 4251, 1), (Sum.inr 4256, 1), (Sum.inr 4265, 2), (Sum.inr 4728, 1), (Sum.inr 4732, 1), (Sum.inr 4737, 2), (Sum.inr 4802, 2), (Sum.inr 4804, 2), (Sum.inr 4811, 2), (Sum.inr 4831, 1), (Sum.inr 4832, 1), (Sum.inr 4835, 4), (Sum.inr 4887, 1), (Sum.inr 4888, 3), (Sum.inr 5405, 1), (Sum.inr 5434, 2), (Sum.inr 5439, 1), (Sum.inr 5452, 1)]

theorem sourceEq669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm669 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA669 + difference 0 1) (sourceB669 + difference 1 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA669 + difference 0 1) (sourceB669 + difference 1 0) sourceC669) = raw11315 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11315; decide +kernel
    rw [ha]
    exact (canonical11315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA669 + difference 0 2) (sourceB669 + difference 2 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA669 + difference 0 2) (sourceB669 + difference 2 0) sourceC669) = raw11316 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11316; decide +kernel
    rw [ha]
    exact (canonical11316 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA669 + difference 0 3) (sourceB669 + difference 3 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA669 + difference 0 3) (sourceB669 + difference 3 0) sourceC669) = raw11317 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11317; decide +kernel
    rw [ha]
    exact (canonical11317 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA669 + difference 0 4) (sourceB669 + difference 4 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA669 + difference 0 4) (sourceB669 + difference 4 0) sourceC669) = raw11318 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11318; decide +kernel
    rw [ha]
    exact (canonical11318 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA669 + difference 0 5) (sourceB669 + difference 5 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA669 + difference 0 5) (sourceB669 + difference 5 0) sourceC669) = raw11319 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11319; decide +kernel
    rw [ha]
    exact (canonical11319 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA669 + difference 1 0) (sourceB669 + difference 0 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA669 + difference 1 0) (sourceB669 + difference 0 1) sourceC669) = raw11320 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11320; decide +kernel
    rw [ha]
    exact (canonical11320 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA669 + difference 1 2) (sourceB669 + difference 2 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA669 + difference 1 2) (sourceB669 + difference 2 1) sourceC669) = raw11321 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11321; decide +kernel
    rw [ha]
    exact (canonical11321 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA669 + difference 1 3) (sourceB669 + difference 3 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA669 + difference 1 3) (sourceB669 + difference 3 1) sourceC669) = raw11322 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11322; decide +kernel
    rw [ha]
    exact (canonical11322 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA669 + difference 1 4) (sourceB669 + difference 4 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA669 + difference 1 4) (sourceB669 + difference 4 1) sourceC669) = raw11323 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11323; decide +kernel
    rw [ha]
    exact (canonical11323 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA669 + difference 1 5) (sourceB669 + difference 5 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA669 + difference 1 5) (sourceB669 + difference 5 1) sourceC669) = raw11324 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11324; decide +kernel
    rw [ha]
    exact (canonical11324 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA669 + difference 2 0) (sourceB669 + difference 0 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA669 + difference 2 0) (sourceB669 + difference 0 2) sourceC669) = raw11325 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11325; decide +kernel
    rw [ha]
    exact (canonical11325 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA669 + difference 2 1) (sourceB669 + difference 1 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA669 + difference 2 1) (sourceB669 + difference 1 2) sourceC669) = raw11326 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11326; decide +kernel
    rw [ha]
    exact (canonical11326 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA669 + difference 2 3) (sourceB669 + difference 3 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA669 + difference 2 3) (sourceB669 + difference 3 2) sourceC669) = raw11327 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11327; decide +kernel
    rw [ha]
    exact (canonical11327 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA669 + difference 2 4) (sourceB669 + difference 4 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA669 + difference 2 4) (sourceB669 + difference 4 2) sourceC669) = raw11328 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11328; decide +kernel
    rw [ha]
    exact (canonical11328 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA669 + difference 2 5) (sourceB669 + difference 5 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA669 + difference 2 5) (sourceB669 + difference 5 2) sourceC669) = raw11329 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11329; decide +kernel
    rw [ha]
    exact (canonical11329 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA669 + difference 3 0) (sourceB669 + difference 0 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA669 + difference 3 0) (sourceB669 + difference 0 3) sourceC669) = raw11330 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11330; decide +kernel
    rw [ha]
    exact (canonical11330 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA669 + difference 3 1) (sourceB669 + difference 1 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA669 + difference 3 1) (sourceB669 + difference 1 3) sourceC669) = raw11331 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11331; decide +kernel
    rw [ha]
    exact (canonical11331 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA669 + difference 3 2) (sourceB669 + difference 2 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA669 + difference 3 2) (sourceB669 + difference 2 3) sourceC669) = raw11332 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11332; decide +kernel
    rw [ha]
    exact (canonical11332 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA669 + difference 3 4) (sourceB669 + difference 4 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA669 + difference 3 4) (sourceB669 + difference 4 3) sourceC669) = raw11333 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11333; decide +kernel
    rw [ha]
    exact (canonical11333 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA669 + difference 3 5) (sourceB669 + difference 5 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA669 + difference 3 5) (sourceB669 + difference 5 3) sourceC669) = raw11334 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11334; decide +kernel
    rw [ha]
    exact (canonical11334 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA669 + difference 4 0) (sourceB669 + difference 0 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA669 + difference 4 0) (sourceB669 + difference 0 4) sourceC669) = raw11335 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11335; decide +kernel
    rw [ha]
    exact (canonical11335 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA669 + difference 4 1) (sourceB669 + difference 1 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA669 + difference 4 1) (sourceB669 + difference 1 4) sourceC669) = raw11336 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11336; decide +kernel
    rw [ha]
    exact (canonical11336 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA669 + difference 4 2) (sourceB669 + difference 2 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA669 + difference 4 2) (sourceB669 + difference 2 4) sourceC669) = raw11337 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11337; decide +kernel
    rw [ha]
    exact (canonical11337 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA669 + difference 4 3) (sourceB669 + difference 3 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA669 + difference 4 3) (sourceB669 + difference 3 4) sourceC669) = raw11338 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11338; decide +kernel
    rw [ha]
    exact (canonical11338 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA669 + difference 4 5) (sourceB669 + difference 5 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA669 + difference 4 5) (sourceB669 + difference 5 4) sourceC669) = raw11339 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11339; decide +kernel
    rw [ha]
    exact (canonical11339 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA669 + difference 5 0) (sourceB669 + difference 0 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA669 + difference 5 0) (sourceB669 + difference 0 5) sourceC669) = raw11340 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11340; decide +kernel
    rw [ha]
    exact (canonical11340 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA669 + difference 5 1) (sourceB669 + difference 1 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA669 + difference 5 1) (sourceB669 + difference 1 5) sourceC669) = raw11341 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11341; decide +kernel
    rw [ha]
    exact (canonical11341 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA669 + difference 5 2) (sourceB669 + difference 2 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA669 + difference 5 2) (sourceB669 + difference 2 5) sourceC669) = raw11342 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11342; decide +kernel
    rw [ha]
    exact (canonical11342 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA669 + difference 5 3) (sourceB669 + difference 3 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA669 + difference 5 3) (sourceB669 + difference 3 5) sourceC669) = raw11343 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11343; decide +kernel
    rw [ha]
    exact (canonical11343 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA669 + difference 5 4) (sourceB669 + difference 4 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA669 + difference 5 4) (sourceB669 + difference 4 5) sourceC669) = raw11344 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11344; decide +kernel
    rw [ha]
    exact (canonical11344 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA669 sourceB669 sourceC669
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm669, Integer.Sparse.eval]
  linarith only [hs]

def sourceA670 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB670 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC670 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceForm670 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 785, 1), (Sum.inr 790, 1), (Sum.inr 807, 2), (Sum.inr 1897, 1), (Sum.inr 1901, 1), (Sum.inr 1909, 2), (Sum.inr 2020, 2), (Sum.inr 2022, 2), (Sum.inr 2029, 2), (Sum.inr 2054, 2), (Sum.inr 2191, 1), (Sum.inr 2193, 1), (Sum.inr 2206, 2), (Sum.inr 2243, 1), (Sum.inr 2244, 1), (Sum.inr 2262, 2), (Sum.inr 3800, 1), (Sum.inr 3852, 2), (Sum.inr 3902, 1), (Sum.inr 3911, 1)]

theorem sourceEq670 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm670 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA670 + difference 0 1) (sourceB670 + difference 1 0) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA670 + difference 0 1) (sourceB670 + difference 1 0) sourceC670) = raw11345 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11345; decide +kernel
    rw [ha]
    exact (canonical11345 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA670 + difference 0 2) (sourceB670 + difference 2 0) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA670 + difference 0 2) (sourceB670 + difference 2 0) sourceC670) = raw11346 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11346; decide +kernel
    rw [ha]
    exact (canonical11346 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA670 + difference 0 3) (sourceB670 + difference 3 0) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA670 + difference 0 3) (sourceB670 + difference 3 0) sourceC670) = raw11347 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11347; decide +kernel
    rw [ha]
    exact (canonical11347 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA670 + difference 0 4) (sourceB670 + difference 4 0) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA670 + difference 0 4) (sourceB670 + difference 4 0) sourceC670) = raw11348 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11348; decide +kernel
    rw [ha]
    exact (canonical11348 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA670 + difference 0 5) (sourceB670 + difference 5 0) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3911) := by
    have ha : (tripleCharges (sourceA670 + difference 0 5) (sourceB670 + difference 5 0) sourceC670) = raw11349 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11349; decide +kernel
    rw [ha]
    exact (canonical11349 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA670 + difference 1 0) (sourceB670 + difference 0 1) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA670 + difference 1 0) (sourceB670 + difference 0 1) sourceC670) = raw11350 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11350; decide +kernel
    rw [ha]
    exact (canonical11350 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA670 + difference 1 2) (sourceB670 + difference 2 1) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA670 + difference 1 2) (sourceB670 + difference 2 1) sourceC670) = raw11351 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11351; decide +kernel
    rw [ha]
    exact (canonical11351 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA670 + difference 1 3) (sourceB670 + difference 3 1) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1909) := by
    have ha : (tripleCharges (sourceA670 + difference 1 3) (sourceB670 + difference 3 1) sourceC670) = raw11352 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11352; decide +kernel
    rw [ha]
    exact (canonical11352 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA670 + difference 1 4) (sourceB670 + difference 4 1) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA670 + difference 1 4) (sourceB670 + difference 4 1) sourceC670) = raw11353 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11353; decide +kernel
    rw [ha]
    exact (canonical11353 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA670 + difference 1 5) (sourceB670 + difference 5 1) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA670 + difference 1 5) (sourceB670 + difference 5 1) sourceC670) = raw11354 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11354; decide +kernel
    rw [ha]
    exact (canonical11354 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA670 + difference 2 0) (sourceB670 + difference 0 2) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA670 + difference 2 0) (sourceB670 + difference 0 2) sourceC670) = raw11355 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11355; decide +kernel
    rw [ha]
    exact (canonical11355 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA670 + difference 2 1) (sourceB670 + difference 1 2) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA670 + difference 2 1) (sourceB670 + difference 1 2) sourceC670) = raw11356 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11356; decide +kernel
    rw [ha]
    exact (canonical11356 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA670 + difference 2 3) (sourceB670 + difference 3 2) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1909) := by
    have ha : (tripleCharges (sourceA670 + difference 2 3) (sourceB670 + difference 3 2) sourceC670) = raw11357 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11357; decide +kernel
    rw [ha]
    exact (canonical11357 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA670 + difference 2 4) (sourceB670 + difference 4 2) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA670 + difference 2 4) (sourceB670 + difference 4 2) sourceC670) = raw11358 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11358; decide +kernel
    rw [ha]
    exact (canonical11358 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA670 + difference 2 5) (sourceB670 + difference 5 2) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA670 + difference 2 5) (sourceB670 + difference 5 2) sourceC670) = raw11359 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11359; decide +kernel
    rw [ha]
    exact (canonical11359 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA670 + difference 3 0) (sourceB670 + difference 0 3) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA670 + difference 3 0) (sourceB670 + difference 0 3) sourceC670) = raw11360 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11360; decide +kernel
    rw [ha]
    exact (canonical11360 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA670 + difference 3 1) (sourceB670 + difference 1 3) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA670 + difference 3 1) (sourceB670 + difference 1 3) sourceC670) = raw11361 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11361; decide +kernel
    rw [ha]
    exact (canonical11361 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA670 + difference 3 2) (sourceB670 + difference 2 3) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA670 + difference 3 2) (sourceB670 + difference 2 3) sourceC670) = raw11362 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11362; decide +kernel
    rw [ha]
    exact (canonical11362 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA670 + difference 3 4) (sourceB670 + difference 4 3) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA670 + difference 3 4) (sourceB670 + difference 4 3) sourceC670) = raw11363 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11363; decide +kernel
    rw [ha]
    exact (canonical11363 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA670 + difference 3 5) (sourceB670 + difference 5 3) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA670 + difference 3 5) (sourceB670 + difference 5 3) sourceC670) = raw11364 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11364; decide +kernel
    rw [ha]
    exact (canonical11364 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA670 + difference 4 0) (sourceB670 + difference 0 4) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA670 + difference 4 0) (sourceB670 + difference 0 4) sourceC670) = raw11365 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11365; decide +kernel
    rw [ha]
    exact (canonical11365 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA670 + difference 4 1) (sourceB670 + difference 1 4) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA670 + difference 4 1) (sourceB670 + difference 1 4) sourceC670) = raw11366 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11366; decide +kernel
    rw [ha]
    exact (canonical11366 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA670 + difference 4 2) (sourceB670 + difference 2 4) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA670 + difference 4 2) (sourceB670 + difference 2 4) sourceC670) = raw11367 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11367; decide +kernel
    rw [ha]
    exact (canonical11367 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA670 + difference 4 3) (sourceB670 + difference 3 4) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1901) := by
    have ha : (tripleCharges (sourceA670 + difference 4 3) (sourceB670 + difference 3 4) sourceC670) = raw11368 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11368; decide +kernel
    rw [ha]
    exact (canonical11368 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA670 + difference 4 5) (sourceB670 + difference 5 4) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA670 + difference 4 5) (sourceB670 + difference 5 4) sourceC670) = raw11369 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11369; decide +kernel
    rw [ha]
    exact (canonical11369 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA670 + difference 5 0) (sourceB670 + difference 0 5) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA670 + difference 5 0) (sourceB670 + difference 0 5) sourceC670) = raw11370 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11370; decide +kernel
    rw [ha]
    exact (canonical11370 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA670 + difference 5 1) (sourceB670 + difference 1 5) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA670 + difference 5 1) (sourceB670 + difference 1 5) sourceC670) = raw11371 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11371; decide +kernel
    rw [ha]
    exact (canonical11371 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA670 + difference 5 2) (sourceB670 + difference 2 5) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA670 + difference 5 2) (sourceB670 + difference 2 5) sourceC670) = raw11372 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11372; decide +kernel
    rw [ha]
    exact (canonical11372 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA670 + difference 5 3) (sourceB670 + difference 3 5) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA670 + difference 5 3) (sourceB670 + difference 3 5) sourceC670) = raw11373 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11373; decide +kernel
    rw [ha]
    exact (canonical11373 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA670 + difference 5 4) (sourceB670 + difference 4 5) sourceC670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA670 + difference 5 4) (sourceB670 + difference 4 5) sourceC670) = raw11374 := by
      apply Matrix.ext; unfold tripleCharges sourceA670 sourceB670 sourceC670 difference raw11374; decide +kernel
    rw [ha]
    exact (canonical11374 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA670 sourceB670 sourceC670
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm670, Integer.Sparse.eval]
  linarith only [hs]

def sourceA671 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB671 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC671 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm671 : Integer.Sparse Master := [(Sum.inr 4455, 1), (Sum.inr 4457, 1), (Sum.inr 4459, 2), (Sum.inr 4495, 1), (Sum.inr 4801, 1), (Sum.inr 4803, 2), (Sum.inr 4831, 1), (Sum.inr 4863, 1), (Sum.inr 4865, 1), (Sum.inr 4867, 2), (Sum.inr 4885, 1), (Sum.inr 4888, 2), (Sum.inr 4889, 1), (Sum.inr 4891, 2), (Sum.inr 4894, 2), (Sum.inr 4895, 2), (Sum.inr 4896, 2), (Sum.inr 5250, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5293, 2)]

theorem sourceEq671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm671 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA671 + difference 0 1) (sourceB671 + difference 1 0) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA671 + difference 0 1) (sourceB671 + difference 1 0) sourceC671) = raw7225 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw7225; decide +kernel
    rw [ha]
    exact (canonical7225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA671 + difference 0 2) (sourceB671 + difference 2 0) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA671 + difference 0 2) (sourceB671 + difference 2 0) sourceC671) = raw7923 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw7923; decide +kernel
    rw [ha]
    exact (canonical7923 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA671 + difference 0 3) (sourceB671 + difference 3 0) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA671 + difference 0 3) (sourceB671 + difference 3 0) sourceC671) = raw9904 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw9904; decide +kernel
    rw [ha]
    exact (canonical9904 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA671 + difference 0 4) (sourceB671 + difference 4 0) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA671 + difference 0 4) (sourceB671 + difference 4 0) sourceC671) = raw9041 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw9041; decide +kernel
    rw [ha]
    exact (canonical9041 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA671 + difference 0 5) (sourceB671 + difference 5 0) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA671 + difference 0 5) (sourceB671 + difference 5 0) sourceC671) = raw5660 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw5660; decide +kernel
    rw [ha]
    exact (canonical5660 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA671 + difference 1 0) (sourceB671 + difference 0 1) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA671 + difference 1 0) (sourceB671 + difference 0 1) sourceC671) = raw10967 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw10967; decide +kernel
    rw [ha]
    exact (canonical10967 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA671 + difference 1 2) (sourceB671 + difference 2 1) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA671 + difference 1 2) (sourceB671 + difference 2 1) sourceC671) = raw11375 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw11375; decide +kernel
    rw [ha]
    exact (canonical11375 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA671 + difference 1 3) (sourceB671 + difference 3 1) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA671 + difference 1 3) (sourceB671 + difference 3 1) sourceC671) = raw10968 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw10968; decide +kernel
    rw [ha]
    exact (canonical10968 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA671 + difference 1 4) (sourceB671 + difference 4 1) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA671 + difference 1 4) (sourceB671 + difference 4 1) sourceC671) = raw10969 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw10969; decide +kernel
    rw [ha]
    exact (canonical10969 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA671 + difference 1 5) (sourceB671 + difference 5 1) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA671 + difference 1 5) (sourceB671 + difference 5 1) sourceC671) = raw5665 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw5665; decide +kernel
    rw [ha]
    exact (canonical5665 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA671 + difference 2 0) (sourceB671 + difference 0 2) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA671 + difference 2 0) (sourceB671 + difference 0 2) sourceC671) = raw11376 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw11376; decide +kernel
    rw [ha]
    exact (canonical11376 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA671 + difference 2 1) (sourceB671 + difference 1 2) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA671 + difference 2 1) (sourceB671 + difference 1 2) sourceC671) = raw11377 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw11377; decide +kernel
    rw [ha]
    exact (canonical11377 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA671 + difference 2 3) (sourceB671 + difference 3 2) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA671 + difference 2 3) (sourceB671 + difference 3 2) sourceC671) = raw11378 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw11378; decide +kernel
    rw [ha]
    exact (canonical11378 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA671 + difference 2 4) (sourceB671 + difference 4 2) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA671 + difference 2 4) (sourceB671 + difference 4 2) sourceC671) = raw11379 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw11379; decide +kernel
    rw [ha]
    exact (canonical11379 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA671 + difference 2 5) (sourceB671 + difference 5 2) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA671 + difference 2 5) (sourceB671 + difference 5 2) sourceC671) = raw5670 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw5670; decide +kernel
    rw [ha]
    exact (canonical5670 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA671 + difference 3 0) (sourceB671 + difference 0 3) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA671 + difference 3 0) (sourceB671 + difference 0 3) sourceC671) = raw5683 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw5683; decide +kernel
    rw [ha]
    exact (canonical5683 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA671 + difference 3 1) (sourceB671 + difference 1 3) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA671 + difference 3 1) (sourceB671 + difference 1 3) sourceC671) = raw5684 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw5684; decide +kernel
    rw [ha]
    exact (canonical5684 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA671 + difference 3 2) (sourceB671 + difference 2 3) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA671 + difference 3 2) (sourceB671 + difference 2 3) sourceC671) = raw5685 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw5685; decide +kernel
    rw [ha]
    exact (canonical5685 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA671 + difference 3 4) (sourceB671 + difference 4 3) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA671 + difference 3 4) (sourceB671 + difference 4 3) sourceC671) = raw5687 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw5687; decide +kernel
    rw [ha]
    exact (canonical5687 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA671 + difference 3 5) (sourceB671 + difference 5 3) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA671 + difference 3 5) (sourceB671 + difference 5 3) sourceC671) = raw9236 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw9236; decide +kernel
    rw [ha]
    exact (canonical9236 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA671 + difference 4 0) (sourceB671 + difference 0 4) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA671 + difference 4 0) (sourceB671 + difference 0 4) sourceC671) = raw11172 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw11172; decide +kernel
    rw [ha]
    exact (canonical11172 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA671 + difference 4 1) (sourceB671 + difference 1 4) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA671 + difference 4 1) (sourceB671 + difference 1 4) sourceC671) = raw11173 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw11173; decide +kernel
    rw [ha]
    exact (canonical11173 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA671 + difference 4 2) (sourceB671 + difference 2 4) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA671 + difference 4 2) (sourceB671 + difference 2 4) sourceC671) = raw9906 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw9906; decide +kernel
    rw [ha]
    exact (canonical9906 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA671 + difference 4 3) (sourceB671 + difference 3 4) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA671 + difference 4 3) (sourceB671 + difference 3 4) sourceC671) = raw9901 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw9901; decide +kernel
    rw [ha]
    exact (canonical9901 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA671 + difference 4 5) (sourceB671 + difference 5 4) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA671 + difference 4 5) (sourceB671 + difference 5 4) sourceC671) = raw5681 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw5681; decide +kernel
    rw [ha]
    exact (canonical5681 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA671 + difference 5 0) (sourceB671 + difference 0 5) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA671 + difference 5 0) (sourceB671 + difference 0 5) sourceC671) = raw11380 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw11380; decide +kernel
    rw [ha]
    exact (canonical11380 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA671 + difference 5 1) (sourceB671 + difference 1 5) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA671 + difference 5 1) (sourceB671 + difference 1 5) sourceC671) = raw11381 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw11381; decide +kernel
    rw [ha]
    exact (canonical11381 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA671 + difference 5 2) (sourceB671 + difference 2 5) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA671 + difference 5 2) (sourceB671 + difference 2 5) sourceC671) = raw9668 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw9668; decide +kernel
    rw [ha]
    exact (canonical9668 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA671 + difference 5 3) (sourceB671 + difference 3 5) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA671 + difference 5 3) (sourceB671 + difference 3 5) sourceC671) = raw10151 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw10151; decide +kernel
    rw [ha]
    exact (canonical10151 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA671 + difference 5 4) (sourceB671 + difference 4 5) sourceC671) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA671 + difference 5 4) (sourceB671 + difference 4 5) sourceC671) = raw9662 := by
      apply Matrix.ext; unfold tripleCharges sourceA671 sourceB671 sourceC671 difference raw9662; decide +kernel
    rw [ha]
    exact (canonical9662 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA671 sourceB671 sourceC671
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm671, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
