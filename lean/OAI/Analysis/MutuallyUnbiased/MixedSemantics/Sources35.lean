import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical110
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical142
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical144
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical147
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical148
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical149
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical150
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1120 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceB1120 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1120 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceForm1120 : Integer.Sparse Master := [(Sum.inr 5249, 1), (Sum.inr 5251, 1), (Sum.inr 5255, 2), (Sum.inr 5281, 1), (Sum.inr 5401, 2), (Sum.inr 5403, 1), (Sum.inr 5408, 1), (Sum.inr 5414, 1), (Sum.inr 5424, 2), (Sum.inr 5429, 1), (Sum.inr 5430, 2), (Sum.inr 5431, 1), (Sum.inr 5439, 1), (Sum.inr 5470, 2), (Sum.inr 5472, 1), (Sum.inr 5478, 2), (Sum.inr 5480, 2), (Sum.inr 5482, 2), (Sum.inr 5484, 2), (Sum.inr 5485, 1), (Sum.inr 5486, 1)]

theorem sourceEq1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1120 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 1) (sourceB1120 + difference 1 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 1) (sourceB1120 + difference 1 0) sourceC1120) = raw18863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18863; decide +kernel
    rw [ha]
    exact (canonical18863 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 2) (sourceB1120 + difference 2 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 2) (sourceB1120 + difference 2 0) sourceC1120) = raw18864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18864; decide +kernel
    rw [ha]
    exact (canonical18864 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 3) (sourceB1120 + difference 3 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 3) (sourceB1120 + difference 3 0) sourceC1120) = raw18865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18865; decide +kernel
    rw [ha]
    exact (canonical18865 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 4) (sourceB1120 + difference 4 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 4) (sourceB1120 + difference 4 0) sourceC1120) = raw18866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18866; decide +kernel
    rw [ha]
    exact (canonical18866 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 5) (sourceB1120 + difference 5 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 5) (sourceB1120 + difference 5 0) sourceC1120) = raw18867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18867; decide +kernel
    rw [ha]
    exact (canonical18867 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 0) (sourceB1120 + difference 0 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 0) (sourceB1120 + difference 0 1) sourceC1120) = raw18868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18868; decide +kernel
    rw [ha]
    exact (canonical18868 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 2) (sourceB1120 + difference 2 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 2) (sourceB1120 + difference 2 1) sourceC1120) = raw18869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18869; decide +kernel
    rw [ha]
    exact (canonical18869 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 3) (sourceB1120 + difference 3 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 3) (sourceB1120 + difference 3 1) sourceC1120) = raw18870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18870; decide +kernel
    rw [ha]
    exact (canonical18870 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 4) (sourceB1120 + difference 4 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 4) (sourceB1120 + difference 4 1) sourceC1120) = raw18871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18871; decide +kernel
    rw [ha]
    exact (canonical18871 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 5) (sourceB1120 + difference 5 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 5) (sourceB1120 + difference 5 1) sourceC1120) = raw18872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18872; decide +kernel
    rw [ha]
    exact (canonical18872 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 0) (sourceB1120 + difference 0 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 0) (sourceB1120 + difference 0 2) sourceC1120) = raw18873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18873; decide +kernel
    rw [ha]
    exact (canonical18873 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 1) (sourceB1120 + difference 1 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 1) (sourceB1120 + difference 1 2) sourceC1120) = raw18874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18874; decide +kernel
    rw [ha]
    exact (canonical18874 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 3) (sourceB1120 + difference 3 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 3) (sourceB1120 + difference 3 2) sourceC1120) = raw18875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18875; decide +kernel
    rw [ha]
    exact (canonical18875 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 4) (sourceB1120 + difference 4 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 4) (sourceB1120 + difference 4 2) sourceC1120) = raw18876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18876; decide +kernel
    rw [ha]
    exact (canonical18876 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 5) (sourceB1120 + difference 5 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 5) (sourceB1120 + difference 5 2) sourceC1120) = raw18877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18877; decide +kernel
    rw [ha]
    exact (canonical18877 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 0) (sourceB1120 + difference 0 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 0) (sourceB1120 + difference 0 3) sourceC1120) = raw18878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18878; decide +kernel
    rw [ha]
    exact (canonical18878 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 1) (sourceB1120 + difference 1 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 1) (sourceB1120 + difference 1 3) sourceC1120) = raw18879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18879; decide +kernel
    rw [ha]
    exact (canonical18879 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 2) (sourceB1120 + difference 2 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 2) (sourceB1120 + difference 2 3) sourceC1120) = raw18880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18880; decide +kernel
    rw [ha]
    exact (canonical18880 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 4) (sourceB1120 + difference 4 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 4) (sourceB1120 + difference 4 3) sourceC1120) = raw18881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18881; decide +kernel
    rw [ha]
    exact (canonical18881 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 5) (sourceB1120 + difference 5 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 5) (sourceB1120 + difference 5 3) sourceC1120) = raw18882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18882; decide +kernel
    rw [ha]
    exact (canonical18882 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 0) (sourceB1120 + difference 0 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 0) (sourceB1120 + difference 0 4) sourceC1120) = raw18883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18883; decide +kernel
    rw [ha]
    exact (canonical18883 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 1) (sourceB1120 + difference 1 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 1) (sourceB1120 + difference 1 4) sourceC1120) = raw18884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18884; decide +kernel
    rw [ha]
    exact (canonical18884 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 2) (sourceB1120 + difference 2 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 2) (sourceB1120 + difference 2 4) sourceC1120) = raw18885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18885; decide +kernel
    rw [ha]
    exact (canonical18885 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 3) (sourceB1120 + difference 3 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 3) (sourceB1120 + difference 3 4) sourceC1120) = raw18886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18886; decide +kernel
    rw [ha]
    exact (canonical18886 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 5) (sourceB1120 + difference 5 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 5) (sourceB1120 + difference 5 4) sourceC1120) = raw18887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18887; decide +kernel
    rw [ha]
    exact (canonical18887 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 0) (sourceB1120 + difference 0 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 0) (sourceB1120 + difference 0 5) sourceC1120) = raw18888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18888; decide +kernel
    rw [ha]
    exact (canonical18888 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 1) (sourceB1120 + difference 1 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 1) (sourceB1120 + difference 1 5) sourceC1120) = raw18889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18889; decide +kernel
    rw [ha]
    exact (canonical18889 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 2) (sourceB1120 + difference 2 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 2) (sourceB1120 + difference 2 5) sourceC1120) = raw18890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18890; decide +kernel
    rw [ha]
    exact (canonical18890 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 3) (sourceB1120 + difference 3 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 3) (sourceB1120 + difference 3 5) sourceC1120) = raw18891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18891; decide +kernel
    rw [ha]
    exact (canonical18891 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 4) (sourceB1120 + difference 4 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 4) (sourceB1120 + difference 4 5) sourceC1120) = raw18892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18892; decide +kernel
    rw [ha]
    exact (canonical18892 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1120 sourceB1120 sourceC1120
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1120, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1121 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceB1121 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1121 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceForm1121 : Integer.Sparse Master := [(Sum.inr 2708, 1), (Sum.inr 2710, 1), (Sum.inr 2718, 2), (Sum.inr 2750, 1), (Sum.inr 3804, 2), (Sum.inr 3806, 1), (Sum.inr 3810, 1), (Sum.inr 3849, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 2), (Sum.inr 3954, 1), (Sum.inr 3955, 2), (Sum.inr 3957, 1), (Sum.inr 3978, 2), (Sum.inr 3980, 2), (Sum.inr 3983, 2), (Sum.inr 3985, 1), (Sum.inr 3990, 2), (Sum.inr 3994, 2), (Sum.inr 3998, 1), (Sum.inr 4012, 1)]

theorem sourceEq1121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1121 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1121 + difference 0 1) (sourceB1121 + difference 1 0) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA1121 + difference 0 1) (sourceB1121 + difference 1 0) sourceC1121) = raw18893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18893; decide +kernel
    rw [ha]
    exact (canonical18893 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1121 + difference 0 2) (sourceB1121 + difference 2 0) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA1121 + difference 0 2) (sourceB1121 + difference 2 0) sourceC1121) = raw18894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18894; decide +kernel
    rw [ha]
    exact (canonical18894 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1121 + difference 0 3) (sourceB1121 + difference 3 0) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1121 + difference 0 3) (sourceB1121 + difference 3 0) sourceC1121) = raw18895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18895; decide +kernel
    rw [ha]
    exact (canonical18895 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1121 + difference 0 4) (sourceB1121 + difference 4 0) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA1121 + difference 0 4) (sourceB1121 + difference 4 0) sourceC1121) = raw18896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18896; decide +kernel
    rw [ha]
    exact (canonical18896 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1121 + difference 0 5) (sourceB1121 + difference 5 0) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA1121 + difference 0 5) (sourceB1121 + difference 5 0) sourceC1121) = raw18897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18897; decide +kernel
    rw [ha]
    exact (canonical18897 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1121 + difference 1 0) (sourceB1121 + difference 0 1) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA1121 + difference 1 0) (sourceB1121 + difference 0 1) sourceC1121) = raw18898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18898; decide +kernel
    rw [ha]
    exact (canonical18898 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1121 + difference 1 2) (sourceB1121 + difference 2 1) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA1121 + difference 1 2) (sourceB1121 + difference 2 1) sourceC1121) = raw18899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18899; decide +kernel
    rw [ha]
    exact (canonical18899 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1121 + difference 1 3) (sourceB1121 + difference 3 1) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA1121 + difference 1 3) (sourceB1121 + difference 3 1) sourceC1121) = raw18900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18900; decide +kernel
    rw [ha]
    exact (canonical18900 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1121 + difference 1 4) (sourceB1121 + difference 4 1) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA1121 + difference 1 4) (sourceB1121 + difference 4 1) sourceC1121) = raw18901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18901; decide +kernel
    rw [ha]
    exact (canonical18901 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1121 + difference 1 5) (sourceB1121 + difference 5 1) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA1121 + difference 1 5) (sourceB1121 + difference 5 1) sourceC1121) = raw18902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18902; decide +kernel
    rw [ha]
    exact (canonical18902 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1121 + difference 2 0) (sourceB1121 + difference 0 2) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3810) := by
    have ha : (tripleCharges (sourceA1121 + difference 2 0) (sourceB1121 + difference 0 2) sourceC1121) = raw18903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18903; decide +kernel
    rw [ha]
    exact (canonical18903 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1121 + difference 2 1) (sourceB1121 + difference 1 2) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA1121 + difference 2 1) (sourceB1121 + difference 1 2) sourceC1121) = raw18904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18904; decide +kernel
    rw [ha]
    exact (canonical18904 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1121 + difference 2 3) (sourceB1121 + difference 3 2) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1121 + difference 2 3) (sourceB1121 + difference 3 2) sourceC1121) = raw18905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18905; decide +kernel
    rw [ha]
    exact (canonical18905 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1121 + difference 2 4) (sourceB1121 + difference 4 2) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA1121 + difference 2 4) (sourceB1121 + difference 4 2) sourceC1121) = raw18906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18906; decide +kernel
    rw [ha]
    exact (canonical18906 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1121 + difference 2 5) (sourceB1121 + difference 5 2) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA1121 + difference 2 5) (sourceB1121 + difference 5 2) sourceC1121) = raw18907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18907; decide +kernel
    rw [ha]
    exact (canonical18907 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1121 + difference 3 0) (sourceB1121 + difference 0 3) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1121 + difference 3 0) (sourceB1121 + difference 0 3) sourceC1121) = raw18908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18908; decide +kernel
    rw [ha]
    exact (canonical18908 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1121 + difference 3 1) (sourceB1121 + difference 1 3) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1121 + difference 3 1) (sourceB1121 + difference 1 3) sourceC1121) = raw18909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18909; decide +kernel
    rw [ha]
    exact (canonical18909 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1121 + difference 3 2) (sourceB1121 + difference 2 3) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1121 + difference 3 2) (sourceB1121 + difference 2 3) sourceC1121) = raw18910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18910; decide +kernel
    rw [ha]
    exact (canonical18910 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1121 + difference 3 4) (sourceB1121 + difference 4 3) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1121 + difference 3 4) (sourceB1121 + difference 4 3) sourceC1121) = raw18911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18911; decide +kernel
    rw [ha]
    exact (canonical18911 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1121 + difference 3 5) (sourceB1121 + difference 5 3) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1121 + difference 3 5) (sourceB1121 + difference 5 3) sourceC1121) = raw18912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18912; decide +kernel
    rw [ha]
    exact (canonical18912 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1121 + difference 4 0) (sourceB1121 + difference 0 4) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1121 + difference 4 0) (sourceB1121 + difference 0 4) sourceC1121) = raw18913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18913; decide +kernel
    rw [ha]
    exact (canonical18913 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1121 + difference 4 1) (sourceB1121 + difference 1 4) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1121 + difference 4 1) (sourceB1121 + difference 1 4) sourceC1121) = raw18914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18914; decide +kernel
    rw [ha]
    exact (canonical18914 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1121 + difference 4 2) (sourceB1121 + difference 2 4) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1121 + difference 4 2) (sourceB1121 + difference 2 4) sourceC1121) = raw18915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18915; decide +kernel
    rw [ha]
    exact (canonical18915 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1121 + difference 4 3) (sourceB1121 + difference 3 4) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1121 + difference 4 3) (sourceB1121 + difference 3 4) sourceC1121) = raw18916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18916; decide +kernel
    rw [ha]
    exact (canonical18916 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1121 + difference 4 5) (sourceB1121 + difference 5 4) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1121 + difference 4 5) (sourceB1121 + difference 5 4) sourceC1121) = raw18917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18917; decide +kernel
    rw [ha]
    exact (canonical18917 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1121 + difference 5 0) (sourceB1121 + difference 0 5) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA1121 + difference 5 0) (sourceB1121 + difference 0 5) sourceC1121) = raw18918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18918; decide +kernel
    rw [ha]
    exact (canonical18918 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1121 + difference 5 1) (sourceB1121 + difference 1 5) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA1121 + difference 5 1) (sourceB1121 + difference 1 5) sourceC1121) = raw18919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18919; decide +kernel
    rw [ha]
    exact (canonical18919 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1121 + difference 5 2) (sourceB1121 + difference 2 5) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3985) := by
    have ha : (tripleCharges (sourceA1121 + difference 5 2) (sourceB1121 + difference 2 5) sourceC1121) = raw18920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18920; decide +kernel
    rw [ha]
    exact (canonical18920 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1121 + difference 5 3) (sourceB1121 + difference 3 5) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1121 + difference 5 3) (sourceB1121 + difference 3 5) sourceC1121) = raw18921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18921; decide +kernel
    rw [ha]
    exact (canonical18921 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1121 + difference 5 4) (sourceB1121 + difference 4 5) sourceC1121) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1121 + difference 5 4) (sourceB1121 + difference 4 5) sourceC1121) = raw18922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1121 sourceB1121 sourceC1121 difference raw18922; decide +kernel
    rw [ha]
    exact (canonical18922 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1121 sourceB1121 sourceC1121
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1121, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1122 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1122 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1122 : Charge := ![1, 1, 0, -2, -1, 1]
def sourceForm1122 : Integer.Sparse Master := [(Sum.inr 5160, 1), (Sum.inr 5161, 1), (Sum.inr 5164, 1), (Sum.inr 5170, 1), (Sum.inr 5255, 1), (Sum.inr 5260, 1), (Sum.inr 5269, 1), (Sum.inr 5289, 2), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 1), (Sum.inr 5430, 1), (Sum.inr 5438, 2), (Sum.inr 5439, 1), (Sum.inr 5446, 1), (Sum.inr 5461, 1), (Sum.inr 5463, 1), (Sum.inr 5470, 1), (Sum.inr 5473, 1), (Sum.inr 5478, 1), (Sum.inr 5480, 2), (Sum.inr 5481, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 2), (Sum.inr 5486, 1)]

theorem sourceEq1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1122 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1122 + difference 0 1) (sourceB1122 + difference 1 0) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1122 + difference 0 1) (sourceB1122 + difference 1 0) sourceC1122) = raw18923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18923; decide +kernel
    rw [ha]
    exact (canonical18923 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1122 + difference 0 2) (sourceB1122 + difference 2 0) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1122 + difference 0 2) (sourceB1122 + difference 2 0) sourceC1122) = raw18924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18924; decide +kernel
    rw [ha]
    exact (canonical18924 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1122 + difference 0 3) (sourceB1122 + difference 3 0) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1122 + difference 0 3) (sourceB1122 + difference 3 0) sourceC1122) = raw18925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18925; decide +kernel
    rw [ha]
    exact (canonical18925 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1122 + difference 0 4) (sourceB1122 + difference 4 0) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1122 + difference 0 4) (sourceB1122 + difference 4 0) sourceC1122) = raw18926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18926; decide +kernel
    rw [ha]
    exact (canonical18926 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1122 + difference 0 5) (sourceB1122 + difference 5 0) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1122 + difference 0 5) (sourceB1122 + difference 5 0) sourceC1122) = raw18927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18927; decide +kernel
    rw [ha]
    exact (canonical18927 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1122 + difference 1 0) (sourceB1122 + difference 0 1) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA1122 + difference 1 0) (sourceB1122 + difference 0 1) sourceC1122) = raw18928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18928; decide +kernel
    rw [ha]
    exact (canonical18928 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1122 + difference 1 2) (sourceB1122 + difference 2 1) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1122 + difference 1 2) (sourceB1122 + difference 2 1) sourceC1122) = raw18929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18929; decide +kernel
    rw [ha]
    exact (canonical18929 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1122 + difference 1 3) (sourceB1122 + difference 3 1) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1122 + difference 1 3) (sourceB1122 + difference 3 1) sourceC1122) = raw18930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18930; decide +kernel
    rw [ha]
    exact (canonical18930 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1122 + difference 1 4) (sourceB1122 + difference 4 1) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1122 + difference 1 4) (sourceB1122 + difference 4 1) sourceC1122) = raw18931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18931; decide +kernel
    rw [ha]
    exact (canonical18931 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1122 + difference 1 5) (sourceB1122 + difference 5 1) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1122 + difference 1 5) (sourceB1122 + difference 5 1) sourceC1122) = raw18932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18932; decide +kernel
    rw [ha]
    exact (canonical18932 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1122 + difference 2 0) (sourceB1122 + difference 0 2) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA1122 + difference 2 0) (sourceB1122 + difference 0 2) sourceC1122) = raw18933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18933; decide +kernel
    rw [ha]
    exact (canonical18933 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1122 + difference 2 1) (sourceB1122 + difference 1 2) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5461) := by
    have ha : (tripleCharges (sourceA1122 + difference 2 1) (sourceB1122 + difference 1 2) sourceC1122) = raw18934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18934; decide +kernel
    rw [ha]
    exact (canonical18934 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1122 + difference 2 3) (sourceB1122 + difference 3 2) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1122 + difference 2 3) (sourceB1122 + difference 3 2) sourceC1122) = raw18935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18935; decide +kernel
    rw [ha]
    exact (canonical18935 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1122 + difference 2 4) (sourceB1122 + difference 4 2) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1122 + difference 2 4) (sourceB1122 + difference 4 2) sourceC1122) = raw18936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18936; decide +kernel
    rw [ha]
    exact (canonical18936 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1122 + difference 2 5) (sourceB1122 + difference 5 2) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1122 + difference 2 5) (sourceB1122 + difference 5 2) sourceC1122) = raw18937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18937; decide +kernel
    rw [ha]
    exact (canonical18937 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1122 + difference 3 0) (sourceB1122 + difference 0 3) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1122 + difference 3 0) (sourceB1122 + difference 0 3) sourceC1122) = raw18938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18938; decide +kernel
    rw [ha]
    exact (canonical18938 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1122 + difference 3 1) (sourceB1122 + difference 1 3) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA1122 + difference 3 1) (sourceB1122 + difference 1 3) sourceC1122) = raw18939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18939; decide +kernel
    rw [ha]
    exact (canonical18939 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1122 + difference 3 2) (sourceB1122 + difference 2 3) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1122 + difference 3 2) (sourceB1122 + difference 2 3) sourceC1122) = raw18940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18940; decide +kernel
    rw [ha]
    exact (canonical18940 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1122 + difference 3 4) (sourceB1122 + difference 4 3) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1122 + difference 3 4) (sourceB1122 + difference 4 3) sourceC1122) = raw18941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18941; decide +kernel
    rw [ha]
    exact (canonical18941 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1122 + difference 3 5) (sourceB1122 + difference 5 3) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1122 + difference 3 5) (sourceB1122 + difference 5 3) sourceC1122) = raw18942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18942; decide +kernel
    rw [ha]
    exact (canonical18942 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1122 + difference 4 0) (sourceB1122 + difference 0 4) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA1122 + difference 4 0) (sourceB1122 + difference 0 4) sourceC1122) = raw18943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18943; decide +kernel
    rw [ha]
    exact (canonical18943 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1122 + difference 4 1) (sourceB1122 + difference 1 4) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5463) := by
    have ha : (tripleCharges (sourceA1122 + difference 4 1) (sourceB1122 + difference 1 4) sourceC1122) = raw18944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18944; decide +kernel
    rw [ha]
    exact (canonical18944 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1122 + difference 4 2) (sourceB1122 + difference 2 4) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1122 + difference 4 2) (sourceB1122 + difference 2 4) sourceC1122) = raw18945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18945; decide +kernel
    rw [ha]
    exact (canonical18945 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1122 + difference 4 3) (sourceB1122 + difference 3 4) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1122 + difference 4 3) (sourceB1122 + difference 3 4) sourceC1122) = raw18946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18946; decide +kernel
    rw [ha]
    exact (canonical18946 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1122 + difference 4 5) (sourceB1122 + difference 5 4) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1122 + difference 4 5) (sourceB1122 + difference 5 4) sourceC1122) = raw18947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18947; decide +kernel
    rw [ha]
    exact (canonical18947 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1122 + difference 5 0) (sourceB1122 + difference 0 5) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA1122 + difference 5 0) (sourceB1122 + difference 0 5) sourceC1122) = raw18948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18948; decide +kernel
    rw [ha]
    exact (canonical18948 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1122 + difference 5 1) (sourceB1122 + difference 1 5) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA1122 + difference 5 1) (sourceB1122 + difference 1 5) sourceC1122) = raw18949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18949; decide +kernel
    rw [ha]
    exact (canonical18949 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1122 + difference 5 2) (sourceB1122 + difference 2 5) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA1122 + difference 5 2) (sourceB1122 + difference 2 5) sourceC1122) = raw18950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18950; decide +kernel
    rw [ha]
    exact (canonical18950 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1122 + difference 5 3) (sourceB1122 + difference 3 5) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA1122 + difference 5 3) (sourceB1122 + difference 3 5) sourceC1122) = raw18951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18951; decide +kernel
    rw [ha]
    exact (canonical18951 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1122 + difference 5 4) (sourceB1122 + difference 4 5) sourceC1122) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA1122 + difference 5 4) (sourceB1122 + difference 4 5) sourceC1122) = raw18952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1122 sourceB1122 sourceC1122 difference raw18952; decide +kernel
    rw [ha]
    exact (canonical18952 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1122 sourceB1122 sourceC1122
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1122, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1123 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1123 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1123 : Charge := ![1, 1, 0, -2, -1, 1]
def sourceForm1123 : Integer.Sparse Master := [(Sum.inr 2718, 1), (Sum.inr 2719, 1), (Sum.inr 2724, 1), (Sum.inr 2736, 1), (Sum.inr 2763, 1), (Sum.inr 3558, 1), (Sum.inr 3565, 1), (Sum.inr 3572, 1), (Sum.inr 3606, 1), (Sum.inr 3804, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 1), (Sum.inr 3857, 1), (Sum.inr 3955, 1), (Sum.inr 3959, 1), (Sum.inr 3960, 1), (Sum.inr 3961, 1), (Sum.inr 3972, 1), (Sum.inr 3973, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 2), (Sum.inr 3979, 1), (Sum.inr 3983, 1), (Sum.inr 3984, 1), (Sum.inr 3985, 1), (Sum.inr 3993, 1), (Sum.inr 3997, 1), (Sum.inr 3998, 1), (Sum.inr 4012, 1)]

theorem sourceEq1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1123 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 1) (sourceB1123 + difference 1 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 1) (sourceB1123 + difference 1 0) sourceC1123) = raw18953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18953; decide +kernel
    rw [ha]
    exact (canonical18953 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 2) (sourceB1123 + difference 2 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 2) (sourceB1123 + difference 2 0) sourceC1123) = raw18954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18954; decide +kernel
    rw [ha]
    exact (canonical18954 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 3) (sourceB1123 + difference 3 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 3) (sourceB1123 + difference 3 0) sourceC1123) = raw18955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18955; decide +kernel
    rw [ha]
    exact (canonical18955 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 4) (sourceB1123 + difference 4 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 4) (sourceB1123 + difference 4 0) sourceC1123) = raw18956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18956; decide +kernel
    rw [ha]
    exact (canonical18956 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1123 + difference 0 5) (sourceB1123 + difference 5 0) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3985) := by
    have ha : (tripleCharges (sourceA1123 + difference 0 5) (sourceB1123 + difference 5 0) sourceC1123) = raw18957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18957; decide +kernel
    rw [ha]
    exact (canonical18957 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 0) (sourceB1123 + difference 0 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 0) (sourceB1123 + difference 0 1) sourceC1123) = raw18958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18958; decide +kernel
    rw [ha]
    exact (canonical18958 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 2) (sourceB1123 + difference 2 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 2) (sourceB1123 + difference 2 1) sourceC1123) = raw18959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18959; decide +kernel
    rw [ha]
    exact (canonical18959 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 3) (sourceB1123 + difference 3 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 3) (sourceB1123 + difference 3 1) sourceC1123) = raw18960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18960; decide +kernel
    rw [ha]
    exact (canonical18960 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 4) (sourceB1123 + difference 4 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 4) (sourceB1123 + difference 4 1) sourceC1123) = raw18961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18961; decide +kernel
    rw [ha]
    exact (canonical18961 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1123 + difference 1 5) (sourceB1123 + difference 5 1) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA1123 + difference 1 5) (sourceB1123 + difference 5 1) sourceC1123) = raw18962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18962; decide +kernel
    rw [ha]
    exact (canonical18962 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 0) (sourceB1123 + difference 0 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 0) (sourceB1123 + difference 0 2) sourceC1123) = raw18963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18963; decide +kernel
    rw [ha]
    exact (canonical18963 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 1) (sourceB1123 + difference 1 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 1) (sourceB1123 + difference 1 2) sourceC1123) = raw18964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18964; decide +kernel
    rw [ha]
    exact (canonical18964 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 3) (sourceB1123 + difference 3 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 3) (sourceB1123 + difference 3 2) sourceC1123) = raw18965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18965; decide +kernel
    rw [ha]
    exact (canonical18965 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 4) (sourceB1123 + difference 4 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 4) (sourceB1123 + difference 4 2) sourceC1123) = raw18966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18966; decide +kernel
    rw [ha]
    exact (canonical18966 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1123 + difference 2 5) (sourceB1123 + difference 5 2) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA1123 + difference 2 5) (sourceB1123 + difference 5 2) sourceC1123) = raw18967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18967; decide +kernel
    rw [ha]
    exact (canonical18967 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 0) (sourceB1123 + difference 0 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 0) (sourceB1123 + difference 0 3) sourceC1123) = raw18968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18968; decide +kernel
    rw [ha]
    exact (canonical18968 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 1) (sourceB1123 + difference 1 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 1) (sourceB1123 + difference 1 3) sourceC1123) = raw18969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18969; decide +kernel
    rw [ha]
    exact (canonical18969 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 2) (sourceB1123 + difference 2 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 2) (sourceB1123 + difference 2 3) sourceC1123) = raw18970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18970; decide +kernel
    rw [ha]
    exact (canonical18970 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 4) (sourceB1123 + difference 4 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 4) (sourceB1123 + difference 4 3) sourceC1123) = raw18971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18971; decide +kernel
    rw [ha]
    exact (canonical18971 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1123 + difference 3 5) (sourceB1123 + difference 5 3) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA1123 + difference 3 5) (sourceB1123 + difference 5 3) sourceC1123) = raw18972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18972; decide +kernel
    rw [ha]
    exact (canonical18972 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 0) (sourceB1123 + difference 0 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 0) (sourceB1123 + difference 0 4) sourceC1123) = raw18973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18973; decide +kernel
    rw [ha]
    exact (canonical18973 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 1) (sourceB1123 + difference 1 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3960) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 1) (sourceB1123 + difference 1 4) sourceC1123) = raw18974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18974; decide +kernel
    rw [ha]
    exact (canonical18974 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 2) (sourceB1123 + difference 2 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 2) (sourceB1123 + difference 2 4) sourceC1123) = raw18975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18975; decide +kernel
    rw [ha]
    exact (canonical18975 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 3) (sourceB1123 + difference 3 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 3) (sourceB1123 + difference 3 4) sourceC1123) = raw18976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18976; decide +kernel
    rw [ha]
    exact (canonical18976 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1123 + difference 4 5) (sourceB1123 + difference 5 4) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1123 + difference 4 5) (sourceB1123 + difference 5 4) sourceC1123) = raw18977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18977; decide +kernel
    rw [ha]
    exact (canonical18977 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 0) (sourceB1123 + difference 0 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 0) (sourceB1123 + difference 0 5) sourceC1123) = raw18978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18978; decide +kernel
    rw [ha]
    exact (canonical18978 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 1) (sourceB1123 + difference 1 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 1) (sourceB1123 + difference 1 5) sourceC1123) = raw18979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18979; decide +kernel
    rw [ha]
    exact (canonical18979 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 2) (sourceB1123 + difference 2 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 2) (sourceB1123 + difference 2 5) sourceC1123) = raw18980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18980; decide +kernel
    rw [ha]
    exact (canonical18980 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 3) (sourceB1123 + difference 3 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 3) (sourceB1123 + difference 3 5) sourceC1123) = raw18981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18981; decide +kernel
    rw [ha]
    exact (canonical18981 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1123 + difference 5 4) (sourceB1123 + difference 4 5) sourceC1123) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA1123 + difference 5 4) (sourceB1123 + difference 4 5) sourceC1123) = raw18982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1123 sourceB1123 sourceC1123 difference raw18982; decide +kernel
    rw [ha]
    exact (canonical18982 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1123 sourceB1123 sourceC1123
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1123, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1124 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1124 : Charge := ![1, 1, 0, -2, -1, 1]
def sourceC1124 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm1124 : Integer.Sparse Master := [(Sum.inr 5093, 2), (Sum.inr 5094, 1), (Sum.inr 5095, 2), (Sum.inr 5105, 2), (Sum.inr 5304, 2), (Sum.inr 5363, 2), (Sum.inr 5364, 1), (Sum.inr 5370, 2), (Sum.inr 5422, 2), (Sum.inr 5434, 2), (Sum.inr 5438, 2), (Sum.inr 5451, 2), (Sum.inr 5481, 2), (Sum.inr 5484, 2), (Sum.inr 5490, 1), (Sum.inr 5492, 2), (Sum.inr 5494, 1)]

theorem sourceEq1124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1124 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1124 + difference 0 1) (sourceB1124 + difference 1 0) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1124 + difference 0 1) (sourceB1124 + difference 1 0) sourceC1124) = raw18983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18983; decide +kernel
    rw [ha]
    exact (canonical18983 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1124 + difference 0 2) (sourceB1124 + difference 2 0) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1124 + difference 0 2) (sourceB1124 + difference 2 0) sourceC1124) = raw18984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18984; decide +kernel
    rw [ha]
    exact (canonical18984 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1124 + difference 0 3) (sourceB1124 + difference 3 0) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1124 + difference 0 3) (sourceB1124 + difference 3 0) sourceC1124) = raw18985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18985; decide +kernel
    rw [ha]
    exact (canonical18985 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1124 + difference 0 4) (sourceB1124 + difference 4 0) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1124 + difference 0 4) (sourceB1124 + difference 4 0) sourceC1124) = raw18986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18986; decide +kernel
    rw [ha]
    exact (canonical18986 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1124 + difference 0 5) (sourceB1124 + difference 5 0) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1124 + difference 0 5) (sourceB1124 + difference 5 0) sourceC1124) = raw18987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18987; decide +kernel
    rw [ha]
    exact (canonical18987 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1124 + difference 1 0) (sourceB1124 + difference 0 1) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA1124 + difference 1 0) (sourceB1124 + difference 0 1) sourceC1124) = raw8021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw8021; decide +kernel
    rw [ha]
    exact (canonical8021 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1124 + difference 1 2) (sourceB1124 + difference 2 1) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1124 + difference 1 2) (sourceB1124 + difference 2 1) sourceC1124) = raw13970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw13970; decide +kernel
    rw [ha]
    exact (canonical13970 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1124 + difference 1 3) (sourceB1124 + difference 3 1) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1124 + difference 1 3) (sourceB1124 + difference 3 1) sourceC1124) = raw8006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw8006; decide +kernel
    rw [ha]
    exact (canonical8006 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1124 + difference 1 4) (sourceB1124 + difference 4 1) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5494) := by
    have ha : (tripleCharges (sourceA1124 + difference 1 4) (sourceB1124 + difference 4 1) sourceC1124) = raw13971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw13971; decide +kernel
    rw [ha]
    exact (canonical13971 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1124 + difference 1 5) (sourceB1124 + difference 5 1) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1124 + difference 1 5) (sourceB1124 + difference 5 1) sourceC1124) = raw13972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw13972; decide +kernel
    rw [ha]
    exact (canonical13972 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1124 + difference 2 0) (sourceB1124 + difference 0 2) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA1124 + difference 2 0) (sourceB1124 + difference 0 2) sourceC1124) = raw13978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw13978; decide +kernel
    rw [ha]
    exact (canonical13978 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1124 + difference 2 1) (sourceB1124 + difference 1 2) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA1124 + difference 2 1) (sourceB1124 + difference 1 2) sourceC1124) = raw18988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18988; decide +kernel
    rw [ha]
    exact (canonical18988 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1124 + difference 2 3) (sourceB1124 + difference 3 2) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1124 + difference 2 3) (sourceB1124 + difference 3 2) sourceC1124) = raw18989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18989; decide +kernel
    rw [ha]
    exact (canonical18989 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1124 + difference 2 4) (sourceB1124 + difference 4 2) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1124 + difference 2 4) (sourceB1124 + difference 4 2) sourceC1124) = raw18990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18990; decide +kernel
    rw [ha]
    exact (canonical18990 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1124 + difference 2 5) (sourceB1124 + difference 5 2) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1124 + difference 2 5) (sourceB1124 + difference 5 2) sourceC1124) = raw18991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18991; decide +kernel
    rw [ha]
    exact (canonical18991 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1124 + difference 3 0) (sourceB1124 + difference 0 3) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA1124 + difference 3 0) (sourceB1124 + difference 0 3) sourceC1124) = raw13982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw13982; decide +kernel
    rw [ha]
    exact (canonical13982 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1124 + difference 3 1) (sourceB1124 + difference 1 3) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA1124 + difference 3 1) (sourceB1124 + difference 1 3) sourceC1124) = raw18992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18992; decide +kernel
    rw [ha]
    exact (canonical18992 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1124 + difference 3 2) (sourceB1124 + difference 2 3) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA1124 + difference 3 2) (sourceB1124 + difference 2 3) sourceC1124) = raw18993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18993; decide +kernel
    rw [ha]
    exact (canonical18993 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1124 + difference 3 4) (sourceB1124 + difference 4 3) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA1124 + difference 3 4) (sourceB1124 + difference 4 3) sourceC1124) = raw18994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18994; decide +kernel
    rw [ha]
    exact (canonical18994 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1124 + difference 3 5) (sourceB1124 + difference 5 3) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA1124 + difference 3 5) (sourceB1124 + difference 5 3) sourceC1124) = raw18995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18995; decide +kernel
    rw [ha]
    exact (canonical18995 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1124 + difference 4 0) (sourceB1124 + difference 0 4) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA1124 + difference 4 0) (sourceB1124 + difference 0 4) sourceC1124) = raw13987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw13987; decide +kernel
    rw [ha]
    exact (canonical13987 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1124 + difference 4 1) (sourceB1124 + difference 1 4) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA1124 + difference 4 1) (sourceB1124 + difference 1 4) sourceC1124) = raw18996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18996; decide +kernel
    rw [ha]
    exact (canonical18996 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1124 + difference 4 2) (sourceB1124 + difference 2 4) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA1124 + difference 4 2) (sourceB1124 + difference 2 4) sourceC1124) = raw18997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18997; decide +kernel
    rw [ha]
    exact (canonical18997 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1124 + difference 4 3) (sourceB1124 + difference 3 4) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1124 + difference 4 3) (sourceB1124 + difference 3 4) sourceC1124) = raw18998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18998; decide +kernel
    rw [ha]
    exact (canonical18998 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1124 + difference 4 5) (sourceB1124 + difference 5 4) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA1124 + difference 4 5) (sourceB1124 + difference 5 4) sourceC1124) = raw18999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw18999; decide +kernel
    rw [ha]
    exact (canonical18999 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1124 + difference 5 0) (sourceB1124 + difference 0 5) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA1124 + difference 5 0) (sourceB1124 + difference 0 5) sourceC1124) = raw8018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw8018; decide +kernel
    rw [ha]
    exact (canonical8018 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1124 + difference 5 1) (sourceB1124 + difference 1 5) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA1124 + difference 5 1) (sourceB1124 + difference 1 5) sourceC1124) = raw19000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw19000; decide +kernel
    rw [ha]
    exact (canonical19000 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1124 + difference 5 2) (sourceB1124 + difference 2 5) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1124 + difference 5 2) (sourceB1124 + difference 2 5) sourceC1124) = raw19001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw19001; decide +kernel
    rw [ha]
    exact (canonical19001 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1124 + difference 5 3) (sourceB1124 + difference 3 5) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1124 + difference 5 3) (sourceB1124 + difference 3 5) sourceC1124) = raw8002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw8002; decide +kernel
    rw [ha]
    exact (canonical8002 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1124 + difference 5 4) (sourceB1124 + difference 4 5) sourceC1124) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1124 + difference 5 4) (sourceB1124 + difference 4 5) sourceC1124) = raw19002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1124 sourceB1124 sourceC1124 difference raw19002; decide +kernel
    rw [ha]
    exact (canonical19002 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1124 sourceB1124 sourceC1124
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1124, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1125 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1125 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1125 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm1125 : Integer.Sparse Master := [(Sum.inr 4096, 1), (Sum.inr 5167, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 2), (Sum.inr 5292, 1), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5434, 2), (Sum.inr 5464, 1), (Sum.inr 5465, 2), (Sum.inr 5476, 2), (Sum.inr 5482, 3), (Sum.inr 5483, 2), (Sum.inr 5486, 2), (Sum.inr 5487, 2), (Sum.inr 5490, 2), (Sum.inr 5493, 1), (Sum.inr 5497, 1), (Sum.inr 5499, 2)]

theorem sourceEq1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1125 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1125 + difference 0 1) (sourceB1125 + difference 1 0) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1125 + difference 0 1) (sourceB1125 + difference 1 0) sourceC1125) = raw19003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19003; decide +kernel
    rw [ha]
    exact (canonical19003 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1125 + difference 0 2) (sourceB1125 + difference 2 0) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5497) := by
    have ha : (tripleCharges (sourceA1125 + difference 0 2) (sourceB1125 + difference 2 0) sourceC1125) = raw19004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19004; decide +kernel
    rw [ha]
    exact (canonical19004 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1125 + difference 0 3) (sourceB1125 + difference 3 0) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA1125 + difference 0 3) (sourceB1125 + difference 3 0) sourceC1125) = raw19005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19005; decide +kernel
    rw [ha]
    exact (canonical19005 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1125 + difference 0 4) (sourceB1125 + difference 4 0) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5499) := by
    have ha : (tripleCharges (sourceA1125 + difference 0 4) (sourceB1125 + difference 4 0) sourceC1125) = raw19006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19006; decide +kernel
    rw [ha]
    exact (canonical19006 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1125 + difference 0 5) (sourceB1125 + difference 5 0) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1125 + difference 0 5) (sourceB1125 + difference 5 0) sourceC1125) = raw19007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19007; decide +kernel
    rw [ha]
    exact (canonical19007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1125 + difference 1 0) (sourceB1125 + difference 0 1) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1125 + difference 1 0) (sourceB1125 + difference 0 1) sourceC1125) = raw10104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw10104; decide +kernel
    rw [ha]
    exact (canonical10104 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1125 + difference 1 2) (sourceB1125 + difference 2 1) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1125 + difference 1 2) (sourceB1125 + difference 2 1) sourceC1125) = raw19008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19008; decide +kernel
    rw [ha]
    exact (canonical19008 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1125 + difference 1 3) (sourceB1125 + difference 3 1) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1125 + difference 1 3) (sourceB1125 + difference 3 1) sourceC1125) = raw10089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw10089; decide +kernel
    rw [ha]
    exact (canonical10089 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1125 + difference 1 4) (sourceB1125 + difference 4 1) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1125 + difference 1 4) (sourceB1125 + difference 4 1) sourceC1125) = raw19009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19009; decide +kernel
    rw [ha]
    exact (canonical19009 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1125 + difference 1 5) (sourceB1125 + difference 5 1) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1125 + difference 1 5) (sourceB1125 + difference 5 1) sourceC1125) = raw19010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19010; decide +kernel
    rw [ha]
    exact (canonical19010 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1125 + difference 2 0) (sourceB1125 + difference 0 2) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA1125 + difference 2 0) (sourceB1125 + difference 0 2) sourceC1125) = raw19011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19011; decide +kernel
    rw [ha]
    exact (canonical19011 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1125 + difference 2 1) (sourceB1125 + difference 1 2) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5464) := by
    have ha : (tripleCharges (sourceA1125 + difference 2 1) (sourceB1125 + difference 1 2) sourceC1125) = raw19012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19012; decide +kernel
    rw [ha]
    exact (canonical19012 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1125 + difference 2 3) (sourceB1125 + difference 3 2) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1125 + difference 2 3) (sourceB1125 + difference 3 2) sourceC1125) = raw19013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19013; decide +kernel
    rw [ha]
    exact (canonical19013 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1125 + difference 2 4) (sourceB1125 + difference 4 2) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1125 + difference 2 4) (sourceB1125 + difference 4 2) sourceC1125) = raw19014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19014; decide +kernel
    rw [ha]
    exact (canonical19014 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1125 + difference 2 5) (sourceB1125 + difference 5 2) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1125 + difference 2 5) (sourceB1125 + difference 5 2) sourceC1125) = raw19015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19015; decide +kernel
    rw [ha]
    exact (canonical19015 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1125 + difference 3 0) (sourceB1125 + difference 0 3) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1125 + difference 3 0) (sourceB1125 + difference 0 3) sourceC1125) = raw19016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19016; decide +kernel
    rw [ha]
    exact (canonical19016 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1125 + difference 3 1) (sourceB1125 + difference 1 3) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA1125 + difference 3 1) (sourceB1125 + difference 1 3) sourceC1125) = raw19017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19017; decide +kernel
    rw [ha]
    exact (canonical19017 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1125 + difference 3 2) (sourceB1125 + difference 2 3) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1125 + difference 3 2) (sourceB1125 + difference 2 3) sourceC1125) = raw19018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19018; decide +kernel
    rw [ha]
    exact (canonical19018 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1125 + difference 3 4) (sourceB1125 + difference 4 3) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1125 + difference 3 4) (sourceB1125 + difference 4 3) sourceC1125) = raw19019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19019; decide +kernel
    rw [ha]
    exact (canonical19019 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1125 + difference 3 5) (sourceB1125 + difference 5 3) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1125 + difference 3 5) (sourceB1125 + difference 5 3) sourceC1125) = raw19020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19020; decide +kernel
    rw [ha]
    exact (canonical19020 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1125 + difference 4 0) (sourceB1125 + difference 0 4) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1125 + difference 4 0) (sourceB1125 + difference 0 4) sourceC1125) = raw19021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19021; decide +kernel
    rw [ha]
    exact (canonical19021 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1125 + difference 4 1) (sourceB1125 + difference 1 4) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA1125 + difference 4 1) (sourceB1125 + difference 1 4) sourceC1125) = raw19022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19022; decide +kernel
    rw [ha]
    exact (canonical19022 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1125 + difference 4 2) (sourceB1125 + difference 2 4) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA1125 + difference 4 2) (sourceB1125 + difference 2 4) sourceC1125) = raw19023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19023; decide +kernel
    rw [ha]
    exact (canonical19023 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1125 + difference 4 3) (sourceB1125 + difference 3 4) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1125 + difference 4 3) (sourceB1125 + difference 3 4) sourceC1125) = raw19024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19024; decide +kernel
    rw [ha]
    exact (canonical19024 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1125 + difference 4 5) (sourceB1125 + difference 5 4) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1125 + difference 4 5) (sourceB1125 + difference 5 4) sourceC1125) = raw19025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19025; decide +kernel
    rw [ha]
    exact (canonical19025 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1125 + difference 5 0) (sourceB1125 + difference 0 5) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1125 + difference 5 0) (sourceB1125 + difference 0 5) sourceC1125) = raw10101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw10101; decide +kernel
    rw [ha]
    exact (canonical10101 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1125 + difference 5 1) (sourceB1125 + difference 1 5) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA1125 + difference 5 1) (sourceB1125 + difference 1 5) sourceC1125) = raw19026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19026; decide +kernel
    rw [ha]
    exact (canonical19026 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1125 + difference 5 2) (sourceB1125 + difference 2 5) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1125 + difference 5 2) (sourceB1125 + difference 2 5) sourceC1125) = raw19027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19027; decide +kernel
    rw [ha]
    exact (canonical19027 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1125 + difference 5 3) (sourceB1125 + difference 3 5) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1125 + difference 5 3) (sourceB1125 + difference 3 5) sourceC1125) = raw10085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw10085; decide +kernel
    rw [ha]
    exact (canonical10085 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1125 + difference 5 4) (sourceB1125 + difference 4 5) sourceC1125) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1125 + difference 5 4) (sourceB1125 + difference 4 5) sourceC1125) = raw19028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1125 sourceB1125 sourceC1125 difference raw19028; decide +kernel
    rw [ha]
    exact (canonical19028 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1125 sourceB1125 sourceC1125
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1125, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1126 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1126 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC1126 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceForm1126 : Integer.Sparse Master := [(Sum.inr 5055, 1), (Sum.inr 5056, 2), (Sum.inr 5059, 2), (Sum.inr 5098, 2), (Sum.inr 5271, 2), (Sum.inr 5344, 1), (Sum.inr 5346, 2), (Sum.inr 5365, 2), (Sum.inr 5424, 2), (Sum.inr 5467, 1), (Sum.inr 5473, 2), (Sum.inr 5477, 2), (Sum.inr 5478, 1), (Sum.inr 5482, 2), (Sum.inr 5485, 2), (Sum.inr 5490, 2), (Sum.inr 5492, 1), (Sum.inr 5500, 1)]

theorem sourceEq1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1126 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1126 + difference 0 1) (sourceB1126 + difference 1 0) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1126 + difference 0 1) (sourceB1126 + difference 1 0) sourceC1126) = raw19029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19029; decide +kernel
    rw [ha]
    exact (canonical19029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1126 + difference 0 2) (sourceB1126 + difference 2 0) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1126 + difference 0 2) (sourceB1126 + difference 2 0) sourceC1126) = raw19030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19030; decide +kernel
    rw [ha]
    exact (canonical19030 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1126 + difference 0 3) (sourceB1126 + difference 3 0) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5500) := by
    have ha : (tripleCharges (sourceA1126 + difference 0 3) (sourceB1126 + difference 3 0) sourceC1126) = raw19031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19031; decide +kernel
    rw [ha]
    exact (canonical19031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1126 + difference 0 4) (sourceB1126 + difference 4 0) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1126 + difference 0 4) (sourceB1126 + difference 4 0) sourceC1126) = raw19032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19032; decide +kernel
    rw [ha]
    exact (canonical19032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1126 + difference 0 5) (sourceB1126 + difference 5 0) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1126 + difference 0 5) (sourceB1126 + difference 5 0) sourceC1126) = raw19033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19033; decide +kernel
    rw [ha]
    exact (canonical19033 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1126 + difference 1 0) (sourceB1126 + difference 0 1) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1126 + difference 1 0) (sourceB1126 + difference 0 1) sourceC1126) = raw19034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19034; decide +kernel
    rw [ha]
    exact (canonical19034 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1126 + difference 1 2) (sourceB1126 + difference 2 1) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1126 + difference 1 2) (sourceB1126 + difference 2 1) sourceC1126) = raw14134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw14134; decide +kernel
    rw [ha]
    exact (canonical14134 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1126 + difference 1 3) (sourceB1126 + difference 3 1) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1126 + difference 1 3) (sourceB1126 + difference 3 1) sourceC1126) = raw14135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw14135; decide +kernel
    rw [ha]
    exact (canonical14135 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1126 + difference 1 4) (sourceB1126 + difference 4 1) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1126 + difference 1 4) (sourceB1126 + difference 4 1) sourceC1126) = raw14136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw14136; decide +kernel
    rw [ha]
    exact (canonical14136 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1126 + difference 1 5) (sourceB1126 + difference 5 1) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1126 + difference 1 5) (sourceB1126 + difference 5 1) sourceC1126) = raw14137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw14137; decide +kernel
    rw [ha]
    exact (canonical14137 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1126 + difference 2 0) (sourceB1126 + difference 0 2) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA1126 + difference 2 0) (sourceB1126 + difference 0 2) sourceC1126) = raw14144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw14144; decide +kernel
    rw [ha]
    exact (canonical14144 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1126 + difference 2 1) (sourceB1126 + difference 1 2) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1126 + difference 2 1) (sourceB1126 + difference 1 2) sourceC1126) = raw19035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19035; decide +kernel
    rw [ha]
    exact (canonical19035 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1126 + difference 2 3) (sourceB1126 + difference 3 2) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1126 + difference 2 3) (sourceB1126 + difference 3 2) sourceC1126) = raw19036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19036; decide +kernel
    rw [ha]
    exact (canonical19036 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1126 + difference 2 4) (sourceB1126 + difference 4 2) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1126 + difference 2 4) (sourceB1126 + difference 4 2) sourceC1126) = raw19037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19037; decide +kernel
    rw [ha]
    exact (canonical19037 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1126 + difference 2 5) (sourceB1126 + difference 5 2) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1126 + difference 2 5) (sourceB1126 + difference 5 2) sourceC1126) = raw19038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19038; decide +kernel
    rw [ha]
    exact (canonical19038 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1126 + difference 3 0) (sourceB1126 + difference 0 3) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA1126 + difference 3 0) (sourceB1126 + difference 0 3) sourceC1126) = raw14149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw14149; decide +kernel
    rw [ha]
    exact (canonical14149 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1126 + difference 3 1) (sourceB1126 + difference 1 3) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA1126 + difference 3 1) (sourceB1126 + difference 1 3) sourceC1126) = raw19039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19039; decide +kernel
    rw [ha]
    exact (canonical19039 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1126 + difference 3 2) (sourceB1126 + difference 2 3) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA1126 + difference 3 2) (sourceB1126 + difference 2 3) sourceC1126) = raw19040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19040; decide +kernel
    rw [ha]
    exact (canonical19040 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1126 + difference 3 4) (sourceB1126 + difference 4 3) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1126 + difference 3 4) (sourceB1126 + difference 4 3) sourceC1126) = raw19041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19041; decide +kernel
    rw [ha]
    exact (canonical19041 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1126 + difference 3 5) (sourceB1126 + difference 5 3) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA1126 + difference 3 5) (sourceB1126 + difference 5 3) sourceC1126) = raw19042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19042; decide +kernel
    rw [ha]
    exact (canonical19042 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1126 + difference 4 0) (sourceB1126 + difference 0 4) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA1126 + difference 4 0) (sourceB1126 + difference 0 4) sourceC1126) = raw14154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw14154; decide +kernel
    rw [ha]
    exact (canonical14154 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1126 + difference 4 1) (sourceB1126 + difference 1 4) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA1126 + difference 4 1) (sourceB1126 + difference 1 4) sourceC1126) = raw19043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19043; decide +kernel
    rw [ha]
    exact (canonical19043 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1126 + difference 4 2) (sourceB1126 + difference 2 4) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1126 + difference 4 2) (sourceB1126 + difference 2 4) sourceC1126) = raw19044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19044; decide +kernel
    rw [ha]
    exact (canonical19044 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1126 + difference 4 3) (sourceB1126 + difference 3 4) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1126 + difference 4 3) (sourceB1126 + difference 3 4) sourceC1126) = raw19045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19045; decide +kernel
    rw [ha]
    exact (canonical19045 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1126 + difference 4 5) (sourceB1126 + difference 5 4) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1126 + difference 4 5) (sourceB1126 + difference 5 4) sourceC1126) = raw19046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19046; decide +kernel
    rw [ha]
    exact (canonical19046 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1126 + difference 5 0) (sourceB1126 + difference 0 5) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA1126 + difference 5 0) (sourceB1126 + difference 0 5) sourceC1126) = raw14159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw14159; decide +kernel
    rw [ha]
    exact (canonical14159 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1126 + difference 5 1) (sourceB1126 + difference 1 5) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1126 + difference 5 1) (sourceB1126 + difference 1 5) sourceC1126) = raw19047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19047; decide +kernel
    rw [ha]
    exact (canonical19047 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1126 + difference 5 2) (sourceB1126 + difference 2 5) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5467) := by
    have ha : (tripleCharges (sourceA1126 + difference 5 2) (sourceB1126 + difference 2 5) sourceC1126) = raw19048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19048; decide +kernel
    rw [ha]
    exact (canonical19048 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1126 + difference 5 3) (sourceB1126 + difference 3 5) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1126 + difference 5 3) (sourceB1126 + difference 3 5) sourceC1126) = raw19049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19049; decide +kernel
    rw [ha]
    exact (canonical19049 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1126 + difference 5 4) (sourceB1126 + difference 4 5) sourceC1126) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1126 + difference 5 4) (sourceB1126 + difference 4 5) sourceC1126) = raw19050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1126 sourceB1126 sourceC1126 difference raw19050; decide +kernel
    rw [ha]
    exact (canonical19050 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1126 sourceB1126 sourceC1126
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1126, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1127 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB1127 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1127 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceForm1127 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 5396, 3), (Sum.inr 5422, 3), (Sum.inr 5427, 1), (Sum.inr 5433, 3), (Sum.inr 5437, 1), (Sum.inr 5447, 2), (Sum.inr 5469, 3), (Sum.inr 5474, 1), (Sum.inr 5478, 6), (Sum.inr 5482, 3), (Sum.inr 5486, 3)]

theorem sourceEq1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1127 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 1) (sourceB1127 + difference 1 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 1) (sourceB1127 + difference 1 0) sourceC1127) = raw19051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19051; decide +kernel
    rw [ha]
    exact (canonical19051 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 2) (sourceB1127 + difference 2 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 2) (sourceB1127 + difference 2 0) sourceC1127) = raw19052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19052; decide +kernel
    rw [ha]
    exact (canonical19052 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 3) (sourceB1127 + difference 3 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 3) (sourceB1127 + difference 3 0) sourceC1127) = raw19053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19053; decide +kernel
    rw [ha]
    exact (canonical19053 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 4) (sourceB1127 + difference 4 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 4) (sourceB1127 + difference 4 0) sourceC1127) = raw19054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19054; decide +kernel
    rw [ha]
    exact (canonical19054 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1127 + difference 0 5) (sourceB1127 + difference 5 0) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1127 + difference 0 5) (sourceB1127 + difference 5 0) sourceC1127) = raw19055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19055; decide +kernel
    rw [ha]
    exact (canonical19055 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 0) (sourceB1127 + difference 0 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 0) (sourceB1127 + difference 0 1) sourceC1127) = raw19056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19056; decide +kernel
    rw [ha]
    exact (canonical19056 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 2) (sourceB1127 + difference 2 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 2) (sourceB1127 + difference 2 1) sourceC1127) = raw19057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19057; decide +kernel
    rw [ha]
    exact (canonical19057 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 3) (sourceB1127 + difference 3 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 3) (sourceB1127 + difference 3 1) sourceC1127) = raw19058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19058; decide +kernel
    rw [ha]
    exact (canonical19058 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 4) (sourceB1127 + difference 4 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 4) (sourceB1127 + difference 4 1) sourceC1127) = raw19059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19059; decide +kernel
    rw [ha]
    exact (canonical19059 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1127 + difference 1 5) (sourceB1127 + difference 5 1) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1127 + difference 1 5) (sourceB1127 + difference 5 1) sourceC1127) = raw19060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19060; decide +kernel
    rw [ha]
    exact (canonical19060 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 0) (sourceB1127 + difference 0 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 0) (sourceB1127 + difference 0 2) sourceC1127) = raw19061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19061; decide +kernel
    rw [ha]
    exact (canonical19061 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 1) (sourceB1127 + difference 1 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 1) (sourceB1127 + difference 1 2) sourceC1127) = raw19062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19062; decide +kernel
    rw [ha]
    exact (canonical19062 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 3) (sourceB1127 + difference 3 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 3) (sourceB1127 + difference 3 2) sourceC1127) = raw19063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19063; decide +kernel
    rw [ha]
    exact (canonical19063 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 4) (sourceB1127 + difference 4 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 4) (sourceB1127 + difference 4 2) sourceC1127) = raw19064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19064; decide +kernel
    rw [ha]
    exact (canonical19064 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1127 + difference 2 5) (sourceB1127 + difference 5 2) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1127 + difference 2 5) (sourceB1127 + difference 5 2) sourceC1127) = raw18890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw18890; decide +kernel
    rw [ha]
    exact (canonical18890 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 0) (sourceB1127 + difference 0 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 0) (sourceB1127 + difference 0 3) sourceC1127) = raw19065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19065; decide +kernel
    rw [ha]
    exact (canonical19065 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 1) (sourceB1127 + difference 1 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 1) (sourceB1127 + difference 1 3) sourceC1127) = raw19066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19066; decide +kernel
    rw [ha]
    exact (canonical19066 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 2) (sourceB1127 + difference 2 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 2) (sourceB1127 + difference 2 3) sourceC1127) = raw19067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19067; decide +kernel
    rw [ha]
    exact (canonical19067 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 4) (sourceB1127 + difference 4 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 4) (sourceB1127 + difference 4 3) sourceC1127) = raw19068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19068; decide +kernel
    rw [ha]
    exact (canonical19068 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1127 + difference 3 5) (sourceB1127 + difference 5 3) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 3 5) (sourceB1127 + difference 5 3) sourceC1127) = raw19069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19069; decide +kernel
    rw [ha]
    exact (canonical19069 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 0) (sourceB1127 + difference 0 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 0) (sourceB1127 + difference 0 4) sourceC1127) = raw19070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19070; decide +kernel
    rw [ha]
    exact (canonical19070 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 1) (sourceB1127 + difference 1 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 1) (sourceB1127 + difference 1 4) sourceC1127) = raw19071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19071; decide +kernel
    rw [ha]
    exact (canonical19071 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 2) (sourceB1127 + difference 2 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 2) (sourceB1127 + difference 2 4) sourceC1127) = raw19072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19072; decide +kernel
    rw [ha]
    exact (canonical19072 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 3) (sourceB1127 + difference 3 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 3) (sourceB1127 + difference 3 4) sourceC1127) = raw19073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19073; decide +kernel
    rw [ha]
    exact (canonical19073 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1127 + difference 4 5) (sourceB1127 + difference 5 4) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 4 5) (sourceB1127 + difference 5 4) sourceC1127) = raw19074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19074; decide +kernel
    rw [ha]
    exact (canonical19074 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 0) (sourceB1127 + difference 0 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 0) (sourceB1127 + difference 0 5) sourceC1127) = raw19075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19075; decide +kernel
    rw [ha]
    exact (canonical19075 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 1) (sourceB1127 + difference 1 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 1) (sourceB1127 + difference 1 5) sourceC1127) = raw19076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19076; decide +kernel
    rw [ha]
    exact (canonical19076 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 2) (sourceB1127 + difference 2 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 2) (sourceB1127 + difference 2 5) sourceC1127) = raw19077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19077; decide +kernel
    rw [ha]
    exact (canonical19077 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 3) (sourceB1127 + difference 3 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 3) (sourceB1127 + difference 3 5) sourceC1127) = raw19078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19078; decide +kernel
    rw [ha]
    exact (canonical19078 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1127 + difference 5 4) (sourceB1127 + difference 4 5) sourceC1127) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1127 + difference 5 4) (sourceB1127 + difference 4 5) sourceC1127) = raw19079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1127 sourceB1127 sourceC1127 difference raw19079; decide +kernel
    rw [ha]
    exact (canonical19079 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1127 sourceB1127 sourceC1127
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1127, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1128 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1128 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC1128 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceForm1128 : Integer.Sparse Master := [(Sum.inr 5184, 1), (Sum.inr 5185, 2), (Sum.inr 5202, 1), (Sum.inr 5265, 1), (Sum.inr 5352, 2), (Sum.inr 5354, 1), (Sum.inr 5366, 1), (Sum.inr 5408, 1), (Sum.inr 5414, 1), (Sum.inr 5429, 3), (Sum.inr 5431, 2), (Sum.inr 5450, 1), (Sum.inr 5470, 2), (Sum.inr 5471, 2), (Sum.inr 5472, 2), (Sum.inr 5473, 2), (Sum.inr 5474, 1), (Sum.inr 5481, 1), (Sum.inr 5482, 2), (Sum.inr 5486, 1)]

theorem sourceEq1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1128 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1128 + difference 0 1) (sourceB1128 + difference 1 0) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1128 + difference 0 1) (sourceB1128 + difference 1 0) sourceC1128) = raw19080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19080; decide +kernel
    rw [ha]
    exact (canonical19080 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1128 + difference 0 2) (sourceB1128 + difference 2 0) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1128 + difference 0 2) (sourceB1128 + difference 2 0) sourceC1128) = raw19081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19081; decide +kernel
    rw [ha]
    exact (canonical19081 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1128 + difference 0 3) (sourceB1128 + difference 3 0) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1128 + difference 0 3) (sourceB1128 + difference 3 0) sourceC1128) = raw19082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19082; decide +kernel
    rw [ha]
    exact (canonical19082 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1128 + difference 0 4) (sourceB1128 + difference 4 0) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1128 + difference 0 4) (sourceB1128 + difference 4 0) sourceC1128) = raw19083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19083; decide +kernel
    rw [ha]
    exact (canonical19083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1128 + difference 0 5) (sourceB1128 + difference 5 0) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1128 + difference 0 5) (sourceB1128 + difference 5 0) sourceC1128) = raw19084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19084; decide +kernel
    rw [ha]
    exact (canonical19084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1128 + difference 1 0) (sourceB1128 + difference 0 1) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA1128 + difference 1 0) (sourceB1128 + difference 0 1) sourceC1128) = raw19085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19085; decide +kernel
    rw [ha]
    exact (canonical19085 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1128 + difference 1 2) (sourceB1128 + difference 2 1) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1128 + difference 1 2) (sourceB1128 + difference 2 1) sourceC1128) = raw19086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19086; decide +kernel
    rw [ha]
    exact (canonical19086 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1128 + difference 1 3) (sourceB1128 + difference 3 1) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1128 + difference 1 3) (sourceB1128 + difference 3 1) sourceC1128) = raw19087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19087; decide +kernel
    rw [ha]
    exact (canonical19087 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1128 + difference 1 4) (sourceB1128 + difference 4 1) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1128 + difference 1 4) (sourceB1128 + difference 4 1) sourceC1128) = raw19088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19088; decide +kernel
    rw [ha]
    exact (canonical19088 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1128 + difference 1 5) (sourceB1128 + difference 5 1) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1128 + difference 1 5) (sourceB1128 + difference 5 1) sourceC1128) = raw19089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19089; decide +kernel
    rw [ha]
    exact (canonical19089 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1128 + difference 2 0) (sourceB1128 + difference 0 2) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA1128 + difference 2 0) (sourceB1128 + difference 0 2) sourceC1128) = raw19090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19090; decide +kernel
    rw [ha]
    exact (canonical19090 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1128 + difference 2 1) (sourceB1128 + difference 1 2) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5366) := by
    have ha : (tripleCharges (sourceA1128 + difference 2 1) (sourceB1128 + difference 1 2) sourceC1128) = raw19091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19091; decide +kernel
    rw [ha]
    exact (canonical19091 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1128 + difference 2 3) (sourceB1128 + difference 3 2) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1128 + difference 2 3) (sourceB1128 + difference 3 2) sourceC1128) = raw19092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19092; decide +kernel
    rw [ha]
    exact (canonical19092 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1128 + difference 2 4) (sourceB1128 + difference 4 2) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1128 + difference 2 4) (sourceB1128 + difference 4 2) sourceC1128) = raw19093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19093; decide +kernel
    rw [ha]
    exact (canonical19093 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1128 + difference 2 5) (sourceB1128 + difference 5 2) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA1128 + difference 2 5) (sourceB1128 + difference 5 2) sourceC1128) = raw19094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19094; decide +kernel
    rw [ha]
    exact (canonical19094 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1128 + difference 3 0) (sourceB1128 + difference 0 3) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1128 + difference 3 0) (sourceB1128 + difference 0 3) sourceC1128) = raw19095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19095; decide +kernel
    rw [ha]
    exact (canonical19095 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1128 + difference 3 1) (sourceB1128 + difference 1 3) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1128 + difference 3 1) (sourceB1128 + difference 1 3) sourceC1128) = raw19096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19096; decide +kernel
    rw [ha]
    exact (canonical19096 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1128 + difference 3 2) (sourceB1128 + difference 2 3) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1128 + difference 3 2) (sourceB1128 + difference 2 3) sourceC1128) = raw19097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19097; decide +kernel
    rw [ha]
    exact (canonical19097 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1128 + difference 3 4) (sourceB1128 + difference 4 3) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1128 + difference 3 4) (sourceB1128 + difference 4 3) sourceC1128) = raw19098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19098; decide +kernel
    rw [ha]
    exact (canonical19098 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1128 + difference 3 5) (sourceB1128 + difference 5 3) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1128 + difference 3 5) (sourceB1128 + difference 5 3) sourceC1128) = raw19099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19099; decide +kernel
    rw [ha]
    exact (canonical19099 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1128 + difference 4 0) (sourceB1128 + difference 0 4) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1128 + difference 4 0) (sourceB1128 + difference 0 4) sourceC1128) = raw19100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19100; decide +kernel
    rw [ha]
    exact (canonical19100 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1128 + difference 4 1) (sourceB1128 + difference 1 4) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1128 + difference 4 1) (sourceB1128 + difference 1 4) sourceC1128) = raw19101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19101; decide +kernel
    rw [ha]
    exact (canonical19101 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1128 + difference 4 2) (sourceB1128 + difference 2 4) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1128 + difference 4 2) (sourceB1128 + difference 2 4) sourceC1128) = raw19102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19102; decide +kernel
    rw [ha]
    exact (canonical19102 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1128 + difference 4 3) (sourceB1128 + difference 3 4) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1128 + difference 4 3) (sourceB1128 + difference 3 4) sourceC1128) = raw19103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19103; decide +kernel
    rw [ha]
    exact (canonical19103 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1128 + difference 4 5) (sourceB1128 + difference 5 4) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1128 + difference 4 5) (sourceB1128 + difference 5 4) sourceC1128) = raw19104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19104; decide +kernel
    rw [ha]
    exact (canonical19104 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1128 + difference 5 0) (sourceB1128 + difference 0 5) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA1128 + difference 5 0) (sourceB1128 + difference 0 5) sourceC1128) = raw19105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19105; decide +kernel
    rw [ha]
    exact (canonical19105 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1128 + difference 5 1) (sourceB1128 + difference 1 5) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA1128 + difference 5 1) (sourceB1128 + difference 1 5) sourceC1128) = raw19106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19106; decide +kernel
    rw [ha]
    exact (canonical19106 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1128 + difference 5 2) (sourceB1128 + difference 2 5) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA1128 + difference 5 2) (sourceB1128 + difference 2 5) sourceC1128) = raw19107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19107; decide +kernel
    rw [ha]
    exact (canonical19107 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1128 + difference 5 3) (sourceB1128 + difference 3 5) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1128 + difference 5 3) (sourceB1128 + difference 3 5) sourceC1128) = raw19108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19108; decide +kernel
    rw [ha]
    exact (canonical19108 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1128 + difference 5 4) (sourceB1128 + difference 4 5) sourceC1128) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1128 + difference 5 4) (sourceB1128 + difference 4 5) sourceC1128) = raw19109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1128 sourceB1128 sourceC1128 difference raw19109; decide +kernel
    rw [ha]
    exact (canonical19109 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1128 sourceB1128 sourceC1128
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1128, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1129 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1129 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC1129 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceForm1129 : Integer.Sparse Master := [(Sum.inr 3524, 1), (Sum.inr 3526, 1), (Sum.inr 3529, 2), (Sum.inr 3617, 1), (Sum.inr 3764, 2), (Sum.inr 3765, 1), (Sum.inr 3769, 1), (Sum.inr 3806, 1), (Sum.inr 3869, 1), (Sum.inr 3874, 2), (Sum.inr 3954, 1), (Sum.inr 3955, 2), (Sum.inr 3956, 2), (Sum.inr 3957, 2), (Sum.inr 3961, 2), (Sum.inr 3962, 1), (Sum.inr 3979, 1), (Sum.inr 3980, 2), (Sum.inr 3985, 1), (Sum.inr 4026, 2), (Sum.inr 4029, 1)]

theorem sourceEq1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1129 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1129 + difference 0 1) (sourceB1129 + difference 1 0) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA1129 + difference 0 1) (sourceB1129 + difference 1 0) sourceC1129) = raw19110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19110; decide +kernel
    rw [ha]
    exact (canonical19110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1129 + difference 0 2) (sourceB1129 + difference 2 0) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA1129 + difference 0 2) (sourceB1129 + difference 2 0) sourceC1129) = raw19111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19111; decide +kernel
    rw [ha]
    exact (canonical19111 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1129 + difference 0 3) (sourceB1129 + difference 3 0) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1129 + difference 0 3) (sourceB1129 + difference 3 0) sourceC1129) = raw19112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19112; decide +kernel
    rw [ha]
    exact (canonical19112 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1129 + difference 0 4) (sourceB1129 + difference 4 0) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA1129 + difference 0 4) (sourceB1129 + difference 4 0) sourceC1129) = raw19113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19113; decide +kernel
    rw [ha]
    exact (canonical19113 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1129 + difference 0 5) (sourceB1129 + difference 5 0) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3985) := by
    have ha : (tripleCharges (sourceA1129 + difference 0 5) (sourceB1129 + difference 5 0) sourceC1129) = raw19114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19114; decide +kernel
    rw [ha]
    exact (canonical19114 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1129 + difference 1 0) (sourceB1129 + difference 0 1) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA1129 + difference 1 0) (sourceB1129 + difference 0 1) sourceC1129) = raw19115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19115; decide +kernel
    rw [ha]
    exact (canonical19115 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1129 + difference 1 2) (sourceB1129 + difference 2 1) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA1129 + difference 1 2) (sourceB1129 + difference 2 1) sourceC1129) = raw19116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19116; decide +kernel
    rw [ha]
    exact (canonical19116 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1129 + difference 1 3) (sourceB1129 + difference 3 1) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA1129 + difference 1 3) (sourceB1129 + difference 3 1) sourceC1129) = raw19117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19117; decide +kernel
    rw [ha]
    exact (canonical19117 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1129 + difference 1 4) (sourceB1129 + difference 4 1) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA1129 + difference 1 4) (sourceB1129 + difference 4 1) sourceC1129) = raw19118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19118; decide +kernel
    rw [ha]
    exact (canonical19118 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1129 + difference 1 5) (sourceB1129 + difference 5 1) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA1129 + difference 1 5) (sourceB1129 + difference 5 1) sourceC1129) = raw19119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19119; decide +kernel
    rw [ha]
    exact (canonical19119 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1129 + difference 2 0) (sourceB1129 + difference 0 2) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3617) := by
    have ha : (tripleCharges (sourceA1129 + difference 2 0) (sourceB1129 + difference 0 2) sourceC1129) = raw19120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19120; decide +kernel
    rw [ha]
    exact (canonical19120 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1129 + difference 2 1) (sourceB1129 + difference 1 2) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3765) := by
    have ha : (tripleCharges (sourceA1129 + difference 2 1) (sourceB1129 + difference 1 2) sourceC1129) = raw19121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19121; decide +kernel
    rw [ha]
    exact (canonical19121 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1129 + difference 2 3) (sourceB1129 + difference 3 2) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA1129 + difference 2 3) (sourceB1129 + difference 3 2) sourceC1129) = raw19122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19122; decide +kernel
    rw [ha]
    exact (canonical19122 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1129 + difference 2 4) (sourceB1129 + difference 4 2) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA1129 + difference 2 4) (sourceB1129 + difference 4 2) sourceC1129) = raw19123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19123; decide +kernel
    rw [ha]
    exact (canonical19123 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1129 + difference 2 5) (sourceB1129 + difference 5 2) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3962) := by
    have ha : (tripleCharges (sourceA1129 + difference 2 5) (sourceB1129 + difference 5 2) sourceC1129) = raw19124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19124; decide +kernel
    rw [ha]
    exact (canonical19124 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1129 + difference 3 0) (sourceB1129 + difference 0 3) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1129 + difference 3 0) (sourceB1129 + difference 0 3) sourceC1129) = raw19125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19125; decide +kernel
    rw [ha]
    exact (canonical19125 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1129 + difference 3 1) (sourceB1129 + difference 1 3) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA1129 + difference 3 1) (sourceB1129 + difference 1 3) sourceC1129) = raw19126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19126; decide +kernel
    rw [ha]
    exact (canonical19126 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1129 + difference 3 2) (sourceB1129 + difference 2 3) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1129 + difference 3 2) (sourceB1129 + difference 2 3) sourceC1129) = raw19127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19127; decide +kernel
    rw [ha]
    exact (canonical19127 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1129 + difference 3 4) (sourceB1129 + difference 4 3) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA1129 + difference 3 4) (sourceB1129 + difference 4 3) sourceC1129) = raw19128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19128; decide +kernel
    rw [ha]
    exact (canonical19128 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1129 + difference 3 5) (sourceB1129 + difference 5 3) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1129 + difference 3 5) (sourceB1129 + difference 5 3) sourceC1129) = raw19129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19129; decide +kernel
    rw [ha]
    exact (canonical19129 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1129 + difference 4 0) (sourceB1129 + difference 0 4) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1129 + difference 4 0) (sourceB1129 + difference 0 4) sourceC1129) = raw19130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19130; decide +kernel
    rw [ha]
    exact (canonical19130 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1129 + difference 4 1) (sourceB1129 + difference 1 4) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA1129 + difference 4 1) (sourceB1129 + difference 1 4) sourceC1129) = raw19131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19131; decide +kernel
    rw [ha]
    exact (canonical19131 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1129 + difference 4 2) (sourceB1129 + difference 2 4) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA1129 + difference 4 2) (sourceB1129 + difference 2 4) sourceC1129) = raw19132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19132; decide +kernel
    rw [ha]
    exact (canonical19132 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1129 + difference 4 3) (sourceB1129 + difference 3 4) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA1129 + difference 4 3) (sourceB1129 + difference 3 4) sourceC1129) = raw19133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19133; decide +kernel
    rw [ha]
    exact (canonical19133 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1129 + difference 4 5) (sourceB1129 + difference 5 4) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1129 + difference 4 5) (sourceB1129 + difference 5 4) sourceC1129) = raw19134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19134; decide +kernel
    rw [ha]
    exact (canonical19134 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1129 + difference 5 0) (sourceB1129 + difference 0 5) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA1129 + difference 5 0) (sourceB1129 + difference 0 5) sourceC1129) = raw19135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19135; decide +kernel
    rw [ha]
    exact (canonical19135 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1129 + difference 5 1) (sourceB1129 + difference 1 5) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA1129 + difference 5 1) (sourceB1129 + difference 1 5) sourceC1129) = raw19136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19136; decide +kernel
    rw [ha]
    exact (canonical19136 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1129 + difference 5 2) (sourceB1129 + difference 2 5) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA1129 + difference 5 2) (sourceB1129 + difference 2 5) sourceC1129) = raw19137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19137; decide +kernel
    rw [ha]
    exact (canonical19137 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1129 + difference 5 3) (sourceB1129 + difference 3 5) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA1129 + difference 5 3) (sourceB1129 + difference 3 5) sourceC1129) = raw19138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19138; decide +kernel
    rw [ha]
    exact (canonical19138 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1129 + difference 5 4) (sourceB1129 + difference 4 5) sourceC1129) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA1129 + difference 5 4) (sourceB1129 + difference 4 5) sourceC1129) = raw19139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1129 sourceB1129 sourceC1129 difference raw19139; decide +kernel
    rw [ha]
    exact (canonical19139 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1129 sourceB1129 sourceC1129
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1129, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1130 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1130 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC1130 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceForm1130 : Integer.Sparse Master := [(Sum.inr 4996, 4), (Sum.inr 4998, 2), (Sum.inr 5013, 2), (Sum.inr 5257, 2), (Sum.inr 5395, 4), (Sum.inr 5428, 2), (Sum.inr 5469, 2), (Sum.inr 5473, 4), (Sum.inr 5482, 2), (Sum.inr 5489, 2), (Sum.inr 5490, 4)]

theorem sourceEq1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1130 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 1) (sourceB1130 + difference 1 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 1) (sourceB1130 + difference 1 0) sourceC1130) = raw19140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19140; decide +kernel
    rw [ha]
    exact (canonical19140 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 2) (sourceB1130 + difference 2 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 2) (sourceB1130 + difference 2 0) sourceC1130) = raw19141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19141; decide +kernel
    rw [ha]
    exact (canonical19141 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 3) (sourceB1130 + difference 3 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 3) (sourceB1130 + difference 3 0) sourceC1130) = raw19142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19142; decide +kernel
    rw [ha]
    exact (canonical19142 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 4) (sourceB1130 + difference 4 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 4) (sourceB1130 + difference 4 0) sourceC1130) = raw19143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19143; decide +kernel
    rw [ha]
    exact (canonical19143 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 5) (sourceB1130 + difference 5 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 5) (sourceB1130 + difference 5 0) sourceC1130) = raw19144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19144; decide +kernel
    rw [ha]
    exact (canonical19144 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 0) (sourceB1130 + difference 0 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 0) (sourceB1130 + difference 0 1) sourceC1130) = raw19145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19145; decide +kernel
    rw [ha]
    exact (canonical19145 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 2) (sourceB1130 + difference 2 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 2) (sourceB1130 + difference 2 1) sourceC1130) = raw19146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19146; decide +kernel
    rw [ha]
    exact (canonical19146 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 3) (sourceB1130 + difference 3 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 3) (sourceB1130 + difference 3 1) sourceC1130) = raw19147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19147; decide +kernel
    rw [ha]
    exact (canonical19147 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 4) (sourceB1130 + difference 4 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 4) (sourceB1130 + difference 4 1) sourceC1130) = raw19148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19148; decide +kernel
    rw [ha]
    exact (canonical19148 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 5) (sourceB1130 + difference 5 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 5) (sourceB1130 + difference 5 1) sourceC1130) = raw19149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19149; decide +kernel
    rw [ha]
    exact (canonical19149 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 0) (sourceB1130 + difference 0 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 0) (sourceB1130 + difference 0 2) sourceC1130) = raw19150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19150; decide +kernel
    rw [ha]
    exact (canonical19150 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 1) (sourceB1130 + difference 1 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 1) (sourceB1130 + difference 1 2) sourceC1130) = raw19151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19151; decide +kernel
    rw [ha]
    exact (canonical19151 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 3) (sourceB1130 + difference 3 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 3) (sourceB1130 + difference 3 2) sourceC1130) = raw19152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19152; decide +kernel
    rw [ha]
    exact (canonical19152 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 4) (sourceB1130 + difference 4 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 4) (sourceB1130 + difference 4 2) sourceC1130) = raw19153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19153; decide +kernel
    rw [ha]
    exact (canonical19153 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 5) (sourceB1130 + difference 5 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 5) (sourceB1130 + difference 5 2) sourceC1130) = raw19154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19154; decide +kernel
    rw [ha]
    exact (canonical19154 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 0) (sourceB1130 + difference 0 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 0) (sourceB1130 + difference 0 3) sourceC1130) = raw19155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19155; decide +kernel
    rw [ha]
    exact (canonical19155 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 1) (sourceB1130 + difference 1 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 1) (sourceB1130 + difference 1 3) sourceC1130) = raw19156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19156; decide +kernel
    rw [ha]
    exact (canonical19156 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 2) (sourceB1130 + difference 2 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 2) (sourceB1130 + difference 2 3) sourceC1130) = raw19157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19157; decide +kernel
    rw [ha]
    exact (canonical19157 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 4) (sourceB1130 + difference 4 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 4) (sourceB1130 + difference 4 3) sourceC1130) = raw19158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19158; decide +kernel
    rw [ha]
    exact (canonical19158 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 5) (sourceB1130 + difference 5 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 5) (sourceB1130 + difference 5 3) sourceC1130) = raw19159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19159; decide +kernel
    rw [ha]
    exact (canonical19159 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 0) (sourceB1130 + difference 0 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 0) (sourceB1130 + difference 0 4) sourceC1130) = raw19160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19160; decide +kernel
    rw [ha]
    exact (canonical19160 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 1) (sourceB1130 + difference 1 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 1) (sourceB1130 + difference 1 4) sourceC1130) = raw19161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19161; decide +kernel
    rw [ha]
    exact (canonical19161 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 2) (sourceB1130 + difference 2 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 2) (sourceB1130 + difference 2 4) sourceC1130) = raw19162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19162; decide +kernel
    rw [ha]
    exact (canonical19162 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 3) (sourceB1130 + difference 3 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 3) (sourceB1130 + difference 3 4) sourceC1130) = raw19163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19163; decide +kernel
    rw [ha]
    exact (canonical19163 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 5) (sourceB1130 + difference 5 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 5) (sourceB1130 + difference 5 4) sourceC1130) = raw19164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19164; decide +kernel
    rw [ha]
    exact (canonical19164 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 0) (sourceB1130 + difference 0 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 0) (sourceB1130 + difference 0 5) sourceC1130) = raw19165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19165; decide +kernel
    rw [ha]
    exact (canonical19165 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 1) (sourceB1130 + difference 1 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 1) (sourceB1130 + difference 1 5) sourceC1130) = raw19166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19166; decide +kernel
    rw [ha]
    exact (canonical19166 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 2) (sourceB1130 + difference 2 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 2) (sourceB1130 + difference 2 5) sourceC1130) = raw19167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19167; decide +kernel
    rw [ha]
    exact (canonical19167 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 3) (sourceB1130 + difference 3 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 3) (sourceB1130 + difference 3 5) sourceC1130) = raw19168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19168; decide +kernel
    rw [ha]
    exact (canonical19168 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 4) (sourceB1130 + difference 4 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 4) (sourceB1130 + difference 4 5) sourceC1130) = raw19169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19169; decide +kernel
    rw [ha]
    exact (canonical19169 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1130 sourceB1130 sourceC1130
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1130, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1131 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1131 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC1131 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceForm1131 : Integer.Sparse Master := [(Sum.inr 4859, 1), (Sum.inr 4860, 2), (Sum.inr 4869, 2), (Sum.inr 5383, 2), (Sum.inr 5384, 4), (Sum.inr 5387, 2), (Sum.inr 5398, 2), (Sum.inr 5403, 2), (Sum.inr 5439, 2), (Sum.inr 5443, 4), (Sum.inr 5448, 2), (Sum.inr 5449, 2), (Sum.inr 5488, 1), (Sum.inr 5491, 2)]

theorem sourceEq1131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1131 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1131 + difference 0 1) (sourceB1131 + difference 1 0) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1131 + difference 0 1) (sourceB1131 + difference 1 0) sourceC1131) = raw19170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19170; decide +kernel
    rw [ha]
    exact (canonical19170 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1131 + difference 0 2) (sourceB1131 + difference 2 0) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5488) := by
    have ha : (tripleCharges (sourceA1131 + difference 0 2) (sourceB1131 + difference 2 0) sourceC1131) = raw19171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19171; decide +kernel
    rw [ha]
    exact (canonical19171 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1131 + difference 0 3) (sourceB1131 + difference 3 0) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1131 + difference 0 3) (sourceB1131 + difference 3 0) sourceC1131) = raw19172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19172; decide +kernel
    rw [ha]
    exact (canonical19172 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1131 + difference 0 4) (sourceB1131 + difference 4 0) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1131 + difference 0 4) (sourceB1131 + difference 4 0) sourceC1131) = raw19173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19173; decide +kernel
    rw [ha]
    exact (canonical19173 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1131 + difference 0 5) (sourceB1131 + difference 5 0) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1131 + difference 0 5) (sourceB1131 + difference 5 0) sourceC1131) = raw19174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19174; decide +kernel
    rw [ha]
    exact (canonical19174 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1131 + difference 1 0) (sourceB1131 + difference 0 1) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA1131 + difference 1 0) (sourceB1131 + difference 0 1) sourceC1131) = raw10788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw10788; decide +kernel
    rw [ha]
    exact (canonical10788 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1131 + difference 1 2) (sourceB1131 + difference 2 1) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1131 + difference 1 2) (sourceB1131 + difference 2 1) sourceC1131) = raw19175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19175; decide +kernel
    rw [ha]
    exact (canonical19175 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1131 + difference 1 3) (sourceB1131 + difference 3 1) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1131 + difference 1 3) (sourceB1131 + difference 3 1) sourceC1131) = raw10773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw10773; decide +kernel
    rw [ha]
    exact (canonical10773 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1131 + difference 1 4) (sourceB1131 + difference 4 1) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1131 + difference 1 4) (sourceB1131 + difference 4 1) sourceC1131) = raw19176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19176; decide +kernel
    rw [ha]
    exact (canonical19176 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1131 + difference 1 5) (sourceB1131 + difference 5 1) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1131 + difference 1 5) (sourceB1131 + difference 5 1) sourceC1131) = raw19177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19177; decide +kernel
    rw [ha]
    exact (canonical19177 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1131 + difference 2 0) (sourceB1131 + difference 0 2) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4859) := by
    have ha : (tripleCharges (sourceA1131 + difference 2 0) (sourceB1131 + difference 0 2) sourceC1131) = raw19178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19178; decide +kernel
    rw [ha]
    exact (canonical19178 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1131 + difference 2 1) (sourceB1131 + difference 1 2) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1131 + difference 2 1) (sourceB1131 + difference 1 2) sourceC1131) = raw19179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19179; decide +kernel
    rw [ha]
    exact (canonical19179 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1131 + difference 2 3) (sourceB1131 + difference 3 2) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1131 + difference 2 3) (sourceB1131 + difference 3 2) sourceC1131) = raw19180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19180; decide +kernel
    rw [ha]
    exact (canonical19180 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1131 + difference 2 4) (sourceB1131 + difference 4 2) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1131 + difference 2 4) (sourceB1131 + difference 4 2) sourceC1131) = raw19181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19181; decide +kernel
    rw [ha]
    exact (canonical19181 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1131 + difference 2 5) (sourceB1131 + difference 5 2) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1131 + difference 2 5) (sourceB1131 + difference 5 2) sourceC1131) = raw19182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19182; decide +kernel
    rw [ha]
    exact (canonical19182 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1131 + difference 3 0) (sourceB1131 + difference 0 3) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA1131 + difference 3 0) (sourceB1131 + difference 0 3) sourceC1131) = raw19183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19183; decide +kernel
    rw [ha]
    exact (canonical19183 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1131 + difference 3 1) (sourceB1131 + difference 1 3) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1131 + difference 3 1) (sourceB1131 + difference 1 3) sourceC1131) = raw19184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19184; decide +kernel
    rw [ha]
    exact (canonical19184 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1131 + difference 3 2) (sourceB1131 + difference 2 3) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5398) := by
    have ha : (tripleCharges (sourceA1131 + difference 3 2) (sourceB1131 + difference 2 3) sourceC1131) = raw19185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19185; decide +kernel
    rw [ha]
    exact (canonical19185 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1131 + difference 3 4) (sourceB1131 + difference 4 3) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA1131 + difference 3 4) (sourceB1131 + difference 4 3) sourceC1131) = raw19186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19186; decide +kernel
    rw [ha]
    exact (canonical19186 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1131 + difference 3 5) (sourceB1131 + difference 5 3) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1131 + difference 3 5) (sourceB1131 + difference 5 3) sourceC1131) = raw19187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19187; decide +kernel
    rw [ha]
    exact (canonical19187 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1131 + difference 4 0) (sourceB1131 + difference 0 4) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA1131 + difference 4 0) (sourceB1131 + difference 0 4) sourceC1131) = raw19188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19188; decide +kernel
    rw [ha]
    exact (canonical19188 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1131 + difference 4 1) (sourceB1131 + difference 1 4) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1131 + difference 4 1) (sourceB1131 + difference 1 4) sourceC1131) = raw19189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19189; decide +kernel
    rw [ha]
    exact (canonical19189 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1131 + difference 4 2) (sourceB1131 + difference 2 4) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5398) := by
    have ha : (tripleCharges (sourceA1131 + difference 4 2) (sourceB1131 + difference 2 4) sourceC1131) = raw19190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19190; decide +kernel
    rw [ha]
    exact (canonical19190 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1131 + difference 4 3) (sourceB1131 + difference 3 4) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA1131 + difference 4 3) (sourceB1131 + difference 3 4) sourceC1131) = raw19191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19191; decide +kernel
    rw [ha]
    exact (canonical19191 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1131 + difference 4 5) (sourceB1131 + difference 5 4) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1131 + difference 4 5) (sourceB1131 + difference 5 4) sourceC1131) = raw19192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19192; decide +kernel
    rw [ha]
    exact (canonical19192 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1131 + difference 5 0) (sourceB1131 + difference 0 5) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA1131 + difference 5 0) (sourceB1131 + difference 0 5) sourceC1131) = raw10785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw10785; decide +kernel
    rw [ha]
    exact (canonical10785 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1131 + difference 5 1) (sourceB1131 + difference 1 5) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1131 + difference 5 1) (sourceB1131 + difference 1 5) sourceC1131) = raw19193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19193; decide +kernel
    rw [ha]
    exact (canonical19193 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1131 + difference 5 2) (sourceB1131 + difference 2 5) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1131 + difference 5 2) (sourceB1131 + difference 2 5) sourceC1131) = raw19194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19194; decide +kernel
    rw [ha]
    exact (canonical19194 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1131 + difference 5 3) (sourceB1131 + difference 3 5) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1131 + difference 5 3) (sourceB1131 + difference 3 5) sourceC1131) = raw10769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw10769; decide +kernel
    rw [ha]
    exact (canonical10769 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1131 + difference 5 4) (sourceB1131 + difference 4 5) sourceC1131) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1131 + difference 5 4) (sourceB1131 + difference 4 5) sourceC1131) = raw19195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1131 sourceB1131 sourceC1131 difference raw19195; decide +kernel
    rw [ha]
    exact (canonical19195 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1131 sourceB1131 sourceC1131
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1131, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1132 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1132 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC1132 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceForm1132 : Integer.Sparse Master := [(Sum.inr 5185, 2), (Sum.inr 5187, 1), (Sum.inr 5197, 1), (Sum.inr 5219, 1), (Sum.inr 5220, 1), (Sum.inr 5226, 2), (Sum.inr 5257, 1), (Sum.inr 5281, 1), (Sum.inr 5401, 2), (Sum.inr 5403, 1), (Sum.inr 5408, 1), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5433, 2), (Sum.inr 5438, 2), (Sum.inr 5440, 1), (Sum.inr 5445, 2), (Sum.inr 5448, 1), (Sum.inr 5478, 2), (Sum.inr 5481, 1), (Sum.inr 5485, 1)]

theorem sourceEq1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1132 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 1) (sourceB1132 + difference 1 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 1) (sourceB1132 + difference 1 0) sourceC1132) = raw19196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19196; decide +kernel
    rw [ha]
    exact (canonical19196 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 2) (sourceB1132 + difference 2 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 2) (sourceB1132 + difference 2 0) sourceC1132) = raw19197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19197; decide +kernel
    rw [ha]
    exact (canonical19197 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 3) (sourceB1132 + difference 3 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 3) (sourceB1132 + difference 3 0) sourceC1132) = raw19198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19198; decide +kernel
    rw [ha]
    exact (canonical19198 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 4) (sourceB1132 + difference 4 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 4) (sourceB1132 + difference 4 0) sourceC1132) = raw19199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19199; decide +kernel
    rw [ha]
    exact (canonical19199 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 5) (sourceB1132 + difference 5 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 5) (sourceB1132 + difference 5 0) sourceC1132) = raw19200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19200; decide +kernel
    rw [ha]
    exact (canonical19200 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 0) (sourceB1132 + difference 0 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 0) (sourceB1132 + difference 0 1) sourceC1132) = raw19201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19201; decide +kernel
    rw [ha]
    exact (canonical19201 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 2) (sourceB1132 + difference 2 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 2) (sourceB1132 + difference 2 1) sourceC1132) = raw13674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13674; decide +kernel
    rw [ha]
    exact (canonical13674 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 3) (sourceB1132 + difference 3 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 3) (sourceB1132 + difference 3 1) sourceC1132) = raw13675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13675; decide +kernel
    rw [ha]
    exact (canonical13675 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 4) (sourceB1132 + difference 4 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 4) (sourceB1132 + difference 4 1) sourceC1132) = raw13676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13676; decide +kernel
    rw [ha]
    exact (canonical13676 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 5) (sourceB1132 + difference 5 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 5) (sourceB1132 + difference 5 1) sourceC1132) = raw13677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13677; decide +kernel
    rw [ha]
    exact (canonical13677 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 0) (sourceB1132 + difference 0 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 0) (sourceB1132 + difference 0 2) sourceC1132) = raw13684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13684; decide +kernel
    rw [ha]
    exact (canonical13684 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 1) (sourceB1132 + difference 1 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 1) (sourceB1132 + difference 1 2) sourceC1132) = raw19202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19202; decide +kernel
    rw [ha]
    exact (canonical19202 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 3) (sourceB1132 + difference 3 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 3) (sourceB1132 + difference 3 2) sourceC1132) = raw19203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19203; decide +kernel
    rw [ha]
    exact (canonical19203 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 4) (sourceB1132 + difference 4 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 4) (sourceB1132 + difference 4 2) sourceC1132) = raw19204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19204; decide +kernel
    rw [ha]
    exact (canonical19204 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 5) (sourceB1132 + difference 5 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 5) (sourceB1132 + difference 5 2) sourceC1132) = raw19205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19205; decide +kernel
    rw [ha]
    exact (canonical19205 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 0) (sourceB1132 + difference 0 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 0) (sourceB1132 + difference 0 3) sourceC1132) = raw13689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13689; decide +kernel
    rw [ha]
    exact (canonical13689 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 1) (sourceB1132 + difference 1 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 1) (sourceB1132 + difference 1 3) sourceC1132) = raw19206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19206; decide +kernel
    rw [ha]
    exact (canonical19206 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 2) (sourceB1132 + difference 2 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 2) (sourceB1132 + difference 2 3) sourceC1132) = raw19207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19207; decide +kernel
    rw [ha]
    exact (canonical19207 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 4) (sourceB1132 + difference 4 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 4) (sourceB1132 + difference 4 3) sourceC1132) = raw19208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19208; decide +kernel
    rw [ha]
    exact (canonical19208 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 5) (sourceB1132 + difference 5 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 5) (sourceB1132 + difference 5 3) sourceC1132) = raw19209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19209; decide +kernel
    rw [ha]
    exact (canonical19209 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 0) (sourceB1132 + difference 0 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 0) (sourceB1132 + difference 0 4) sourceC1132) = raw13694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13694; decide +kernel
    rw [ha]
    exact (canonical13694 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 1) (sourceB1132 + difference 1 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 1) (sourceB1132 + difference 1 4) sourceC1132) = raw19210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19210; decide +kernel
    rw [ha]
    exact (canonical19210 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 2) (sourceB1132 + difference 2 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 2) (sourceB1132 + difference 2 4) sourceC1132) = raw19211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19211; decide +kernel
    rw [ha]
    exact (canonical19211 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 3) (sourceB1132 + difference 3 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 3) (sourceB1132 + difference 3 4) sourceC1132) = raw19212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19212; decide +kernel
    rw [ha]
    exact (canonical19212 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 5) (sourceB1132 + difference 5 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 5) (sourceB1132 + difference 5 4) sourceC1132) = raw19213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19213; decide +kernel
    rw [ha]
    exact (canonical19213 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 0) (sourceB1132 + difference 0 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 0) (sourceB1132 + difference 0 5) sourceC1132) = raw13699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13699; decide +kernel
    rw [ha]
    exact (canonical13699 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 1) (sourceB1132 + difference 1 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 1) (sourceB1132 + difference 1 5) sourceC1132) = raw19214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19214; decide +kernel
    rw [ha]
    exact (canonical19214 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 2) (sourceB1132 + difference 2 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 2) (sourceB1132 + difference 2 5) sourceC1132) = raw19215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19215; decide +kernel
    rw [ha]
    exact (canonical19215 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 3) (sourceB1132 + difference 3 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 3) (sourceB1132 + difference 3 5) sourceC1132) = raw19216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19216; decide +kernel
    rw [ha]
    exact (canonical19216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 4) (sourceB1132 + difference 4 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 4) (sourceB1132 + difference 4 5) sourceC1132) = raw19217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19217; decide +kernel
    rw [ha]
    exact (canonical19217 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1132 sourceB1132 sourceC1132
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1132, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1133 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1133 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC1133 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceForm1133 : Integer.Sparse Master := [(Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2669, 2), (Sum.inr 2750, 1), (Sum.inr 3529, 2), (Sum.inr 3532, 1), (Sum.inr 3537, 1), (Sum.inr 3569, 1), (Sum.inr 3804, 2), (Sum.inr 3806, 1), (Sum.inr 3810, 1), (Sum.inr 3840, 2), (Sum.inr 3848, 2), (Sum.inr 3851, 2), (Sum.inr 3857, 2), (Sum.inr 3859, 1), (Sum.inr 3880, 2), (Sum.inr 3885, 1), (Sum.inr 3979, 1), (Sum.inr 3994, 2), (Sum.inr 3998, 1)]

theorem sourceEq1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1133 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 1) (sourceB1133 + difference 1 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 1) (sourceB1133 + difference 1 0) sourceC1133) = raw19218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19218; decide +kernel
    rw [ha]
    exact (canonical19218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 2) (sourceB1133 + difference 2 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 2) (sourceB1133 + difference 2 0) sourceC1133) = raw19219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19219; decide +kernel
    rw [ha]
    exact (canonical19219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 3) (sourceB1133 + difference 3 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 3) (sourceB1133 + difference 3 0) sourceC1133) = raw19220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19220; decide +kernel
    rw [ha]
    exact (canonical19220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 4) (sourceB1133 + difference 4 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 4) (sourceB1133 + difference 4 0) sourceC1133) = raw19221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19221; decide +kernel
    rw [ha]
    exact (canonical19221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1133 + difference 0 5) (sourceB1133 + difference 5 0) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA1133 + difference 0 5) (sourceB1133 + difference 5 0) sourceC1133) = raw19222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19222; decide +kernel
    rw [ha]
    exact (canonical19222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 0) (sourceB1133 + difference 0 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 0) (sourceB1133 + difference 0 1) sourceC1133) = raw19223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19223; decide +kernel
    rw [ha]
    exact (canonical19223 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 2) (sourceB1133 + difference 2 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 2) (sourceB1133 + difference 2 1) sourceC1133) = raw13734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13734; decide +kernel
    rw [ha]
    exact (canonical13734 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 3) (sourceB1133 + difference 3 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 3) (sourceB1133 + difference 3 1) sourceC1133) = raw13735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13735; decide +kernel
    rw [ha]
    exact (canonical13735 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 4) (sourceB1133 + difference 4 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 4) (sourceB1133 + difference 4 1) sourceC1133) = raw13736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13736; decide +kernel
    rw [ha]
    exact (canonical13736 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1133 + difference 1 5) (sourceB1133 + difference 5 1) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3859) := by
    have ha : (tripleCharges (sourceA1133 + difference 1 5) (sourceB1133 + difference 5 1) sourceC1133) = raw13737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13737; decide +kernel
    rw [ha]
    exact (canonical13737 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 0) (sourceB1133 + difference 0 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 0) (sourceB1133 + difference 0 2) sourceC1133) = raw13744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13744; decide +kernel
    rw [ha]
    exact (canonical13744 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 1) (sourceB1133 + difference 1 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 1) (sourceB1133 + difference 1 2) sourceC1133) = raw19224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19224; decide +kernel
    rw [ha]
    exact (canonical19224 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 3) (sourceB1133 + difference 3 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 3) (sourceB1133 + difference 3 2) sourceC1133) = raw19225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19225; decide +kernel
    rw [ha]
    exact (canonical19225 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 4) (sourceB1133 + difference 4 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 4) (sourceB1133 + difference 4 2) sourceC1133) = raw19226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19226; decide +kernel
    rw [ha]
    exact (canonical19226 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1133 + difference 2 5) (sourceB1133 + difference 5 2) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA1133 + difference 2 5) (sourceB1133 + difference 5 2) sourceC1133) = raw19227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19227; decide +kernel
    rw [ha]
    exact (canonical19227 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 0) (sourceB1133 + difference 0 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 0) (sourceB1133 + difference 0 3) sourceC1133) = raw13749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13749; decide +kernel
    rw [ha]
    exact (canonical13749 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 1) (sourceB1133 + difference 1 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 1) (sourceB1133 + difference 1 3) sourceC1133) = raw19228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19228; decide +kernel
    rw [ha]
    exact (canonical19228 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 2) (sourceB1133 + difference 2 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 2) (sourceB1133 + difference 2 3) sourceC1133) = raw19229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19229; decide +kernel
    rw [ha]
    exact (canonical19229 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 4) (sourceB1133 + difference 4 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 4) (sourceB1133 + difference 4 3) sourceC1133) = raw19230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19230; decide +kernel
    rw [ha]
    exact (canonical19230 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1133 + difference 3 5) (sourceB1133 + difference 5 3) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1133 + difference 3 5) (sourceB1133 + difference 5 3) sourceC1133) = raw19231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19231; decide +kernel
    rw [ha]
    exact (canonical19231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 0) (sourceB1133 + difference 0 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 0) (sourceB1133 + difference 0 4) sourceC1133) = raw13754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13754; decide +kernel
    rw [ha]
    exact (canonical13754 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 1) (sourceB1133 + difference 1 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 1) (sourceB1133 + difference 1 4) sourceC1133) = raw19232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19232; decide +kernel
    rw [ha]
    exact (canonical19232 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 2) (sourceB1133 + difference 2 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 2) (sourceB1133 + difference 2 4) sourceC1133) = raw19233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19233; decide +kernel
    rw [ha]
    exact (canonical19233 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 3) (sourceB1133 + difference 3 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 3) (sourceB1133 + difference 3 4) sourceC1133) = raw19234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19234; decide +kernel
    rw [ha]
    exact (canonical19234 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1133 + difference 4 5) (sourceB1133 + difference 5 4) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1133 + difference 4 5) (sourceB1133 + difference 5 4) sourceC1133) = raw19235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19235; decide +kernel
    rw [ha]
    exact (canonical19235 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 0) (sourceB1133 + difference 0 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 0) (sourceB1133 + difference 0 5) sourceC1133) = raw13759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw13759; decide +kernel
    rw [ha]
    exact (canonical13759 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 1) (sourceB1133 + difference 1 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 1) (sourceB1133 + difference 1 5) sourceC1133) = raw19236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19236; decide +kernel
    rw [ha]
    exact (canonical19236 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 2) (sourceB1133 + difference 2 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3810) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 2) (sourceB1133 + difference 2 5) sourceC1133) = raw19237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19237; decide +kernel
    rw [ha]
    exact (canonical19237 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 3) (sourceB1133 + difference 3 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 3) (sourceB1133 + difference 3 5) sourceC1133) = raw19238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19238; decide +kernel
    rw [ha]
    exact (canonical19238 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1133 + difference 5 4) (sourceB1133 + difference 4 5) sourceC1133) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA1133 + difference 5 4) (sourceB1133 + difference 4 5) sourceC1133) = raw19239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1133 sourceB1133 sourceC1133 difference raw19239; decide +kernel
    rw [ha]
    exact (canonical19239 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1133 sourceB1133 sourceC1133
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1133, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1134 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1134 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1134 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceForm1134 : Integer.Sparse Master := [(Sum.inr 4798, 2), (Sum.inr 4805, 1), (Sum.inr 4826, 1), (Sum.inr 4864, 1), (Sum.inr 5349, 2), (Sum.inr 5354, 1), (Sum.inr 5363, 1), (Sum.inr 5378, 2), (Sum.inr 5380, 1), (Sum.inr 5386, 1), (Sum.inr 5400, 2), (Sum.inr 5417, 1), (Sum.inr 5431, 1), (Sum.inr 5432, 2), (Sum.inr 5433, 1), (Sum.inr 5435, 2), (Sum.inr 5438, 2), (Sum.inr 5450, 2), (Sum.inr 5481, 1), (Sum.inr 5489, 1), (Sum.inr 5490, 2)]

theorem sourceEq1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1134 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 1) (sourceB1134 + difference 1 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 1) (sourceB1134 + difference 1 0) sourceC1134) = raw19240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19240; decide +kernel
    rw [ha]
    exact (canonical19240 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 2) (sourceB1134 + difference 2 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 2) (sourceB1134 + difference 2 0) sourceC1134) = raw19241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19241; decide +kernel
    rw [ha]
    exact (canonical19241 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 3) (sourceB1134 + difference 3 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 3) (sourceB1134 + difference 3 0) sourceC1134) = raw19242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19242; decide +kernel
    rw [ha]
    exact (canonical19242 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 4) (sourceB1134 + difference 4 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 4) (sourceB1134 + difference 4 0) sourceC1134) = raw19243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19243; decide +kernel
    rw [ha]
    exact (canonical19243 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 5) (sourceB1134 + difference 5 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 5) (sourceB1134 + difference 5 0) sourceC1134) = raw19244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19244; decide +kernel
    rw [ha]
    exact (canonical19244 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 0) (sourceB1134 + difference 0 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 0) (sourceB1134 + difference 0 1) sourceC1134) = raw19245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19245; decide +kernel
    rw [ha]
    exact (canonical19245 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 2) (sourceB1134 + difference 2 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 2) (sourceB1134 + difference 2 1) sourceC1134) = raw19246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19246; decide +kernel
    rw [ha]
    exact (canonical19246 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 3) (sourceB1134 + difference 3 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 3) (sourceB1134 + difference 3 1) sourceC1134) = raw19247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19247; decide +kernel
    rw [ha]
    exact (canonical19247 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 4) (sourceB1134 + difference 4 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 4) (sourceB1134 + difference 4 1) sourceC1134) = raw19248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19248; decide +kernel
    rw [ha]
    exact (canonical19248 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 5) (sourceB1134 + difference 5 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 5) (sourceB1134 + difference 5 1) sourceC1134) = raw19249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19249; decide +kernel
    rw [ha]
    exact (canonical19249 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 0) (sourceB1134 + difference 0 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 0) (sourceB1134 + difference 0 2) sourceC1134) = raw19250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19250; decide +kernel
    rw [ha]
    exact (canonical19250 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 1) (sourceB1134 + difference 1 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 1) (sourceB1134 + difference 1 2) sourceC1134) = raw19251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19251; decide +kernel
    rw [ha]
    exact (canonical19251 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 3) (sourceB1134 + difference 3 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 3) (sourceB1134 + difference 3 2) sourceC1134) = raw19252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19252; decide +kernel
    rw [ha]
    exact (canonical19252 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 4) (sourceB1134 + difference 4 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 4) (sourceB1134 + difference 4 2) sourceC1134) = raw19253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19253; decide +kernel
    rw [ha]
    exact (canonical19253 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 5) (sourceB1134 + difference 5 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 5) (sourceB1134 + difference 5 2) sourceC1134) = raw19254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19254; decide +kernel
    rw [ha]
    exact (canonical19254 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 0) (sourceB1134 + difference 0 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 0) (sourceB1134 + difference 0 3) sourceC1134) = raw19255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19255; decide +kernel
    rw [ha]
    exact (canonical19255 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 1) (sourceB1134 + difference 1 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 1) (sourceB1134 + difference 1 3) sourceC1134) = raw19256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19256; decide +kernel
    rw [ha]
    exact (canonical19256 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 2) (sourceB1134 + difference 2 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 2) (sourceB1134 + difference 2 3) sourceC1134) = raw19257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19257; decide +kernel
    rw [ha]
    exact (canonical19257 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 4) (sourceB1134 + difference 4 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 4) (sourceB1134 + difference 4 3) sourceC1134) = raw19258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19258; decide +kernel
    rw [ha]
    exact (canonical19258 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 5) (sourceB1134 + difference 5 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 5) (sourceB1134 + difference 5 3) sourceC1134) = raw19259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19259; decide +kernel
    rw [ha]
    exact (canonical19259 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 0) (sourceB1134 + difference 0 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 0) (sourceB1134 + difference 0 4) sourceC1134) = raw19260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19260; decide +kernel
    rw [ha]
    exact (canonical19260 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 1) (sourceB1134 + difference 1 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 1) (sourceB1134 + difference 1 4) sourceC1134) = raw19261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19261; decide +kernel
    rw [ha]
    exact (canonical19261 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 2) (sourceB1134 + difference 2 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 2) (sourceB1134 + difference 2 4) sourceC1134) = raw19262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19262; decide +kernel
    rw [ha]
    exact (canonical19262 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 3) (sourceB1134 + difference 3 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 3) (sourceB1134 + difference 3 4) sourceC1134) = raw19263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19263; decide +kernel
    rw [ha]
    exact (canonical19263 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 5) (sourceB1134 + difference 5 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 5) (sourceB1134 + difference 5 4) sourceC1134) = raw19264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19264; decide +kernel
    rw [ha]
    exact (canonical19264 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 0) (sourceB1134 + difference 0 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 0) (sourceB1134 + difference 0 5) sourceC1134) = raw19265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19265; decide +kernel
    rw [ha]
    exact (canonical19265 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 1) (sourceB1134 + difference 1 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 1) (sourceB1134 + difference 1 5) sourceC1134) = raw19266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19266; decide +kernel
    rw [ha]
    exact (canonical19266 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 2) (sourceB1134 + difference 2 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 2) (sourceB1134 + difference 2 5) sourceC1134) = raw19267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19267; decide +kernel
    rw [ha]
    exact (canonical19267 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 3) (sourceB1134 + difference 3 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 3) (sourceB1134 + difference 3 5) sourceC1134) = raw19268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19268; decide +kernel
    rw [ha]
    exact (canonical19268 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 4) (sourceB1134 + difference 4 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 4) (sourceB1134 + difference 4 5) sourceC1134) = raw19269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19269; decide +kernel
    rw [ha]
    exact (canonical19269 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1134 sourceB1134 sourceC1134
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1134, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1135 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1135 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1135 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceForm1135 : Integer.Sparse Master := [(Sum.inr 2075, 2), (Sum.inr 2077, 1), (Sum.inr 2105, 1), (Sum.inr 2214, 1), (Sum.inr 3719, 2), (Sum.inr 3721, 1), (Sum.inr 3735, 1), (Sum.inr 3749, 2), (Sum.inr 3751, 1), (Sum.inr 3769, 1), (Sum.inr 3799, 2), (Sum.inr 3850, 2), (Sum.inr 3875, 1), (Sum.inr 3876, 2), (Sum.inr 3887, 2), (Sum.inr 3897, 1), (Sum.inr 3906, 2), (Sum.inr 4008, 1), (Sum.inr 4009, 1), (Sum.inr 4013, 2), (Sum.inr 4033, 1)]

theorem sourceEq1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1135 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1135 + difference 0 1) (sourceB1135 + difference 1 0) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA1135 + difference 0 1) (sourceB1135 + difference 1 0) sourceC1135) = raw19270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19270; decide +kernel
    rw [ha]
    exact (canonical19270 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1135 + difference 0 2) (sourceB1135 + difference 2 0) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4008) := by
    have ha : (tripleCharges (sourceA1135 + difference 0 2) (sourceB1135 + difference 2 0) sourceC1135) = raw19271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19271; decide +kernel
    rw [ha]
    exact (canonical19271 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1135 + difference 0 3) (sourceB1135 + difference 3 0) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1135 + difference 0 3) (sourceB1135 + difference 3 0) sourceC1135) = raw19272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19272; decide +kernel
    rw [ha]
    exact (canonical19272 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1135 + difference 0 4) (sourceB1135 + difference 4 0) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA1135 + difference 0 4) (sourceB1135 + difference 4 0) sourceC1135) = raw19273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19273; decide +kernel
    rw [ha]
    exact (canonical19273 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1135 + difference 0 5) (sourceB1135 + difference 5 0) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4009) := by
    have ha : (tripleCharges (sourceA1135 + difference 0 5) (sourceB1135 + difference 5 0) sourceC1135) = raw19274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19274; decide +kernel
    rw [ha]
    exact (canonical19274 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1135 + difference 1 0) (sourceB1135 + difference 0 1) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1135 + difference 1 0) (sourceB1135 + difference 0 1) sourceC1135) = raw19275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19275; decide +kernel
    rw [ha]
    exact (canonical19275 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1135 + difference 1 2) (sourceB1135 + difference 2 1) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA1135 + difference 1 2) (sourceB1135 + difference 2 1) sourceC1135) = raw19276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19276; decide +kernel
    rw [ha]
    exact (canonical19276 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1135 + difference 1 3) (sourceB1135 + difference 3 1) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA1135 + difference 1 3) (sourceB1135 + difference 3 1) sourceC1135) = raw19277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19277; decide +kernel
    rw [ha]
    exact (canonical19277 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1135 + difference 1 4) (sourceB1135 + difference 4 1) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA1135 + difference 1 4) (sourceB1135 + difference 4 1) sourceC1135) = raw19278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19278; decide +kernel
    rw [ha]
    exact (canonical19278 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1135 + difference 1 5) (sourceB1135 + difference 5 1) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3897) := by
    have ha : (tripleCharges (sourceA1135 + difference 1 5) (sourceB1135 + difference 5 1) sourceC1135) = raw19279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19279; decide +kernel
    rw [ha]
    exact (canonical19279 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1135 + difference 2 0) (sourceB1135 + difference 0 2) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA1135 + difference 2 0) (sourceB1135 + difference 0 2) sourceC1135) = raw19280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19280; decide +kernel
    rw [ha]
    exact (canonical19280 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1135 + difference 2 1) (sourceB1135 + difference 1 2) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3735) := by
    have ha : (tripleCharges (sourceA1135 + difference 2 1) (sourceB1135 + difference 1 2) sourceC1135) = raw19281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19281; decide +kernel
    rw [ha]
    exact (canonical19281 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1135 + difference 2 3) (sourceB1135 + difference 3 2) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA1135 + difference 2 3) (sourceB1135 + difference 3 2) sourceC1135) = raw19282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19282; decide +kernel
    rw [ha]
    exact (canonical19282 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1135 + difference 2 4) (sourceB1135 + difference 4 2) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA1135 + difference 2 4) (sourceB1135 + difference 4 2) sourceC1135) = raw19283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19283; decide +kernel
    rw [ha]
    exact (canonical19283 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1135 + difference 2 5) (sourceB1135 + difference 5 2) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA1135 + difference 2 5) (sourceB1135 + difference 5 2) sourceC1135) = raw19284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19284; decide +kernel
    rw [ha]
    exact (canonical19284 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1135 + difference 3 0) (sourceB1135 + difference 0 3) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA1135 + difference 3 0) (sourceB1135 + difference 0 3) sourceC1135) = raw19285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19285; decide +kernel
    rw [ha]
    exact (canonical19285 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1135 + difference 3 1) (sourceB1135 + difference 1 3) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA1135 + difference 3 1) (sourceB1135 + difference 1 3) sourceC1135) = raw19286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19286; decide +kernel
    rw [ha]
    exact (canonical19286 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1135 + difference 3 2) (sourceB1135 + difference 2 3) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3749) := by
    have ha : (tripleCharges (sourceA1135 + difference 3 2) (sourceB1135 + difference 2 3) sourceC1135) = raw19287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19287; decide +kernel
    rw [ha]
    exact (canonical19287 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1135 + difference 3 4) (sourceB1135 + difference 4 3) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1135 + difference 3 4) (sourceB1135 + difference 4 3) sourceC1135) = raw19288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19288; decide +kernel
    rw [ha]
    exact (canonical19288 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1135 + difference 3 5) (sourceB1135 + difference 5 3) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA1135 + difference 3 5) (sourceB1135 + difference 5 3) sourceC1135) = raw19289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19289; decide +kernel
    rw [ha]
    exact (canonical19289 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1135 + difference 4 0) (sourceB1135 + difference 0 4) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA1135 + difference 4 0) (sourceB1135 + difference 0 4) sourceC1135) = raw19290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19290; decide +kernel
    rw [ha]
    exact (canonical19290 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1135 + difference 4 1) (sourceB1135 + difference 1 4) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA1135 + difference 4 1) (sourceB1135 + difference 1 4) sourceC1135) = raw19291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19291; decide +kernel
    rw [ha]
    exact (canonical19291 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1135 + difference 4 2) (sourceB1135 + difference 2 4) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3749) := by
    have ha : (tripleCharges (sourceA1135 + difference 4 2) (sourceB1135 + difference 2 4) sourceC1135) = raw19292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19292; decide +kernel
    rw [ha]
    exact (canonical19292 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1135 + difference 4 3) (sourceB1135 + difference 3 4) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA1135 + difference 4 3) (sourceB1135 + difference 3 4) sourceC1135) = raw19293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19293; decide +kernel
    rw [ha]
    exact (canonical19293 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1135 + difference 4 5) (sourceB1135 + difference 5 4) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA1135 + difference 4 5) (sourceB1135 + difference 5 4) sourceC1135) = raw19294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19294; decide +kernel
    rw [ha]
    exact (canonical19294 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1135 + difference 5 0) (sourceB1135 + difference 0 5) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA1135 + difference 5 0) (sourceB1135 + difference 0 5) sourceC1135) = raw19295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19295; decide +kernel
    rw [ha]
    exact (canonical19295 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1135 + difference 5 1) (sourceB1135 + difference 1 5) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA1135 + difference 5 1) (sourceB1135 + difference 1 5) sourceC1135) = raw19296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19296; decide +kernel
    rw [ha]
    exact (canonical19296 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1135 + difference 5 2) (sourceB1135 + difference 2 5) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3751) := by
    have ha : (tripleCharges (sourceA1135 + difference 5 2) (sourceB1135 + difference 2 5) sourceC1135) = raw19297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19297; decide +kernel
    rw [ha]
    exact (canonical19297 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1135 + difference 5 3) (sourceB1135 + difference 3 5) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1135 + difference 5 3) (sourceB1135 + difference 3 5) sourceC1135) = raw19298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19298; decide +kernel
    rw [ha]
    exact (canonical19298 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1135 + difference 5 4) (sourceB1135 + difference 4 5) sourceC1135) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1135 + difference 5 4) (sourceB1135 + difference 4 5) sourceC1135) = raw19299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1135 sourceB1135 sourceC1135 difference raw19299; decide +kernel
    rw [ha]
    exact (canonical19299 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1135 sourceB1135 sourceC1135
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1135, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1136 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceB1136 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1136 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceForm1136 : Integer.Sparse Master := [(Sum.inr 5145, 2), (Sum.inr 5150, 1), (Sum.inr 5162, 1), (Sum.inr 5243, 1), (Sum.inr 5244, 1), (Sum.inr 5265, 2), (Sum.inr 5290, 1), (Sum.inr 5379, 2), (Sum.inr 5383, 1), (Sum.inr 5421, 2), (Sum.inr 5424, 2), (Sum.inr 5427, 1), (Sum.inr 5429, 3), (Sum.inr 5431, 2), (Sum.inr 5440, 1), (Sum.inr 5448, 1), (Sum.inr 5450, 2), (Sum.inr 5471, 1), (Sum.inr 5472, 2), (Sum.inr 5482, 1)]

theorem sourceEq1136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1136 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1136 + difference 0 1) (sourceB1136 + difference 1 0) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1136 + difference 0 1) (sourceB1136 + difference 1 0) sourceC1136) = raw19060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19060; decide +kernel
    rw [ha]
    exact (canonical19060 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1136 + difference 0 2) (sourceB1136 + difference 2 0) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1136 + difference 0 2) (sourceB1136 + difference 2 0) sourceC1136) = raw19300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19300; decide +kernel
    rw [ha]
    exact (canonical19300 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1136 + difference 0 3) (sourceB1136 + difference 3 0) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1136 + difference 0 3) (sourceB1136 + difference 3 0) sourceC1136) = raw19301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19301; decide +kernel
    rw [ha]
    exact (canonical19301 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1136 + difference 0 4) (sourceB1136 + difference 4 0) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1136 + difference 0 4) (sourceB1136 + difference 4 0) sourceC1136) = raw19302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19302; decide +kernel
    rw [ha]
    exact (canonical19302 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1136 + difference 0 5) (sourceB1136 + difference 5 0) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1136 + difference 0 5) (sourceB1136 + difference 5 0) sourceC1136) = raw19303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19303; decide +kernel
    rw [ha]
    exact (canonical19303 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1136 + difference 1 0) (sourceB1136 + difference 0 1) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA1136 + difference 1 0) (sourceB1136 + difference 0 1) sourceC1136) = raw19304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19304; decide +kernel
    rw [ha]
    exact (canonical19304 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1136 + difference 1 2) (sourceB1136 + difference 2 1) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA1136 + difference 1 2) (sourceB1136 + difference 2 1) sourceC1136) = raw19305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19305; decide +kernel
    rw [ha]
    exact (canonical19305 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1136 + difference 1 3) (sourceB1136 + difference 3 1) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA1136 + difference 1 3) (sourceB1136 + difference 3 1) sourceC1136) = raw19306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19306; decide +kernel
    rw [ha]
    exact (canonical19306 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1136 + difference 1 4) (sourceB1136 + difference 4 1) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA1136 + difference 1 4) (sourceB1136 + difference 4 1) sourceC1136) = raw19307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19307; decide +kernel
    rw [ha]
    exact (canonical19307 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1136 + difference 1 5) (sourceB1136 + difference 5 1) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA1136 + difference 1 5) (sourceB1136 + difference 5 1) sourceC1136) = raw19308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19308; decide +kernel
    rw [ha]
    exact (canonical19308 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1136 + difference 2 0) (sourceB1136 + difference 0 2) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1136 + difference 2 0) (sourceB1136 + difference 0 2) sourceC1136) = raw19309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19309; decide +kernel
    rw [ha]
    exact (canonical19309 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1136 + difference 2 1) (sourceB1136 + difference 1 2) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1136 + difference 2 1) (sourceB1136 + difference 1 2) sourceC1136) = raw19310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19310; decide +kernel
    rw [ha]
    exact (canonical19310 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1136 + difference 2 3) (sourceB1136 + difference 3 2) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1136 + difference 2 3) (sourceB1136 + difference 3 2) sourceC1136) = raw18524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw18524; decide +kernel
    rw [ha]
    exact (canonical18524 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1136 + difference 2 4) (sourceB1136 + difference 4 2) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1136 + difference 2 4) (sourceB1136 + difference 4 2) sourceC1136) = raw18520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw18520; decide +kernel
    rw [ha]
    exact (canonical18520 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1136 + difference 2 5) (sourceB1136 + difference 5 2) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1136 + difference 2 5) (sourceB1136 + difference 5 2) sourceC1136) = raw19311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19311; decide +kernel
    rw [ha]
    exact (canonical19311 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1136 + difference 3 0) (sourceB1136 + difference 0 3) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA1136 + difference 3 0) (sourceB1136 + difference 0 3) sourceC1136) = raw19312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19312; decide +kernel
    rw [ha]
    exact (canonical19312 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1136 + difference 3 1) (sourceB1136 + difference 1 3) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1136 + difference 3 1) (sourceB1136 + difference 1 3) sourceC1136) = raw19313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19313; decide +kernel
    rw [ha]
    exact (canonical19313 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1136 + difference 3 2) (sourceB1136 + difference 2 3) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1136 + difference 3 2) (sourceB1136 + difference 2 3) sourceC1136) = raw19314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19314; decide +kernel
    rw [ha]
    exact (canonical19314 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1136 + difference 3 4) (sourceB1136 + difference 4 3) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1136 + difference 3 4) (sourceB1136 + difference 4 3) sourceC1136) = raw19315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19315; decide +kernel
    rw [ha]
    exact (canonical19315 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1136 + difference 3 5) (sourceB1136 + difference 5 3) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1136 + difference 3 5) (sourceB1136 + difference 5 3) sourceC1136) = raw19316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19316; decide +kernel
    rw [ha]
    exact (canonical19316 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1136 + difference 4 0) (sourceB1136 + difference 0 4) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA1136 + difference 4 0) (sourceB1136 + difference 0 4) sourceC1136) = raw19317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19317; decide +kernel
    rw [ha]
    exact (canonical19317 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1136 + difference 4 1) (sourceB1136 + difference 1 4) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1136 + difference 4 1) (sourceB1136 + difference 1 4) sourceC1136) = raw19318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19318; decide +kernel
    rw [ha]
    exact (canonical19318 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1136 + difference 4 2) (sourceB1136 + difference 2 4) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1136 + difference 4 2) (sourceB1136 + difference 2 4) sourceC1136) = raw19319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19319; decide +kernel
    rw [ha]
    exact (canonical19319 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1136 + difference 4 3) (sourceB1136 + difference 3 4) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1136 + difference 4 3) (sourceB1136 + difference 3 4) sourceC1136) = raw19320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19320; decide +kernel
    rw [ha]
    exact (canonical19320 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1136 + difference 4 5) (sourceB1136 + difference 5 4) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1136 + difference 4 5) (sourceB1136 + difference 5 4) sourceC1136) = raw19321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19321; decide +kernel
    rw [ha]
    exact (canonical19321 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1136 + difference 5 0) (sourceB1136 + difference 0 5) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA1136 + difference 5 0) (sourceB1136 + difference 0 5) sourceC1136) = raw19322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19322; decide +kernel
    rw [ha]
    exact (canonical19322 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1136 + difference 5 1) (sourceB1136 + difference 1 5) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA1136 + difference 5 1) (sourceB1136 + difference 1 5) sourceC1136) = raw19056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19056; decide +kernel
    rw [ha]
    exact (canonical19056 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1136 + difference 5 2) (sourceB1136 + difference 2 5) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1136 + difference 5 2) (sourceB1136 + difference 2 5) sourceC1136) = raw19323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw19323; decide +kernel
    rw [ha]
    exact (canonical19323 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1136 + difference 5 3) (sourceB1136 + difference 3 5) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1136 + difference 5 3) (sourceB1136 + difference 3 5) sourceC1136) = raw18522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw18522; decide +kernel
    rw [ha]
    exact (canonical18522 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1136 + difference 5 4) (sourceB1136 + difference 4 5) sourceC1136) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1136 + difference 5 4) (sourceB1136 + difference 4 5) sourceC1136) = raw18518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1136 sourceB1136 sourceC1136 difference raw18518; decide +kernel
    rw [ha]
    exact (canonical18518 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1136 sourceB1136 sourceC1136
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1136, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1137 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1137 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1137 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm1137 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 5167, 1), (Sum.inr 5169, 2), (Sum.inr 5172, 1), (Sum.inr 5307, 1), (Sum.inr 5386, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 2), (Sum.inr 5416, 2), (Sum.inr 5417, 1), (Sum.inr 5433, 2), (Sum.inr 5434, 2), (Sum.inr 5435, 2), (Sum.inr 5440, 2), (Sum.inr 5442, 2), (Sum.inr 5450, 1), (Sum.inr 5454, 2), (Sum.inr 5489, 1), (Sum.inr 5490, 2), (Sum.inr 5493, 1)]

theorem sourceEq1137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1137 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 1) (sourceB1137 + difference 1 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 1) (sourceB1137 + difference 1 0) sourceC1137) = raw19324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19324; decide +kernel
    rw [ha]
    exact (canonical19324 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 2) (sourceB1137 + difference 2 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 2) (sourceB1137 + difference 2 0) sourceC1137) = raw19325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19325; decide +kernel
    rw [ha]
    exact (canonical19325 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 3) (sourceB1137 + difference 3 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 3) (sourceB1137 + difference 3 0) sourceC1137) = raw15170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15170; decide +kernel
    rw [ha]
    exact (canonical15170 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 4) (sourceB1137 + difference 4 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 4) (sourceB1137 + difference 4 0) sourceC1137) = raw19326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19326; decide +kernel
    rw [ha]
    exact (canonical19326 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1137 + difference 0 5) (sourceB1137 + difference 5 0) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1137 + difference 0 5) (sourceB1137 + difference 5 0) sourceC1137) = raw19327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19327; decide +kernel
    rw [ha]
    exact (canonical19327 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 0) (sourceB1137 + difference 0 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 0) (sourceB1137 + difference 0 1) sourceC1137) = raw7979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw7979; decide +kernel
    rw [ha]
    exact (canonical7979 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 2) (sourceB1137 + difference 2 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 2) (sourceB1137 + difference 2 1) sourceC1137) = raw14054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14054; decide +kernel
    rw [ha]
    exact (canonical14054 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 3) (sourceB1137 + difference 3 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 3) (sourceB1137 + difference 3 1) sourceC1137) = raw2685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw2685; decide +kernel
    rw [ha]
    exact (canonical2685 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 4) (sourceB1137 + difference 4 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 4) (sourceB1137 + difference 4 1) sourceC1137) = raw2680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw2680; decide +kernel
    rw [ha]
    exact (canonical2680 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1137 + difference 1 5) (sourceB1137 + difference 5 1) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA1137 + difference 1 5) (sourceB1137 + difference 5 1) sourceC1137) = raw14055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14055; decide +kernel
    rw [ha]
    exact (canonical14055 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 0) (sourceB1137 + difference 0 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 0) (sourceB1137 + difference 0 2) sourceC1137) = raw14061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14061; decide +kernel
    rw [ha]
    exact (canonical14061 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 1) (sourceB1137 + difference 1 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 1) (sourceB1137 + difference 1 2) sourceC1137) = raw19328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19328; decide +kernel
    rw [ha]
    exact (canonical19328 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 3) (sourceB1137 + difference 3 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 3) (sourceB1137 + difference 3 2) sourceC1137) = raw15173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15173; decide +kernel
    rw [ha]
    exact (canonical15173 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 4) (sourceB1137 + difference 4 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 4) (sourceB1137 + difference 4 2) sourceC1137) = raw19329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19329; decide +kernel
    rw [ha]
    exact (canonical19329 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1137 + difference 2 5) (sourceB1137 + difference 5 2) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1137 + difference 2 5) (sourceB1137 + difference 5 2) sourceC1137) = raw19330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19330; decide +kernel
    rw [ha]
    exact (canonical19330 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 0) (sourceB1137 + difference 0 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 0) (sourceB1137 + difference 0 3) sourceC1137) = raw14065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14065; decide +kernel
    rw [ha]
    exact (canonical14065 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 1) (sourceB1137 + difference 1 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 1) (sourceB1137 + difference 1 3) sourceC1137) = raw19331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19331; decide +kernel
    rw [ha]
    exact (canonical19331 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 2) (sourceB1137 + difference 2 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 2) (sourceB1137 + difference 2 3) sourceC1137) = raw19332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19332; decide +kernel
    rw [ha]
    exact (canonical19332 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 4) (sourceB1137 + difference 4 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 4) (sourceB1137 + difference 4 3) sourceC1137) = raw19333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19333; decide +kernel
    rw [ha]
    exact (canonical19333 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1137 + difference 3 5) (sourceB1137 + difference 5 3) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1137 + difference 3 5) (sourceB1137 + difference 5 3) sourceC1137) = raw19334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19334; decide +kernel
    rw [ha]
    exact (canonical19334 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 0) (sourceB1137 + difference 0 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 0) (sourceB1137 + difference 0 4) sourceC1137) = raw14070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw14070; decide +kernel
    rw [ha]
    exact (canonical14070 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 1) (sourceB1137 + difference 1 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 1) (sourceB1137 + difference 1 4) sourceC1137) = raw19335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19335; decide +kernel
    rw [ha]
    exact (canonical19335 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 2) (sourceB1137 + difference 2 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 2) (sourceB1137 + difference 2 4) sourceC1137) = raw19336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19336; decide +kernel
    rw [ha]
    exact (canonical19336 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 3) (sourceB1137 + difference 3 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 3) (sourceB1137 + difference 3 4) sourceC1137) = raw15179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15179; decide +kernel
    rw [ha]
    exact (canonical15179 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1137 + difference 4 5) (sourceB1137 + difference 5 4) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1137 + difference 4 5) (sourceB1137 + difference 5 4) sourceC1137) = raw19337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw19337; decide +kernel
    rw [ha]
    exact (canonical19337 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 0) (sourceB1137 + difference 0 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 0) (sourceB1137 + difference 0 5) sourceC1137) = raw7977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw7977; decide +kernel
    rw [ha]
    exact (canonical7977 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 1) (sourceB1137 + difference 1 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 1) (sourceB1137 + difference 1 5) sourceC1137) = raw15174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15174; decide +kernel
    rw [ha]
    exact (canonical15174 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 2) (sourceB1137 + difference 2 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 2) (sourceB1137 + difference 2 5) sourceC1137) = raw15175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw15175; decide +kernel
    rw [ha]
    exact (canonical15175 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 3) (sourceB1137 + difference 3 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 3) (sourceB1137 + difference 3 5) sourceC1137) = raw2682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw2682; decide +kernel
    rw [ha]
    exact (canonical2682 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1137 + difference 5 4) (sourceB1137 + difference 4 5) sourceC1137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1137 + difference 5 4) (sourceB1137 + difference 4 5) sourceC1137) = raw2677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1137 sourceB1137 sourceC1137 difference raw2677; decide +kernel
    rw [ha]
    exact (canonical2677 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1137 sourceB1137 sourceC1137
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1137, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1138 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1138 : Charge := ![0, 1, -1, 0, 0, 0]
def sourceC1138 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm1138 : Integer.Sparse Master := [(Sum.inr 4091, 1), (Sum.inr 5137, 3), (Sum.inr 5162, 1), (Sum.inr 5273, 1), (Sum.inr 5380, 3), (Sum.inr 5383, 1), (Sum.inr 5396, 3), (Sum.inr 5424, 6), (Sum.inr 5431, 3), (Sum.inr 5440, 3), (Sum.inr 5447, 1), (Sum.inr 5479, 1), (Sum.inr 5482, 3)]

theorem sourceEq1138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1138 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1138 + difference 0 1) (sourceB1138 + difference 1 0) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1138 + difference 0 1) (sourceB1138 + difference 1 0) sourceC1138) = raw19338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19338; decide +kernel
    rw [ha]
    exact (canonical19338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1138 + difference 0 2) (sourceB1138 + difference 2 0) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5479) := by
    have ha : (tripleCharges (sourceA1138 + difference 0 2) (sourceB1138 + difference 2 0) sourceC1138) = raw19339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19339; decide +kernel
    rw [ha]
    exact (canonical19339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1138 + difference 0 3) (sourceB1138 + difference 3 0) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1138 + difference 0 3) (sourceB1138 + difference 3 0) sourceC1138) = raw19340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19340; decide +kernel
    rw [ha]
    exact (canonical19340 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1138 + difference 0 4) (sourceB1138 + difference 4 0) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1138 + difference 0 4) (sourceB1138 + difference 4 0) sourceC1138) = raw19341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19341; decide +kernel
    rw [ha]
    exact (canonical19341 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1138 + difference 0 5) (sourceB1138 + difference 5 0) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1138 + difference 0 5) (sourceB1138 + difference 5 0) sourceC1138) = raw19342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19342; decide +kernel
    rw [ha]
    exact (canonical19342 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1138 + difference 1 0) (sourceB1138 + difference 0 1) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA1138 + difference 1 0) (sourceB1138 + difference 0 1) sourceC1138) = raw19343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19343; decide +kernel
    rw [ha]
    exact (canonical19343 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1138 + difference 1 2) (sourceB1138 + difference 2 1) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1138 + difference 1 2) (sourceB1138 + difference 2 1) sourceC1138) = raw14222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw14222; decide +kernel
    rw [ha]
    exact (canonical14222 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1138 + difference 1 3) (sourceB1138 + difference 3 1) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1138 + difference 1 3) (sourceB1138 + difference 3 1) sourceC1138) = raw14223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw14223; decide +kernel
    rw [ha]
    exact (canonical14223 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1138 + difference 1 4) (sourceB1138 + difference 4 1) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1138 + difference 1 4) (sourceB1138 + difference 4 1) sourceC1138) = raw14224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw14224; decide +kernel
    rw [ha]
    exact (canonical14224 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1138 + difference 1 5) (sourceB1138 + difference 5 1) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1138 + difference 1 5) (sourceB1138 + difference 5 1) sourceC1138) = raw14225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw14225; decide +kernel
    rw [ha]
    exact (canonical14225 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1138 + difference 2 0) (sourceB1138 + difference 0 2) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA1138 + difference 2 0) (sourceB1138 + difference 0 2) sourceC1138) = raw14232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw14232; decide +kernel
    rw [ha]
    exact (canonical14232 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1138 + difference 2 1) (sourceB1138 + difference 1 2) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA1138 + difference 2 1) (sourceB1138 + difference 1 2) sourceC1138) = raw19344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19344; decide +kernel
    rw [ha]
    exact (canonical19344 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1138 + difference 2 3) (sourceB1138 + difference 3 2) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1138 + difference 2 3) (sourceB1138 + difference 3 2) sourceC1138) = raw19345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19345; decide +kernel
    rw [ha]
    exact (canonical19345 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1138 + difference 2 4) (sourceB1138 + difference 4 2) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1138 + difference 2 4) (sourceB1138 + difference 4 2) sourceC1138) = raw19346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19346; decide +kernel
    rw [ha]
    exact (canonical19346 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1138 + difference 2 5) (sourceB1138 + difference 5 2) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1138 + difference 2 5) (sourceB1138 + difference 5 2) sourceC1138) = raw19347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19347; decide +kernel
    rw [ha]
    exact (canonical19347 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1138 + difference 3 0) (sourceB1138 + difference 0 3) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA1138 + difference 3 0) (sourceB1138 + difference 0 3) sourceC1138) = raw14237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw14237; decide +kernel
    rw [ha]
    exact (canonical14237 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1138 + difference 3 1) (sourceB1138 + difference 1 3) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1138 + difference 3 1) (sourceB1138 + difference 1 3) sourceC1138) = raw19348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19348; decide +kernel
    rw [ha]
    exact (canonical19348 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1138 + difference 3 2) (sourceB1138 + difference 2 3) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1138 + difference 3 2) (sourceB1138 + difference 2 3) sourceC1138) = raw19349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19349; decide +kernel
    rw [ha]
    exact (canonical19349 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1138 + difference 3 4) (sourceB1138 + difference 4 3) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1138 + difference 3 4) (sourceB1138 + difference 4 3) sourceC1138) = raw19350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19350; decide +kernel
    rw [ha]
    exact (canonical19350 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1138 + difference 3 5) (sourceB1138 + difference 5 3) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1138 + difference 3 5) (sourceB1138 + difference 5 3) sourceC1138) = raw19351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19351; decide +kernel
    rw [ha]
    exact (canonical19351 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1138 + difference 4 0) (sourceB1138 + difference 0 4) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA1138 + difference 4 0) (sourceB1138 + difference 0 4) sourceC1138) = raw14242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw14242; decide +kernel
    rw [ha]
    exact (canonical14242 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1138 + difference 4 1) (sourceB1138 + difference 1 4) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1138 + difference 4 1) (sourceB1138 + difference 1 4) sourceC1138) = raw19352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19352; decide +kernel
    rw [ha]
    exact (canonical19352 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1138 + difference 4 2) (sourceB1138 + difference 2 4) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1138 + difference 4 2) (sourceB1138 + difference 2 4) sourceC1138) = raw19353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19353; decide +kernel
    rw [ha]
    exact (canonical19353 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1138 + difference 4 3) (sourceB1138 + difference 3 4) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1138 + difference 4 3) (sourceB1138 + difference 3 4) sourceC1138) = raw19354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19354; decide +kernel
    rw [ha]
    exact (canonical19354 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1138 + difference 4 5) (sourceB1138 + difference 5 4) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1138 + difference 4 5) (sourceB1138 + difference 5 4) sourceC1138) = raw19355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19355; decide +kernel
    rw [ha]
    exact (canonical19355 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1138 + difference 5 0) (sourceB1138 + difference 0 5) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA1138 + difference 5 0) (sourceB1138 + difference 0 5) sourceC1138) = raw14247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw14247; decide +kernel
    rw [ha]
    exact (canonical14247 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1138 + difference 5 1) (sourceB1138 + difference 1 5) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1138 + difference 5 1) (sourceB1138 + difference 1 5) sourceC1138) = raw19356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19356; decide +kernel
    rw [ha]
    exact (canonical19356 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1138 + difference 5 2) (sourceB1138 + difference 2 5) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA1138 + difference 5 2) (sourceB1138 + difference 2 5) sourceC1138) = raw19357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19357; decide +kernel
    rw [ha]
    exact (canonical19357 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1138 + difference 5 3) (sourceB1138 + difference 3 5) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1138 + difference 5 3) (sourceB1138 + difference 3 5) sourceC1138) = raw19358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19358; decide +kernel
    rw [ha]
    exact (canonical19358 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1138 + difference 5 4) (sourceB1138 + difference 4 5) sourceC1138) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1138 + difference 5 4) (sourceB1138 + difference 4 5) sourceC1138) = raw19359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1138 sourceB1138 sourceC1138 difference raw19359; decide +kernel
    rw [ha]
    exact (canonical19359 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1138 sourceB1138 sourceC1138
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1138, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1139 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1139 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1139 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm1139 : Integer.Sparse Master := [(Sum.inr 4079, 1), (Sum.inr 4080, 3), (Sum.inr 4083, 1), (Sum.inr 4087, 1), (Sum.inr 4088, 3), (Sum.inr 4090, 3), (Sum.inr 4091, 5), (Sum.inr 4092, 6), (Sum.inr 4093, 3), (Sum.inr 4095, 1), (Sum.inr 4096, 3)]

theorem sourceEq1139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1139 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1139 + difference 0 1) (sourceB1139 + difference 1 0) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1139 + difference 0 1) (sourceB1139 + difference 1 0) sourceC1139) = raw3440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3440; decide +kernel
    rw [ha]
    exact (canonical3440 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1139 + difference 0 2) (sourceB1139 + difference 2 0) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4095) := by
    have ha : (tripleCharges (sourceA1139 + difference 0 2) (sourceB1139 + difference 2 0) sourceC1139) = raw3441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3441; decide +kernel
    rw [ha]
    exact (canonical3441 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1139 + difference 0 3) (sourceB1139 + difference 3 0) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1139 + difference 0 3) (sourceB1139 + difference 3 0) sourceC1139) = raw3319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3319; decide +kernel
    rw [ha]
    exact (canonical3319 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1139 + difference 0 4) (sourceB1139 + difference 4 0) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1139 + difference 0 4) (sourceB1139 + difference 4 0) sourceC1139) = raw3442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3442; decide +kernel
    rw [ha]
    exact (canonical3442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1139 + difference 0 5) (sourceB1139 + difference 5 0) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1139 + difference 0 5) (sourceB1139 + difference 5 0) sourceC1139) = raw3443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3443; decide +kernel
    rw [ha]
    exact (canonical3443 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1139 + difference 1 0) (sourceB1139 + difference 0 1) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1139 + difference 1 0) (sourceB1139 + difference 0 1) sourceC1139) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1139 + difference 1 2) (sourceB1139 + difference 2 1) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1139 + difference 1 2) (sourceB1139 + difference 2 1) sourceC1139) = raw3333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3333; decide +kernel
    rw [ha]
    exact (canonical3333 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1139 + difference 1 3) (sourceB1139 + difference 3 1) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA1139 + difference 1 3) (sourceB1139 + difference 3 1) sourceC1139) = raw2933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw2933; decide +kernel
    rw [ha]
    exact (canonical2933 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1139 + difference 1 4) (sourceB1139 + difference 4 1) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA1139 + difference 1 4) (sourceB1139 + difference 4 1) sourceC1139) = raw2928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw2928; decide +kernel
    rw [ha]
    exact (canonical2928 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1139 + difference 1 5) (sourceB1139 + difference 5 1) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA1139 + difference 1 5) (sourceB1139 + difference 5 1) sourceC1139) = raw3334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3334; decide +kernel
    rw [ha]
    exact (canonical3334 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1139 + difference 2 0) (sourceB1139 + difference 0 2) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA1139 + difference 2 0) (sourceB1139 + difference 0 2) sourceC1139) = raw14365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw14365; decide +kernel
    rw [ha]
    exact (canonical14365 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1139 + difference 2 1) (sourceB1139 + difference 1 2) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (tripleCharges (sourceA1139 + difference 2 1) (sourceB1139 + difference 1 2) sourceC1139) = raw19360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19360; decide +kernel
    rw [ha]
    exact (canonical19360 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1139 + difference 2 3) (sourceB1139 + difference 3 2) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1139 + difference 2 3) (sourceB1139 + difference 3 2) sourceC1139) = raw3328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3328; decide +kernel
    rw [ha]
    exact (canonical3328 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1139 + difference 2 4) (sourceB1139 + difference 4 2) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1139 + difference 2 4) (sourceB1139 + difference 4 2) sourceC1139) = raw19361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19361; decide +kernel
    rw [ha]
    exact (canonical19361 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1139 + difference 2 5) (sourceB1139 + difference 5 2) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1139 + difference 2 5) (sourceB1139 + difference 5 2) sourceC1139) = raw19362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19362; decide +kernel
    rw [ha]
    exact (canonical19362 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1139 + difference 3 0) (sourceB1139 + difference 0 3) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1139 + difference 3 0) (sourceB1139 + difference 0 3) sourceC1139) = raw14369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw14369; decide +kernel
    rw [ha]
    exact (canonical14369 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1139 + difference 3 1) (sourceB1139 + difference 1 3) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA1139 + difference 3 1) (sourceB1139 + difference 1 3) sourceC1139) = raw19363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19363; decide +kernel
    rw [ha]
    exact (canonical19363 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1139 + difference 3 2) (sourceB1139 + difference 2 3) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1139 + difference 3 2) (sourceB1139 + difference 2 3) sourceC1139) = raw19364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19364; decide +kernel
    rw [ha]
    exact (canonical19364 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1139 + difference 3 4) (sourceB1139 + difference 4 3) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1139 + difference 3 4) (sourceB1139 + difference 4 3) sourceC1139) = raw19365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19365; decide +kernel
    rw [ha]
    exact (canonical19365 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1139 + difference 3 5) (sourceB1139 + difference 5 3) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1139 + difference 3 5) (sourceB1139 + difference 5 3) sourceC1139) = raw19366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19366; decide +kernel
    rw [ha]
    exact (canonical19366 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1139 + difference 4 0) (sourceB1139 + difference 0 4) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1139 + difference 4 0) (sourceB1139 + difference 0 4) sourceC1139) = raw14374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw14374; decide +kernel
    rw [ha]
    exact (canonical14374 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1139 + difference 4 1) (sourceB1139 + difference 1 4) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA1139 + difference 4 1) (sourceB1139 + difference 1 4) sourceC1139) = raw19367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19367; decide +kernel
    rw [ha]
    exact (canonical19367 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1139 + difference 4 2) (sourceB1139 + difference 2 4) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1139 + difference 4 2) (sourceB1139 + difference 2 4) sourceC1139) = raw19368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19368; decide +kernel
    rw [ha]
    exact (canonical19368 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1139 + difference 4 3) (sourceB1139 + difference 3 4) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1139 + difference 4 3) (sourceB1139 + difference 3 4) sourceC1139) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1139 + difference 4 5) (sourceB1139 + difference 5 4) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1139 + difference 4 5) (sourceB1139 + difference 5 4) sourceC1139) = raw19369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw19369; decide +kernel
    rw [ha]
    exact (canonical19369 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1139 + difference 5 0) (sourceB1139 + difference 0 5) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1139 + difference 5 0) (sourceB1139 + difference 0 5) sourceC1139) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1139 + difference 5 1) (sourceB1139 + difference 1 5) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA1139 + difference 5 1) (sourceB1139 + difference 1 5) sourceC1139) = raw18337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw18337; decide +kernel
    rw [ha]
    exact (canonical18337 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1139 + difference 5 2) (sourceB1139 + difference 2 5) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1139 + difference 5 2) (sourceB1139 + difference 2 5) sourceC1139) = raw18338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw18338; decide +kernel
    rw [ha]
    exact (canonical18338 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1139 + difference 5 3) (sourceB1139 + difference 3 5) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1139 + difference 5 3) (sourceB1139 + difference 3 5) sourceC1139) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1139 + difference 5 4) (sourceB1139 + difference 4 5) sourceC1139) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA1139 + difference 5 4) (sourceB1139 + difference 4 5) sourceC1139) = raw2925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1139 sourceB1139 sourceC1139 difference raw2925; decide +kernel
    rw [ha]
    exact (canonical2925 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1139 sourceB1139 sourceC1139
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1139, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1140 : Charge := ![-1, -1, -1, 1, 1, 1]
def sourceB1140 : Charge := ![-1, 1, 1, -1, -1, 1]
def sourceC1140 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1140 : Integer.Sparse Master := [(Sum.inr 5398, 4), (Sum.inr 5403, 8), (Sum.inr 5415, 2), (Sum.inr 5439, 8), (Sum.inr 5448, 4), (Sum.inr 5491, 4)]

theorem sourceEq1140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1140 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1140 + difference 0 1) (sourceB1140 + difference 1 0) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1140 + difference 0 1) (sourceB1140 + difference 1 0) sourceC1140) = raw19370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19370; decide +kernel
    rw [ha]
    exact (canonical19370 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1140 + difference 0 2) (sourceB1140 + difference 2 0) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1140 + difference 0 2) (sourceB1140 + difference 2 0) sourceC1140) = raw19371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19371; decide +kernel
    rw [ha]
    exact (canonical19371 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1140 + difference 0 3) (sourceB1140 + difference 3 0) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1140 + difference 0 3) (sourceB1140 + difference 3 0) sourceC1140) = raw19372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19372; decide +kernel
    rw [ha]
    exact (canonical19372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1140 + difference 0 4) (sourceB1140 + difference 4 0) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1140 + difference 0 4) (sourceB1140 + difference 4 0) sourceC1140) = raw19373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19373; decide +kernel
    rw [ha]
    exact (canonical19373 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1140 + difference 0 5) (sourceB1140 + difference 5 0) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1140 + difference 0 5) (sourceB1140 + difference 5 0) sourceC1140) = raw19374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19374; decide +kernel
    rw [ha]
    exact (canonical19374 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1140 + difference 1 0) (sourceB1140 + difference 0 1) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1140 + difference 1 0) (sourceB1140 + difference 0 1) sourceC1140) = raw12081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw12081; decide +kernel
    rw [ha]
    exact (canonical12081 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1140 + difference 1 2) (sourceB1140 + difference 2 1) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1140 + difference 1 2) (sourceB1140 + difference 2 1) sourceC1140) = raw19375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19375; decide +kernel
    rw [ha]
    exact (canonical19375 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1140 + difference 1 3) (sourceB1140 + difference 3 1) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1140 + difference 1 3) (sourceB1140 + difference 3 1) sourceC1140) = raw19376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19376; decide +kernel
    rw [ha]
    exact (canonical19376 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1140 + difference 1 4) (sourceB1140 + difference 4 1) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1140 + difference 1 4) (sourceB1140 + difference 4 1) sourceC1140) = raw19377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19377; decide +kernel
    rw [ha]
    exact (canonical19377 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1140 + difference 1 5) (sourceB1140 + difference 5 1) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1140 + difference 1 5) (sourceB1140 + difference 5 1) sourceC1140) = raw19378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19378; decide +kernel
    rw [ha]
    exact (canonical19378 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1140 + difference 2 0) (sourceB1140 + difference 0 2) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1140 + difference 2 0) (sourceB1140 + difference 0 2) sourceC1140) = raw12080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw12080; decide +kernel
    rw [ha]
    exact (canonical12080 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1140 + difference 2 1) (sourceB1140 + difference 1 2) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1140 + difference 2 1) (sourceB1140 + difference 1 2) sourceC1140) = raw18345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw18345; decide +kernel
    rw [ha]
    exact (canonical18345 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1140 + difference 2 3) (sourceB1140 + difference 3 2) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1140 + difference 2 3) (sourceB1140 + difference 3 2) sourceC1140) = raw18298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw18298; decide +kernel
    rw [ha]
    exact (canonical18298 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1140 + difference 2 4) (sourceB1140 + difference 4 2) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1140 + difference 2 4) (sourceB1140 + difference 4 2) sourceC1140) = raw18347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw18347; decide +kernel
    rw [ha]
    exact (canonical18347 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1140 + difference 2 5) (sourceB1140 + difference 5 2) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1140 + difference 2 5) (sourceB1140 + difference 5 2) sourceC1140) = raw18348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw18348; decide +kernel
    rw [ha]
    exact (canonical18348 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1140 + difference 3 0) (sourceB1140 + difference 0 3) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1140 + difference 3 0) (sourceB1140 + difference 0 3) sourceC1140) = raw18353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw18353; decide +kernel
    rw [ha]
    exact (canonical18353 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1140 + difference 3 1) (sourceB1140 + difference 1 3) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5398) := by
    have ha : (tripleCharges (sourceA1140 + difference 3 1) (sourceB1140 + difference 1 3) sourceC1140) = raw19379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19379; decide +kernel
    rw [ha]
    exact (canonical19379 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1140 + difference 3 2) (sourceB1140 + difference 2 3) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5398) := by
    have ha : (tripleCharges (sourceA1140 + difference 3 2) (sourceB1140 + difference 2 3) sourceC1140) = raw19380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19380; decide +kernel
    rw [ha]
    exact (canonical19380 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1140 + difference 3 4) (sourceB1140 + difference 4 3) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1140 + difference 3 4) (sourceB1140 + difference 4 3) sourceC1140) = raw19381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19381; decide +kernel
    rw [ha]
    exact (canonical19381 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1140 + difference 3 5) (sourceB1140 + difference 5 3) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1140 + difference 3 5) (sourceB1140 + difference 5 3) sourceC1140) = raw19382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19382; decide +kernel
    rw [ha]
    exact (canonical19382 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1140 + difference 4 0) (sourceB1140 + difference 0 4) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1140 + difference 4 0) (sourceB1140 + difference 0 4) sourceC1140) = raw18357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw18357; decide +kernel
    rw [ha]
    exact (canonical18357 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1140 + difference 4 1) (sourceB1140 + difference 1 4) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5398) := by
    have ha : (tripleCharges (sourceA1140 + difference 4 1) (sourceB1140 + difference 1 4) sourceC1140) = raw19383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19383; decide +kernel
    rw [ha]
    exact (canonical19383 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1140 + difference 4 2) (sourceB1140 + difference 2 4) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5398) := by
    have ha : (tripleCharges (sourceA1140 + difference 4 2) (sourceB1140 + difference 2 4) sourceC1140) = raw19384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19384; decide +kernel
    rw [ha]
    exact (canonical19384 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1140 + difference 4 3) (sourceB1140 + difference 3 4) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1140 + difference 4 3) (sourceB1140 + difference 3 4) sourceC1140) = raw19385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19385; decide +kernel
    rw [ha]
    exact (canonical19385 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1140 + difference 4 5) (sourceB1140 + difference 5 4) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1140 + difference 4 5) (sourceB1140 + difference 5 4) sourceC1140) = raw19386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19386; decide +kernel
    rw [ha]
    exact (canonical19386 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1140 + difference 5 0) (sourceB1140 + difference 0 5) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA1140 + difference 5 0) (sourceB1140 + difference 0 5) sourceC1140) = raw18304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw18304; decide +kernel
    rw [ha]
    exact (canonical18304 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1140 + difference 5 1) (sourceB1140 + difference 1 5) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1140 + difference 5 1) (sourceB1140 + difference 1 5) sourceC1140) = raw19387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19387; decide +kernel
    rw [ha]
    exact (canonical19387 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1140 + difference 5 2) (sourceB1140 + difference 2 5) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1140 + difference 5 2) (sourceB1140 + difference 2 5) sourceC1140) = raw19388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19388; decide +kernel
    rw [ha]
    exact (canonical19388 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1140 + difference 5 3) (sourceB1140 + difference 3 5) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1140 + difference 5 3) (sourceB1140 + difference 3 5) sourceC1140) = raw18295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw18295; decide +kernel
    rw [ha]
    exact (canonical18295 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1140 + difference 5 4) (sourceB1140 + difference 4 5) sourceC1140) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1140 + difference 5 4) (sourceB1140 + difference 4 5) sourceC1140) = raw19389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1140 sourceB1140 sourceC1140 difference raw19389; decide +kernel
    rw [ha]
    exact (canonical19389 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1140 sourceB1140 sourceC1140
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1140, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1141 : Charge := ![-1, -1, -1, 1, 1, 1]
def sourceB1141 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1141 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm1141 : Integer.Sparse Master := [(Sum.inr 4090, 9), (Sum.inr 4091, 12), (Sum.inr 4096, 9)]

theorem sourceEq1141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1141 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 1) (sourceB1141 + difference 1 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 1) (sourceB1141 + difference 1 0) sourceC1141) = raw19390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19390; decide +kernel
    rw [ha]
    exact (canonical19390 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 2) (sourceB1141 + difference 2 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 2) (sourceB1141 + difference 2 0) sourceC1141) = raw19391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19391; decide +kernel
    rw [ha]
    exact (canonical19391 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 3) (sourceB1141 + difference 3 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 3) (sourceB1141 + difference 3 0) sourceC1141) = raw3432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3432; decide +kernel
    rw [ha]
    exact (canonical3432 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 4) (sourceB1141 + difference 4 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 4) (sourceB1141 + difference 4 0) sourceC1141) = raw19392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19392; decide +kernel
    rw [ha]
    exact (canonical19392 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1141 + difference 0 5) (sourceB1141 + difference 5 0) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 0 5) (sourceB1141 + difference 5 0) sourceC1141) = raw19393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19393; decide +kernel
    rw [ha]
    exact (canonical19393 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 0) (sourceB1141 + difference 0 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 0) (sourceB1141 + difference 0 1) sourceC1141) = raw3333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3333; decide +kernel
    rw [ha]
    exact (canonical3333 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 2) (sourceB1141 + difference 2 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 2) (sourceB1141 + difference 2 1) sourceC1141) = raw19394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19394; decide +kernel
    rw [ha]
    exact (canonical19394 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 3) (sourceB1141 + difference 3 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 3) (sourceB1141 + difference 3 1) sourceC1141) = raw3320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3320; decide +kernel
    rw [ha]
    exact (canonical3320 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 4) (sourceB1141 + difference 4 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 4) (sourceB1141 + difference 4 1) sourceC1141) = raw19395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19395; decide +kernel
    rw [ha]
    exact (canonical19395 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1141 + difference 1 5) (sourceB1141 + difference 5 1) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 1 5) (sourceB1141 + difference 5 1) sourceC1141) = raw19396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19396; decide +kernel
    rw [ha]
    exact (canonical19396 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 0) (sourceB1141 + difference 0 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 0) (sourceB1141 + difference 0 2) sourceC1141) = raw3332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3332; decide +kernel
    rw [ha]
    exact (canonical3332 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 1) (sourceB1141 + difference 1 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 1) (sourceB1141 + difference 1 2) sourceC1141) = raw3440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3440; decide +kernel
    rw [ha]
    exact (canonical3440 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 3) (sourceB1141 + difference 3 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 3) (sourceB1141 + difference 3 2) sourceC1141) = raw3319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3319; decide +kernel
    rw [ha]
    exact (canonical3319 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 4) (sourceB1141 + difference 4 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 4) (sourceB1141 + difference 4 2) sourceC1141) = raw3442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3442; decide +kernel
    rw [ha]
    exact (canonical3442 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1141 + difference 2 5) (sourceB1141 + difference 5 2) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4096) := by
    have ha : (tripleCharges (sourceA1141 + difference 2 5) (sourceB1141 + difference 5 2) sourceC1141) = raw3443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3443; decide +kernel
    rw [ha]
    exact (canonical3443 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 0) (sourceB1141 + difference 0 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 0) (sourceB1141 + difference 0 3) sourceC1141) = raw19364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19364; decide +kernel
    rw [ha]
    exact (canonical19364 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 1) (sourceB1141 + difference 1 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 1) (sourceB1141 + difference 1 3) sourceC1141) = raw19397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19397; decide +kernel
    rw [ha]
    exact (canonical19397 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 2) (sourceB1141 + difference 2 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 2) (sourceB1141 + difference 2 3) sourceC1141) = raw19398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19398; decide +kernel
    rw [ha]
    exact (canonical19398 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 4) (sourceB1141 + difference 4 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 4) (sourceB1141 + difference 4 3) sourceC1141) = raw19399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19399; decide +kernel
    rw [ha]
    exact (canonical19399 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1141 + difference 3 5) (sourceB1141 + difference 5 3) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 3 5) (sourceB1141 + difference 5 3) sourceC1141) = raw19400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19400; decide +kernel
    rw [ha]
    exact (canonical19400 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 0) (sourceB1141 + difference 0 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 0) (sourceB1141 + difference 0 4) sourceC1141) = raw19368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19368; decide +kernel
    rw [ha]
    exact (canonical19368 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 1) (sourceB1141 + difference 1 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 1) (sourceB1141 + difference 1 4) sourceC1141) = raw19401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19401; decide +kernel
    rw [ha]
    exact (canonical19401 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 2) (sourceB1141 + difference 2 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 2) (sourceB1141 + difference 2 4) sourceC1141) = raw19402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19402; decide +kernel
    rw [ha]
    exact (canonical19402 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 3) (sourceB1141 + difference 3 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 3) (sourceB1141 + difference 3 4) sourceC1141) = raw3445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3445; decide +kernel
    rw [ha]
    exact (canonical3445 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1141 + difference 4 5) (sourceB1141 + difference 5 4) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 4 5) (sourceB1141 + difference 5 4) sourceC1141) = raw19403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19403; decide +kernel
    rw [ha]
    exact (canonical19403 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 0) (sourceB1141 + difference 0 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 0) (sourceB1141 + difference 0 5) sourceC1141) = raw18338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw18338; decide +kernel
    rw [ha]
    exact (canonical18338 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 1) (sourceB1141 + difference 1 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 1) (sourceB1141 + difference 1 5) sourceC1141) = raw19404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19404; decide +kernel
    rw [ha]
    exact (canonical19404 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 2) (sourceB1141 + difference 2 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 2) (sourceB1141 + difference 2 5) sourceC1141) = raw19405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19405; decide +kernel
    rw [ha]
    exact (canonical19405 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 3) (sourceB1141 + difference 3 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 3) (sourceB1141 + difference 3 5) sourceC1141) = raw3449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw3449; decide +kernel
    rw [ha]
    exact (canonical3449 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1141 + difference 5 4) (sourceB1141 + difference 4 5) sourceC1141) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA1141 + difference 5 4) (sourceB1141 + difference 4 5) sourceC1141) = raw19406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1141 sourceB1141 sourceC1141 difference raw19406; decide +kernel
    rw [ha]
    exact (canonical19406 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1141 sourceB1141 sourceC1141
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1141, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1142 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1142 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC1142 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm1142 : Integer.Sparse Master := [(Sum.inr 617, 1), (Sum.inr 936, 3), (Sum.inr 1064, 1), (Sum.inr 1091, 1), (Sum.inr 4084, -1)]

theorem sourceEq1142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1142 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 0) (sourceB1142 + difference 0 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 617) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 0) (sourceB1142 + difference 0 4) sourceC1142) = raw19407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19407; decide +kernel
    rw [ha]
    exact (canonical19407 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 1) (sourceB1142 + difference 1 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 1) (sourceB1142 + difference 1 4) sourceC1142) = raw19408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19408; decide +kernel
    rw [ha]
    exact (canonical19408 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 2) (sourceB1142 + difference 2 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 2) (sourceB1142 + difference 2 4) sourceC1142) = raw19409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19409; decide +kernel
    rw [ha]
    exact (canonical19409 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 3) (sourceB1142 + difference 3 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 3) (sourceB1142 + difference 3 4) sourceC1142) = raw19410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19410; decide +kernel
    rw [ha]
    exact (canonical19410 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 4) (sourceB1142 + difference 4 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1064) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 4) (sourceB1142 + difference 4 4) sourceC1142) = raw19411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19411; decide +kernel
    rw [ha]
    exact (canonical19411 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1142 + difference 4 5) (sourceB1142 + difference 5 4) sourceC1142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1142 + difference 4 5) (sourceB1142 + difference 5 4) sourceC1142) = raw19412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1142 sourceB1142 sourceC1142 difference raw19412; decide +kernel
    rw [ha]
    exact (canonical19412 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1142 + sourceB1142) sourceC1142) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1142 + sourceB1142) sourceC1142) = raw19413 := by
      apply Matrix.ext; unfold doubleCharges sourceA1142 sourceB1142 sourceC1142 raw19413; decide +kernel
    rw [ha]
    exact (canonical19413 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1142 sourceB1142 sourceC1142
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1142, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1143 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1143 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1143 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1143 : Integer.Sparse Master := [(Sum.inr 862, 1), (Sum.inr 1629, 3), (Sum.inr 1752, 1), (Sum.inr 1757, 1), (Sum.inr 4072, -1)]

theorem sourceEq1143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1143 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 0) (sourceB1143 + difference 0 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1757) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 0) (sourceB1143 + difference 0 0) sourceC1143) = raw19414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19414; decide +kernel
    rw [ha]
    exact (canonical19414 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 1) (sourceB1143 + difference 1 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 1) (sourceB1143 + difference 1 0) sourceC1143) = raw19415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19415; decide +kernel
    rw [ha]
    exact (canonical19415 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 2) (sourceB1143 + difference 2 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 2) (sourceB1143 + difference 2 0) sourceC1143) = raw19416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19416; decide +kernel
    rw [ha]
    exact (canonical19416 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 3) (sourceB1143 + difference 3 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 3) (sourceB1143 + difference 3 0) sourceC1143) = raw19417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19417; decide +kernel
    rw [ha]
    exact (canonical19417 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 4) (sourceB1143 + difference 4 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 4) (sourceB1143 + difference 4 0) sourceC1143) = raw19418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19418; decide +kernel
    rw [ha]
    exact (canonical19418 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1143 + difference 0 5) (sourceB1143 + difference 5 0) sourceC1143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 862) := by
    have ha : (tripleCharges (sourceA1143 + difference 0 5) (sourceB1143 + difference 5 0) sourceC1143) = raw19419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1143 sourceB1143 sourceC1143 difference raw19419; decide +kernel
    rw [ha]
    exact (canonical19419 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1143 + sourceB1143) sourceC1143) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1143 + sourceB1143) sourceC1143) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1143 sourceB1143 sourceC1143 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1143 sourceB1143 sourceC1143
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1143, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1144 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1144 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1144 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1144 : Integer.Sparse Master := [(Sum.inr 854, 3), (Sum.inr 861, 1), (Sum.inr 862, 1), (Sum.inr 1757, 1), (Sum.inr 4072, -1)]

theorem sourceEq1144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1144 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1144 + difference 0 0) (sourceB1144 + difference 0 0) sourceC1144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1757) := by
    have ha : (tripleCharges (sourceA1144 + difference 0 0) (sourceB1144 + difference 0 0) sourceC1144) = raw19414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1144 sourceB1144 sourceC1144 difference raw19414; decide +kernel
    rw [ha]
    exact (canonical19414 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1144 + difference 1 0) (sourceB1144 + difference 0 1) sourceC1144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 854) := by
    have ha : (tripleCharges (sourceA1144 + difference 1 0) (sourceB1144 + difference 0 1) sourceC1144) = raw19421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1144 sourceB1144 sourceC1144 difference raw19421; decide +kernel
    rw [ha]
    exact (canonical19421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1144 + difference 2 0) (sourceB1144 + difference 0 2) sourceC1144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 854) := by
    have ha : (tripleCharges (sourceA1144 + difference 2 0) (sourceB1144 + difference 0 2) sourceC1144) = raw19422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1144 sourceB1144 sourceC1144 difference raw19422; decide +kernel
    rw [ha]
    exact (canonical19422 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1144 + difference 3 0) (sourceB1144 + difference 0 3) sourceC1144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 854) := by
    have ha : (tripleCharges (sourceA1144 + difference 3 0) (sourceB1144 + difference 0 3) sourceC1144) = raw19423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1144 sourceB1144 sourceC1144 difference raw19423; decide +kernel
    rw [ha]
    exact (canonical19423 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1144 + difference 4 0) (sourceB1144 + difference 0 4) sourceC1144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 861) := by
    have ha : (tripleCharges (sourceA1144 + difference 4 0) (sourceB1144 + difference 0 4) sourceC1144) = raw19424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1144 sourceB1144 sourceC1144 difference raw19424; decide +kernel
    rw [ha]
    exact (canonical19424 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1144 + difference 5 0) (sourceB1144 + difference 0 5) sourceC1144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 862) := by
    have ha : (tripleCharges (sourceA1144 + difference 5 0) (sourceB1144 + difference 0 5) sourceC1144) = raw19425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1144 sourceB1144 sourceC1144 difference raw19425; decide +kernel
    rw [ha]
    exact (canonical19425 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1144 + sourceB1144) sourceC1144) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1144 + sourceB1144) sourceC1144) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1144 sourceB1144 sourceC1144 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1144 sourceB1144 sourceC1144
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1144, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1145 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1145 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1145 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1145 : Integer.Sparse Master := [(Sum.inr 1749, 3), (Sum.inr 1752, 2), (Sum.inr 1757, 1), (Sum.inr 4072, -1)]

theorem sourceEq1145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1145 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1145 + difference 0 4) (sourceB1145 + difference 4 0) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1145 + difference 0 4) (sourceB1145 + difference 4 0) sourceC1145) = raw19418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19418; decide +kernel
    rw [ha]
    exact (canonical19418 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1145 + difference 1 4) (sourceB1145 + difference 4 1) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1145 + difference 1 4) (sourceB1145 + difference 4 1) sourceC1145) = raw19426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19426; decide +kernel
    rw [ha]
    exact (canonical19426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1145 + difference 2 4) (sourceB1145 + difference 4 2) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1145 + difference 2 4) (sourceB1145 + difference 4 2) sourceC1145) = raw19427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19427; decide +kernel
    rw [ha]
    exact (canonical19427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1145 + difference 3 4) (sourceB1145 + difference 4 3) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1145 + difference 3 4) (sourceB1145 + difference 4 3) sourceC1145) = raw19428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19428; decide +kernel
    rw [ha]
    exact (canonical19428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1145 + difference 4 4) (sourceB1145 + difference 4 4) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1757) := by
    have ha : (tripleCharges (sourceA1145 + difference 4 4) (sourceB1145 + difference 4 4) sourceC1145) = raw19414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19414; decide +kernel
    rw [ha]
    exact (canonical19414 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1145 + difference 5 4) (sourceB1145 + difference 4 5) sourceC1145) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1145 + difference 5 4) (sourceB1145 + difference 4 5) sourceC1145) = raw19429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1145 sourceB1145 sourceC1145 difference raw19429; decide +kernel
    rw [ha]
    exact (canonical19429 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1145 + sourceB1145) sourceC1145) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1145 + sourceB1145) sourceC1145) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1145 sourceB1145 sourceC1145 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1145 sourceB1145 sourceC1145
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1145, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1146 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1146 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1146 : Charge := ![1, 0, 0, 0, 3, -4]
def sourceForm1146 : Integer.Sparse Master := [(Sum.inr 836, 3), (Sum.inr 839, 1), (Sum.inr 860, 1), (Sum.inr 1747, 1), (Sum.inr 4070, -1)]

theorem sourceEq1146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1146 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1146 + difference 0 0) (sourceB1146 + difference 0 0) sourceC1146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 839) := by
    have ha : (tripleCharges (sourceA1146 + difference 0 0) (sourceB1146 + difference 0 0) sourceC1146) = raw19430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1146 sourceB1146 sourceC1146 difference raw19430; decide +kernel
    rw [ha]
    exact (canonical19430 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1146 + difference 0 1) (sourceB1146 + difference 1 0) sourceC1146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 836) := by
    have ha : (tripleCharges (sourceA1146 + difference 0 1) (sourceB1146 + difference 1 0) sourceC1146) = raw19431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1146 sourceB1146 sourceC1146 difference raw19431; decide +kernel
    rw [ha]
    exact (canonical19431 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1146 + difference 0 2) (sourceB1146 + difference 2 0) sourceC1146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 836) := by
    have ha : (tripleCharges (sourceA1146 + difference 0 2) (sourceB1146 + difference 2 0) sourceC1146) = raw19432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1146 sourceB1146 sourceC1146 difference raw19432; decide +kernel
    rw [ha]
    exact (canonical19432 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1146 + difference 0 3) (sourceB1146 + difference 3 0) sourceC1146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 836) := by
    have ha : (tripleCharges (sourceA1146 + difference 0 3) (sourceB1146 + difference 3 0) sourceC1146) = raw19433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1146 sourceB1146 sourceC1146 difference raw19433; decide +kernel
    rw [ha]
    exact (canonical19433 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1146 + difference 0 4) (sourceB1146 + difference 4 0) sourceC1146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 860) := by
    have ha : (tripleCharges (sourceA1146 + difference 0 4) (sourceB1146 + difference 4 0) sourceC1146) = raw19434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1146 sourceB1146 sourceC1146 difference raw19434; decide +kernel
    rw [ha]
    exact (canonical19434 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1146 + difference 0 5) (sourceB1146 + difference 5 0) sourceC1146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA1146 + difference 0 5) (sourceB1146 + difference 5 0) sourceC1146) = raw19435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1146 sourceB1146 sourceC1146 difference raw19435; decide +kernel
    rw [ha]
    exact (canonical19435 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1146 + sourceB1146) sourceC1146) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1146 + sourceB1146) sourceC1146) = raw19436 := by
      apply Matrix.ext; unfold doubleCharges sourceA1146 sourceB1146 sourceC1146 raw19436; decide +kernel
    rw [ha]
    exact (canonical19436 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1146 sourceB1146 sourceC1146
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1146, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1147 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1147 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1147 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceForm1147 : Integer.Sparse Master := [(Sum.inr 587, 1), (Sum.inr 911, 2), (Sum.inr 951, 1), (Sum.inr 1027, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

theorem sourceEq1147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1147 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 0) (sourceB1147 + difference 0 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 0) (sourceB1147 + difference 0 3) sourceC1147) = raw19437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19437; decide +kernel
    rw [ha]
    exact (canonical19437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 1) (sourceB1147 + difference 1 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 1) (sourceB1147 + difference 1 3) sourceC1147) = raw19438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19438; decide +kernel
    rw [ha]
    exact (canonical19438 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 2) (sourceB1147 + difference 2 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 2) (sourceB1147 + difference 2 3) sourceC1147) = raw19439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19439; decide +kernel
    rw [ha]
    exact (canonical19439 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 3) (sourceB1147 + difference 3 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 3) (sourceB1147 + difference 3 3) sourceC1147) = raw19440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19440; decide +kernel
    rw [ha]
    exact (canonical19440 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 4) (sourceB1147 + difference 4 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 951) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 4) (sourceB1147 + difference 4 3) sourceC1147) = raw19441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19441; decide +kernel
    rw [ha]
    exact (canonical19441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1147 + difference 3 5) (sourceB1147 + difference 5 3) sourceC1147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1147 + difference 3 5) (sourceB1147 + difference 5 3) sourceC1147) = raw19442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1147 sourceB1147 sourceC1147 difference raw19442; decide +kernel
    rw [ha]
    exact (canonical19442 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1147 + sourceB1147) sourceC1147) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1147 + sourceB1147) sourceC1147) = raw19443 := by
      apply Matrix.ext; unfold doubleCharges sourceA1147 sourceB1147 sourceC1147 raw19443; decide +kernel
    rw [ha]
    exact (canonical19443 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1147 sourceB1147 sourceC1147
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1147, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1148 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1148 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC1148 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1148 : Integer.Sparse Master := [(Sum.inr 849, 1), (Sum.inr 1615, 2), (Sum.inr 1749, 1), (Sum.inr 1752, 2), (Sum.inr 4072, -1)]

theorem sourceEq1148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1148 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 0) (sourceB1148 + difference 0 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 0) (sourceB1148 + difference 0 0) sourceC1148) = raw19428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19428; decide +kernel
    rw [ha]
    exact (canonical19428 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 1) (sourceB1148 + difference 1 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1615) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 1) (sourceB1148 + difference 1 0) sourceC1148) = raw19444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19444; decide +kernel
    rw [ha]
    exact (canonical19444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 2) (sourceB1148 + difference 2 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1615) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 2) (sourceB1148 + difference 2 0) sourceC1148) = raw19445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19445; decide +kernel
    rw [ha]
    exact (canonical19445 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 3) (sourceB1148 + difference 3 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 3) (sourceB1148 + difference 3 0) sourceC1148) = raw19418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19418; decide +kernel
    rw [ha]
    exact (canonical19418 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 4) (sourceB1148 + difference 4 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 4) (sourceB1148 + difference 4 0) sourceC1148) = raw19446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19446; decide +kernel
    rw [ha]
    exact (canonical19446 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1148 + difference 0 5) (sourceB1148 + difference 5 0) sourceC1148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 849) := by
    have ha : (tripleCharges (sourceA1148 + difference 0 5) (sourceB1148 + difference 5 0) sourceC1148) = raw19447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1148 sourceB1148 sourceC1148 difference raw19447; decide +kernel
    rw [ha]
    exact (canonical19447 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1148 + sourceB1148) sourceC1148) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1148 + sourceB1148) sourceC1148) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1148 sourceB1148 sourceC1148 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1148 sourceB1148 sourceC1148
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1148, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1149 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1149 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC1149 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1149 : Integer.Sparse Master := [(Sum.inr 846, 2), (Sum.inr 849, 1), (Sum.inr 854, 2), (Sum.inr 1749, 1), (Sum.inr 4072, -1)]

theorem sourceEq1149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1149 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1149 + difference 0 0) (sourceB1149 + difference 0 0) sourceC1149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA1149 + difference 0 0) (sourceB1149 + difference 0 0) sourceC1149) = raw19428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1149 sourceB1149 sourceC1149 difference raw19428; decide +kernel
    rw [ha]
    exact (canonical19428 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1149 + difference 1 0) (sourceB1149 + difference 0 1) sourceC1149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 846) := by
    have ha : (tripleCharges (sourceA1149 + difference 1 0) (sourceB1149 + difference 0 1) sourceC1149) = raw19448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1149 sourceB1149 sourceC1149 difference raw19448; decide +kernel
    rw [ha]
    exact (canonical19448 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1149 + difference 2 0) (sourceB1149 + difference 0 2) sourceC1149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 846) := by
    have ha : (tripleCharges (sourceA1149 + difference 2 0) (sourceB1149 + difference 0 2) sourceC1149) = raw19449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1149 sourceB1149 sourceC1149 difference raw19449; decide +kernel
    rw [ha]
    exact (canonical19449 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1149 + difference 3 0) (sourceB1149 + difference 0 3) sourceC1149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 854) := by
    have ha : (tripleCharges (sourceA1149 + difference 3 0) (sourceB1149 + difference 0 3) sourceC1149) = raw19450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1149 sourceB1149 sourceC1149 difference raw19450; decide +kernel
    rw [ha]
    exact (canonical19450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1149 + difference 4 0) (sourceB1149 + difference 0 4) sourceC1149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 854) := by
    have ha : (tripleCharges (sourceA1149 + difference 4 0) (sourceB1149 + difference 0 4) sourceC1149) = raw19423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1149 sourceB1149 sourceC1149 difference raw19423; decide +kernel
    rw [ha]
    exact (canonical19423 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1149 + difference 5 0) (sourceB1149 + difference 0 5) sourceC1149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 849) := by
    have ha : (tripleCharges (sourceA1149 + difference 5 0) (sourceB1149 + difference 0 5) sourceC1149) = raw19451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1149 sourceB1149 sourceC1149 difference raw19451; decide +kernel
    rw [ha]
    exact (canonical19451 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1149 + sourceB1149) sourceC1149) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1149 + sourceB1149) sourceC1149) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1149 sourceB1149 sourceC1149 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1149 sourceB1149 sourceC1149
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1149, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1150 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1150 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1150 : Charge := ![1, 0, 0, 1, 2, -4]
def sourceForm1150 : Integer.Sparse Master := [(Sum.inr 794, 2), (Sum.inr 797, 1), (Sum.inr 813, 1), (Sum.inr 828, 1), (Sum.inr 1716, 1), (Sum.inr 4069, -1)]

theorem sourceEq1150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1150 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 0) (sourceB1150 + difference 0 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 797) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 0) (sourceB1150 + difference 0 0) sourceC1150) = raw19452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19452; decide +kernel
    rw [ha]
    exact (canonical19452 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 1) (sourceB1150 + difference 1 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 794) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 1) (sourceB1150 + difference 1 0) sourceC1150) = raw19453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19453; decide +kernel
    rw [ha]
    exact (canonical19453 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 2) (sourceB1150 + difference 2 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 794) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 2) (sourceB1150 + difference 2 0) sourceC1150) = raw19454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19454; decide +kernel
    rw [ha]
    exact (canonical19454 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 3) (sourceB1150 + difference 3 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 3) (sourceB1150 + difference 3 0) sourceC1150) = raw19455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19455; decide +kernel
    rw [ha]
    exact (canonical19455 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 4) (sourceB1150 + difference 4 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 4) (sourceB1150 + difference 4 0) sourceC1150) = raw19456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19456; decide +kernel
    rw [ha]
    exact (canonical19456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1150 + difference 0 5) (sourceB1150 + difference 5 0) sourceC1150) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1150 + difference 0 5) (sourceB1150 + difference 5 0) sourceC1150) = raw19457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1150 sourceB1150 sourceC1150 difference raw19457; decide +kernel
    rw [ha]
    exact (canonical19457 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1150 + sourceB1150) sourceC1150) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1150 + sourceB1150) sourceC1150) = raw19458 := by
      apply Matrix.ext; unfold doubleCharges sourceA1150 sourceB1150 sourceC1150 raw19458; decide +kernel
    rw [ha]
    exact (canonical19458 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1150 sourceB1150 sourceC1150
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1150, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1151 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1151 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC1151 : Charge := ![1, 0, 1, 1, 1, -4]
def sourceForm1151 : Integer.Sparse Master := [(Sum.inr 776, 1), (Sum.inr 779, 1), (Sum.inr 787, 3), (Sum.inr 1700, 1), (Sum.inr 4068, -1)]

theorem sourceEq1151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1151 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1151 + difference 0 0) (sourceB1151 + difference 0 0) sourceC1151) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 779) := by
    have ha : (tripleCharges (sourceA1151 + difference 0 0) (sourceB1151 + difference 0 0) sourceC1151) = raw19459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1151 sourceB1151 sourceC1151 difference raw19459; decide +kernel
    rw [ha]
    exact (canonical19459 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1151 + difference 0 1) (sourceB1151 + difference 1 0) sourceC1151) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 776) := by
    have ha : (tripleCharges (sourceA1151 + difference 0 1) (sourceB1151 + difference 1 0) sourceC1151) = raw19460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1151 sourceB1151 sourceC1151 difference raw19460; decide +kernel
    rw [ha]
    exact (canonical19460 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1151 + difference 0 2) (sourceB1151 + difference 2 0) sourceC1151) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1151 + difference 0 2) (sourceB1151 + difference 2 0) sourceC1151) = raw19461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1151 sourceB1151 sourceC1151 difference raw19461; decide +kernel
    rw [ha]
    exact (canonical19461 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1151 + difference 0 3) (sourceB1151 + difference 3 0) sourceC1151) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1151 + difference 0 3) (sourceB1151 + difference 3 0) sourceC1151) = raw19462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1151 sourceB1151 sourceC1151 difference raw19462; decide +kernel
    rw [ha]
    exact (canonical19462 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1151 + difference 0 4) (sourceB1151 + difference 4 0) sourceC1151) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1151 + difference 0 4) (sourceB1151 + difference 4 0) sourceC1151) = raw19463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1151 sourceB1151 sourceC1151 difference raw19463; decide +kernel
    rw [ha]
    exact (canonical19463 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1151 + difference 0 5) (sourceB1151 + difference 5 0) sourceC1151) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1151 + difference 0 5) (sourceB1151 + difference 5 0) sourceC1151) = raw19464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1151 sourceB1151 sourceC1151 difference raw19464; decide +kernel
    rw [ha]
    exact (canonical19464 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1151 + sourceB1151) sourceC1151) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1151 + sourceB1151) sourceC1151) = raw19465 := by
      apply Matrix.ext; unfold doubleCharges sourceA1151 sourceB1151 sourceC1151 raw19465; decide +kernel
    rw [ha]
    exact (canonical19465 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1151 sourceB1151 sourceC1151
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1151, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
