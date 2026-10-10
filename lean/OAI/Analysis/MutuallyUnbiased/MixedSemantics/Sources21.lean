import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical91
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical92

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA672 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB672 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC672 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm672 : Integer.Sparse Master := [(Sum.inr 1698, 1), (Sum.inr 1707, 1), (Sum.inr 1708, 1), (Sum.inr 1714, 2), (Sum.inr 2190, 1), (Sum.inr 2191, 1), (Sum.inr 2195, 2), (Sum.inr 2232, 1), (Sum.inr 2233, 1), (Sum.inr 2242, 1), (Sum.inr 2244, 2), (Sum.inr 2245, 1), (Sum.inr 2251, 2), (Sum.inr 2253, 2), (Sum.inr 2264, 2), (Sum.inr 2265, 2), (Sum.inr 2278, 2), (Sum.inr 2709, 1), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 2767, 2)]

theorem sourceEq672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm672 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA672 + difference 0 1) (sourceB672 + difference 1 0) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA672 + difference 0 1) (sourceB672 + difference 1 0) sourceC672) = raw7243 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw7243; decide +kernel
    rw [ha]
    exact (canonical7243 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA672 + difference 0 2) (sourceB672 + difference 2 0) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA672 + difference 0 2) (sourceB672 + difference 2 0) sourceC672) = raw7936 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw7936; decide +kernel
    rw [ha]
    exact (canonical7936 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA672 + difference 0 3) (sourceB672 + difference 3 0) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA672 + difference 0 3) (sourceB672 + difference 3 0) sourceC672) = raw9928 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw9928; decide +kernel
    rw [ha]
    exact (canonical9928 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA672 + difference 0 4) (sourceB672 + difference 4 0) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA672 + difference 0 4) (sourceB672 + difference 4 0) sourceC672) = raw9053 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw9053; decide +kernel
    rw [ha]
    exact (canonical9053 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA672 + difference 0 5) (sourceB672 + difference 5 0) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA672 + difference 0 5) (sourceB672 + difference 5 0) sourceC672) = raw5690 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw5690; decide +kernel
    rw [ha]
    exact (canonical5690 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA672 + difference 1 0) (sourceB672 + difference 0 1) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA672 + difference 1 0) (sourceB672 + difference 0 1) sourceC672) = raw10985 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw10985; decide +kernel
    rw [ha]
    exact (canonical10985 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA672 + difference 1 2) (sourceB672 + difference 2 1) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA672 + difference 1 2) (sourceB672 + difference 2 1) sourceC672) = raw11382 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw11382; decide +kernel
    rw [ha]
    exact (canonical11382 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA672 + difference 1 3) (sourceB672 + difference 3 1) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA672 + difference 1 3) (sourceB672 + difference 3 1) sourceC672) = raw10986 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw10986; decide +kernel
    rw [ha]
    exact (canonical10986 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA672 + difference 1 4) (sourceB672 + difference 4 1) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA672 + difference 1 4) (sourceB672 + difference 4 1) sourceC672) = raw10987 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw10987; decide +kernel
    rw [ha]
    exact (canonical10987 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA672 + difference 1 5) (sourceB672 + difference 5 1) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA672 + difference 1 5) (sourceB672 + difference 5 1) sourceC672) = raw5695 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw5695; decide +kernel
    rw [ha]
    exact (canonical5695 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA672 + difference 2 0) (sourceB672 + difference 0 2) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA672 + difference 2 0) (sourceB672 + difference 0 2) sourceC672) = raw11383 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw11383; decide +kernel
    rw [ha]
    exact (canonical11383 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA672 + difference 2 1) (sourceB672 + difference 1 2) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA672 + difference 2 1) (sourceB672 + difference 1 2) sourceC672) = raw11384 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw11384; decide +kernel
    rw [ha]
    exact (canonical11384 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA672 + difference 2 3) (sourceB672 + difference 3 2) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA672 + difference 2 3) (sourceB672 + difference 3 2) sourceC672) = raw11385 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw11385; decide +kernel
    rw [ha]
    exact (canonical11385 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA672 + difference 2 4) (sourceB672 + difference 4 2) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA672 + difference 2 4) (sourceB672 + difference 4 2) sourceC672) = raw11386 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw11386; decide +kernel
    rw [ha]
    exact (canonical11386 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA672 + difference 2 5) (sourceB672 + difference 5 2) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA672 + difference 2 5) (sourceB672 + difference 5 2) sourceC672) = raw5700 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw5700; decide +kernel
    rw [ha]
    exact (canonical5700 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA672 + difference 3 0) (sourceB672 + difference 0 3) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA672 + difference 3 0) (sourceB672 + difference 0 3) sourceC672) = raw5713 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw5713; decide +kernel
    rw [ha]
    exact (canonical5713 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA672 + difference 3 1) (sourceB672 + difference 1 3) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA672 + difference 3 1) (sourceB672 + difference 1 3) sourceC672) = raw5714 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw5714; decide +kernel
    rw [ha]
    exact (canonical5714 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA672 + difference 3 2) (sourceB672 + difference 2 3) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA672 + difference 3 2) (sourceB672 + difference 2 3) sourceC672) = raw5715 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw5715; decide +kernel
    rw [ha]
    exact (canonical5715 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA672 + difference 3 4) (sourceB672 + difference 4 3) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA672 + difference 3 4) (sourceB672 + difference 4 3) sourceC672) = raw5717 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw5717; decide +kernel
    rw [ha]
    exact (canonical5717 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA672 + difference 3 5) (sourceB672 + difference 5 3) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA672 + difference 3 5) (sourceB672 + difference 5 3) sourceC672) = raw9241 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw9241; decide +kernel
    rw [ha]
    exact (canonical9241 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA672 + difference 4 0) (sourceB672 + difference 0 4) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA672 + difference 4 0) (sourceB672 + difference 0 4) sourceC672) = raw11184 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw11184; decide +kernel
    rw [ha]
    exact (canonical11184 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA672 + difference 4 1) (sourceB672 + difference 1 4) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA672 + difference 4 1) (sourceB672 + difference 1 4) sourceC672) = raw11185 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw11185; decide +kernel
    rw [ha]
    exact (canonical11185 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA672 + difference 4 2) (sourceB672 + difference 2 4) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA672 + difference 4 2) (sourceB672 + difference 2 4) sourceC672) = raw9930 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw9930; decide +kernel
    rw [ha]
    exact (canonical9930 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA672 + difference 4 3) (sourceB672 + difference 3 4) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA672 + difference 4 3) (sourceB672 + difference 3 4) sourceC672) = raw9925 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw9925; decide +kernel
    rw [ha]
    exact (canonical9925 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA672 + difference 4 5) (sourceB672 + difference 5 4) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA672 + difference 4 5) (sourceB672 + difference 5 4) sourceC672) = raw5711 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw5711; decide +kernel
    rw [ha]
    exact (canonical5711 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA672 + difference 5 0) (sourceB672 + difference 0 5) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA672 + difference 5 0) (sourceB672 + difference 0 5) sourceC672) = raw11387 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw11387; decide +kernel
    rw [ha]
    exact (canonical11387 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA672 + difference 5 1) (sourceB672 + difference 1 5) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA672 + difference 5 1) (sourceB672 + difference 1 5) sourceC672) = raw11388 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw11388; decide +kernel
    rw [ha]
    exact (canonical11388 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA672 + difference 5 2) (sourceB672 + difference 2 5) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA672 + difference 5 2) (sourceB672 + difference 2 5) sourceC672) = raw9692 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw9692; decide +kernel
    rw [ha]
    exact (canonical9692 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA672 + difference 5 3) (sourceB672 + difference 3 5) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA672 + difference 5 3) (sourceB672 + difference 3 5) sourceC672) = raw10166 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw10166; decide +kernel
    rw [ha]
    exact (canonical10166 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA672 + difference 5 4) (sourceB672 + difference 4 5) sourceC672) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA672 + difference 5 4) (sourceB672 + difference 4 5) sourceC672) = raw9686 := by
      apply Matrix.ext; unfold tripleCharges sourceA672 sourceB672 sourceC672 difference raw9686; decide +kernel
    rw [ha]
    exact (canonical9686 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA672 sourceB672 sourceC672
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm672, Integer.Sparse.eval]
  linarith only [hs]

def sourceA673 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB673 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC673 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm673 : Integer.Sparse Master := [(Sum.inr 1405, 1), (Sum.inr 1406, 2), (Sum.inr 1414, 1), (Sum.inr 1441, 1), (Sum.inr 3065, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1), (Sum.inr 3102, 2), (Sum.inr 3179, 1), (Sum.inr 3180, 2), (Sum.inr 3185, 1), (Sum.inr 3202, 2), (Sum.inr 3205, 1), (Sum.inr 3209, 1), (Sum.inr 3221, 1), (Sum.inr 3222, 2), (Sum.inr 3223, 1), (Sum.inr 3225, 2), (Sum.inr 3227, 2), (Sum.inr 3229, 2), (Sum.inr 3230, 2)]

theorem sourceEq673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm673 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA673 + difference 0 1) (sourceB673 + difference 1 0) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA673 + difference 0 1) (sourceB673 + difference 1 0) sourceC673) = raw7261 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw7261; decide +kernel
    rw [ha]
    exact (canonical7261 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA673 + difference 0 2) (sourceB673 + difference 2 0) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA673 + difference 0 2) (sourceB673 + difference 2 0) sourceC673) = raw7949 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw7949; decide +kernel
    rw [ha]
    exact (canonical7949 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA673 + difference 0 3) (sourceB673 + difference 3 0) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA673 + difference 0 3) (sourceB673 + difference 3 0) sourceC673) = raw9952 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw9952; decide +kernel
    rw [ha]
    exact (canonical9952 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA673 + difference 0 4) (sourceB673 + difference 4 0) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA673 + difference 0 4) (sourceB673 + difference 4 0) sourceC673) = raw9065 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw9065; decide +kernel
    rw [ha]
    exact (canonical9065 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA673 + difference 0 5) (sourceB673 + difference 5 0) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA673 + difference 0 5) (sourceB673 + difference 5 0) sourceC673) = raw5720 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw5720; decide +kernel
    rw [ha]
    exact (canonical5720 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA673 + difference 1 0) (sourceB673 + difference 0 1) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA673 + difference 1 0) (sourceB673 + difference 0 1) sourceC673) = raw11003 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11003; decide +kernel
    rw [ha]
    exact (canonical11003 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA673 + difference 1 2) (sourceB673 + difference 2 1) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA673 + difference 1 2) (sourceB673 + difference 2 1) sourceC673) = raw11389 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11389; decide +kernel
    rw [ha]
    exact (canonical11389 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA673 + difference 1 3) (sourceB673 + difference 3 1) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA673 + difference 1 3) (sourceB673 + difference 3 1) sourceC673) = raw11004 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11004; decide +kernel
    rw [ha]
    exact (canonical11004 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA673 + difference 1 4) (sourceB673 + difference 4 1) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA673 + difference 1 4) (sourceB673 + difference 4 1) sourceC673) = raw11005 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11005; decide +kernel
    rw [ha]
    exact (canonical11005 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA673 + difference 1 5) (sourceB673 + difference 5 1) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA673 + difference 1 5) (sourceB673 + difference 5 1) sourceC673) = raw5725 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw5725; decide +kernel
    rw [ha]
    exact (canonical5725 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA673 + difference 2 0) (sourceB673 + difference 0 2) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA673 + difference 2 0) (sourceB673 + difference 0 2) sourceC673) = raw11390 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11390; decide +kernel
    rw [ha]
    exact (canonical11390 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA673 + difference 2 1) (sourceB673 + difference 1 2) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA673 + difference 2 1) (sourceB673 + difference 1 2) sourceC673) = raw11391 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11391; decide +kernel
    rw [ha]
    exact (canonical11391 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA673 + difference 2 3) (sourceB673 + difference 3 2) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA673 + difference 2 3) (sourceB673 + difference 3 2) sourceC673) = raw11392 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11392; decide +kernel
    rw [ha]
    exact (canonical11392 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA673 + difference 2 4) (sourceB673 + difference 4 2) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA673 + difference 2 4) (sourceB673 + difference 4 2) sourceC673) = raw11393 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11393; decide +kernel
    rw [ha]
    exact (canonical11393 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA673 + difference 2 5) (sourceB673 + difference 5 2) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA673 + difference 2 5) (sourceB673 + difference 5 2) sourceC673) = raw5730 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw5730; decide +kernel
    rw [ha]
    exact (canonical5730 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA673 + difference 3 0) (sourceB673 + difference 0 3) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1405) := by
    have ha : (tripleCharges (sourceA673 + difference 3 0) (sourceB673 + difference 0 3) sourceC673) = raw5743 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw5743; decide +kernel
    rw [ha]
    exact (canonical5743 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA673 + difference 3 1) (sourceB673 + difference 1 3) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA673 + difference 3 1) (sourceB673 + difference 1 3) sourceC673) = raw5744 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw5744; decide +kernel
    rw [ha]
    exact (canonical5744 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA673 + difference 3 2) (sourceB673 + difference 2 3) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA673 + difference 3 2) (sourceB673 + difference 2 3) sourceC673) = raw5745 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw5745; decide +kernel
    rw [ha]
    exact (canonical5745 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA673 + difference 3 4) (sourceB673 + difference 4 3) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA673 + difference 3 4) (sourceB673 + difference 4 3) sourceC673) = raw5747 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw5747; decide +kernel
    rw [ha]
    exact (canonical5747 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA673 + difference 3 5) (sourceB673 + difference 5 3) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA673 + difference 3 5) (sourceB673 + difference 5 3) sourceC673) = raw9247 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw9247; decide +kernel
    rw [ha]
    exact (canonical9247 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA673 + difference 4 0) (sourceB673 + difference 0 4) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1441) := by
    have ha : (tripleCharges (sourceA673 + difference 4 0) (sourceB673 + difference 0 4) sourceC673) = raw11196 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11196; decide +kernel
    rw [ha]
    exact (canonical11196 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA673 + difference 4 1) (sourceB673 + difference 1 4) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA673 + difference 4 1) (sourceB673 + difference 1 4) sourceC673) = raw11197 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11197; decide +kernel
    rw [ha]
    exact (canonical11197 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA673 + difference 4 2) (sourceB673 + difference 2 4) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA673 + difference 4 2) (sourceB673 + difference 2 4) sourceC673) = raw9954 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw9954; decide +kernel
    rw [ha]
    exact (canonical9954 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA673 + difference 4 3) (sourceB673 + difference 3 4) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3209) := by
    have ha : (tripleCharges (sourceA673 + difference 4 3) (sourceB673 + difference 3 4) sourceC673) = raw9949 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw9949; decide +kernel
    rw [ha]
    exact (canonical9949 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA673 + difference 4 5) (sourceB673 + difference 5 4) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA673 + difference 4 5) (sourceB673 + difference 5 4) sourceC673) = raw5741 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw5741; decide +kernel
    rw [ha]
    exact (canonical5741 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA673 + difference 5 0) (sourceB673 + difference 0 5) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA673 + difference 5 0) (sourceB673 + difference 0 5) sourceC673) = raw11394 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11394; decide +kernel
    rw [ha]
    exact (canonical11394 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA673 + difference 5 1) (sourceB673 + difference 1 5) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA673 + difference 5 1) (sourceB673 + difference 1 5) sourceC673) = raw11395 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw11395; decide +kernel
    rw [ha]
    exact (canonical11395 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA673 + difference 5 2) (sourceB673 + difference 2 5) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA673 + difference 5 2) (sourceB673 + difference 2 5) sourceC673) = raw9716 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw9716; decide +kernel
    rw [ha]
    exact (canonical9716 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA673 + difference 5 3) (sourceB673 + difference 3 5) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3205) := by
    have ha : (tripleCharges (sourceA673 + difference 5 3) (sourceB673 + difference 3 5) sourceC673) = raw10181 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw10181; decide +kernel
    rw [ha]
    exact (canonical10181 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA673 + difference 5 4) (sourceB673 + difference 4 5) sourceC673) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA673 + difference 5 4) (sourceB673 + difference 4 5) sourceC673) = raw9710 := by
      apply Matrix.ext; unfold tripleCharges sourceA673 sourceB673 sourceC673 difference raw9710; decide +kernel
    rw [ha]
    exact (canonical9710 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA673 sourceB673 sourceC673
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm673, Integer.Sparse.eval]
  linarith only [hs]

def sourceA674 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB674 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC674 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm674 : Integer.Sparse Master := [(Sum.inr 1038, 1), (Sum.inr 1040, 1), (Sum.inr 1042, 2), (Sum.inr 1079, 1), (Sum.inr 2262, 1), (Sum.inr 4084, -1)]

theorem sourceEq674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm674 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA674 + difference 0 0) (sourceB674 + difference 0 0) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA674 + difference 0 0) (sourceB674 + difference 0 0) sourceC674) = raw5770 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw5770; decide +kernel
    rw [ha]
    exact (canonical5770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA674 + difference 1 0) (sourceB674 + difference 0 1) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA674 + difference 1 0) (sourceB674 + difference 0 1) sourceC674) = raw11016 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw11016; decide +kernel
    rw [ha]
    exact (canonical11016 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA674 + difference 2 0) (sourceB674 + difference 0 2) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA674 + difference 2 0) (sourceB674 + difference 0 2) sourceC674) = raw11396 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw11396; decide +kernel
    rw [ha]
    exact (canonical11396 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA674 + difference 3 0) (sourceB674 + difference 0 3) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1038) := by
    have ha : (tripleCharges (sourceA674 + difference 3 0) (sourceB674 + difference 0 3) sourceC674) = raw5759 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw5759; decide +kernel
    rw [ha]
    exact (canonical5759 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA674 + difference 4 0) (sourceB674 + difference 0 4) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA674 + difference 4 0) (sourceB674 + difference 0 4) sourceC674) = raw11201 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw11201; decide +kernel
    rw [ha]
    exact (canonical11201 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA674 + difference 5 0) (sourceB674 + difference 0 5) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA674 + difference 5 0) (sourceB674 + difference 0 5) sourceC674) = raw11397 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw11397; decide +kernel
    rw [ha]
    exact (canonical11397 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA674 + sourceB674) sourceC674) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA674 + sourceB674) sourceC674) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA674 sourceB674 sourceC674 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA674 sourceB674 sourceC674
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm674, Integer.Sparse.eval]
  linarith only [hs]

def sourceA675 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB675 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC675 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm675 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4458, 2), (Sum.inr 4463, 1), (Sum.inr 4467, 1), (Sum.inr 4502, 1), (Sum.inr 4802, 2), (Sum.inr 4807, 2), (Sum.inr 4811, 2), (Sum.inr 4838, 2), (Sum.inr 4866, 2), (Sum.inr 4871, 1), (Sum.inr 4875, 1), (Sum.inr 4888, 2), (Sum.inr 4890, 1), (Sum.inr 4893, 2), (Sum.inr 4895, 2), (Sum.inr 5271, 2), (Sum.inr 5304, 1), (Sum.inr 5306, 1), (Sum.inr 5307, 1)]

theorem sourceEq675 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm675 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA675 + difference 0 1) (sourceB675 + difference 1 0) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA675 + difference 0 1) (sourceB675 + difference 1 0) sourceC675) = raw11398 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11398; decide +kernel
    rw [ha]
    exact (canonical11398 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA675 + difference 0 2) (sourceB675 + difference 2 0) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA675 + difference 0 2) (sourceB675 + difference 2 0) sourceC675) = raw11399 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11399; decide +kernel
    rw [ha]
    exact (canonical11399 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA675 + difference 0 3) (sourceB675 + difference 3 0) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA675 + difference 0 3) (sourceB675 + difference 3 0) sourceC675) = raw11400 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11400; decide +kernel
    rw [ha]
    exact (canonical11400 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA675 + difference 0 4) (sourceB675 + difference 4 0) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA675 + difference 0 4) (sourceB675 + difference 4 0) sourceC675) = raw11401 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11401; decide +kernel
    rw [ha]
    exact (canonical11401 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA675 + difference 0 5) (sourceB675 + difference 5 0) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA675 + difference 0 5) (sourceB675 + difference 5 0) sourceC675) = raw11402 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11402; decide +kernel
    rw [ha]
    exact (canonical11402 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA675 + difference 1 0) (sourceB675 + difference 0 1) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA675 + difference 1 0) (sourceB675 + difference 0 1) sourceC675) = raw11403 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11403; decide +kernel
    rw [ha]
    exact (canonical11403 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA675 + difference 1 2) (sourceB675 + difference 2 1) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA675 + difference 1 2) (sourceB675 + difference 2 1) sourceC675) = raw11404 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11404; decide +kernel
    rw [ha]
    exact (canonical11404 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA675 + difference 1 3) (sourceB675 + difference 3 1) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA675 + difference 1 3) (sourceB675 + difference 3 1) sourceC675) = raw11405 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11405; decide +kernel
    rw [ha]
    exact (canonical11405 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA675 + difference 1 4) (sourceB675 + difference 4 1) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA675 + difference 1 4) (sourceB675 + difference 4 1) sourceC675) = raw11406 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11406; decide +kernel
    rw [ha]
    exact (canonical11406 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA675 + difference 1 5) (sourceB675 + difference 5 1) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA675 + difference 1 5) (sourceB675 + difference 5 1) sourceC675) = raw11407 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11407; decide +kernel
    rw [ha]
    exact (canonical11407 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA675 + difference 2 0) (sourceB675 + difference 0 2) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA675 + difference 2 0) (sourceB675 + difference 0 2) sourceC675) = raw11408 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11408; decide +kernel
    rw [ha]
    exact (canonical11408 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA675 + difference 2 1) (sourceB675 + difference 1 2) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA675 + difference 2 1) (sourceB675 + difference 1 2) sourceC675) = raw11409 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11409; decide +kernel
    rw [ha]
    exact (canonical11409 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA675 + difference 2 3) (sourceB675 + difference 3 2) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA675 + difference 2 3) (sourceB675 + difference 3 2) sourceC675) = raw11410 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11410; decide +kernel
    rw [ha]
    exact (canonical11410 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA675 + difference 2 4) (sourceB675 + difference 4 2) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA675 + difference 2 4) (sourceB675 + difference 4 2) sourceC675) = raw11411 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11411; decide +kernel
    rw [ha]
    exact (canonical11411 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA675 + difference 2 5) (sourceB675 + difference 5 2) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA675 + difference 2 5) (sourceB675 + difference 5 2) sourceC675) = raw11412 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11412; decide +kernel
    rw [ha]
    exact (canonical11412 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA675 + difference 3 0) (sourceB675 + difference 0 3) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA675 + difference 3 0) (sourceB675 + difference 0 3) sourceC675) = raw11413 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11413; decide +kernel
    rw [ha]
    exact (canonical11413 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA675 + difference 3 1) (sourceB675 + difference 1 3) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA675 + difference 3 1) (sourceB675 + difference 1 3) sourceC675) = raw11414 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11414; decide +kernel
    rw [ha]
    exact (canonical11414 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA675 + difference 3 2) (sourceB675 + difference 2 3) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA675 + difference 3 2) (sourceB675 + difference 2 3) sourceC675) = raw11415 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11415; decide +kernel
    rw [ha]
    exact (canonical11415 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA675 + difference 3 4) (sourceB675 + difference 4 3) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA675 + difference 3 4) (sourceB675 + difference 4 3) sourceC675) = raw11416 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11416; decide +kernel
    rw [ha]
    exact (canonical11416 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA675 + difference 3 5) (sourceB675 + difference 5 3) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA675 + difference 3 5) (sourceB675 + difference 5 3) sourceC675) = raw11417 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11417; decide +kernel
    rw [ha]
    exact (canonical11417 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA675 + difference 4 0) (sourceB675 + difference 0 4) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA675 + difference 4 0) (sourceB675 + difference 0 4) sourceC675) = raw11418 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11418; decide +kernel
    rw [ha]
    exact (canonical11418 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA675 + difference 4 1) (sourceB675 + difference 1 4) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA675 + difference 4 1) (sourceB675 + difference 1 4) sourceC675) = raw11419 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11419; decide +kernel
    rw [ha]
    exact (canonical11419 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA675 + difference 4 2) (sourceB675 + difference 2 4) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA675 + difference 4 2) (sourceB675 + difference 2 4) sourceC675) = raw11420 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11420; decide +kernel
    rw [ha]
    exact (canonical11420 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA675 + difference 4 3) (sourceB675 + difference 3 4) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA675 + difference 4 3) (sourceB675 + difference 3 4) sourceC675) = raw11421 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11421; decide +kernel
    rw [ha]
    exact (canonical11421 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA675 + difference 4 5) (sourceB675 + difference 5 4) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA675 + difference 4 5) (sourceB675 + difference 5 4) sourceC675) = raw11422 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11422; decide +kernel
    rw [ha]
    exact (canonical11422 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA675 + difference 5 0) (sourceB675 + difference 0 5) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA675 + difference 5 0) (sourceB675 + difference 0 5) sourceC675) = raw11423 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11423; decide +kernel
    rw [ha]
    exact (canonical11423 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA675 + difference 5 1) (sourceB675 + difference 1 5) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA675 + difference 5 1) (sourceB675 + difference 1 5) sourceC675) = raw11424 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11424; decide +kernel
    rw [ha]
    exact (canonical11424 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA675 + difference 5 2) (sourceB675 + difference 2 5) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA675 + difference 5 2) (sourceB675 + difference 2 5) sourceC675) = raw11425 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11425; decide +kernel
    rw [ha]
    exact (canonical11425 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA675 + difference 5 3) (sourceB675 + difference 3 5) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA675 + difference 5 3) (sourceB675 + difference 3 5) sourceC675) = raw11426 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11426; decide +kernel
    rw [ha]
    exact (canonical11426 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA675 + difference 5 4) (sourceB675 + difference 4 5) sourceC675) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA675 + difference 5 4) (sourceB675 + difference 4 5) sourceC675) = raw11427 := by
      apply Matrix.ext; unfold tripleCharges sourceA675 sourceB675 sourceC675 difference raw11427; decide +kernel
    rw [ha]
    exact (canonical11427 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA675 sourceB675 sourceC675
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm675, Integer.Sparse.eval]
  linarith only [hs]

def sourceA676 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB676 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC676 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm676 : Integer.Sparse Master := [(Sum.inr 1724, 2), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 1753, 1), (Sum.inr 2202, 2), (Sum.inr 2224, 2), (Sum.inr 2225, 2), (Sum.inr 2227, 2), (Sum.inr 2260, 2), (Sum.inr 2262, 2), (Sum.inr 2263, 2), (Sum.inr 2287, 1), (Sum.inr 2288, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 2), (Sum.inr 2739, 2), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 2785, 1), (Sum.inr 4083, 1)]

theorem sourceEq676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm676 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA676 + difference 0 1) (sourceB676 + difference 1 0) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA676 + difference 0 1) (sourceB676 + difference 1 0) sourceC676) = raw11428 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11428; decide +kernel
    rw [ha]
    exact (canonical11428 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA676 + difference 0 2) (sourceB676 + difference 2 0) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA676 + difference 0 2) (sourceB676 + difference 2 0) sourceC676) = raw11429 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11429; decide +kernel
    rw [ha]
    exact (canonical11429 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA676 + difference 0 3) (sourceB676 + difference 3 0) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA676 + difference 0 3) (sourceB676 + difference 3 0) sourceC676) = raw11430 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11430; decide +kernel
    rw [ha]
    exact (canonical11430 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA676 + difference 0 4) (sourceB676 + difference 4 0) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA676 + difference 0 4) (sourceB676 + difference 4 0) sourceC676) = raw11431 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11431; decide +kernel
    rw [ha]
    exact (canonical11431 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA676 + difference 0 5) (sourceB676 + difference 5 0) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2785) := by
    have ha : (tripleCharges (sourceA676 + difference 0 5) (sourceB676 + difference 5 0) sourceC676) = raw11432 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11432; decide +kernel
    rw [ha]
    exact (canonical11432 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA676 + difference 1 0) (sourceB676 + difference 0 1) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA676 + difference 1 0) (sourceB676 + difference 0 1) sourceC676) = raw11433 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11433; decide +kernel
    rw [ha]
    exact (canonical11433 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA676 + difference 1 2) (sourceB676 + difference 2 1) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA676 + difference 1 2) (sourceB676 + difference 2 1) sourceC676) = raw11434 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11434; decide +kernel
    rw [ha]
    exact (canonical11434 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA676 + difference 1 3) (sourceB676 + difference 3 1) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA676 + difference 1 3) (sourceB676 + difference 3 1) sourceC676) = raw11435 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11435; decide +kernel
    rw [ha]
    exact (canonical11435 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA676 + difference 1 4) (sourceB676 + difference 4 1) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA676 + difference 1 4) (sourceB676 + difference 4 1) sourceC676) = raw11436 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11436; decide +kernel
    rw [ha]
    exact (canonical11436 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA676 + difference 1 5) (sourceB676 + difference 5 1) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA676 + difference 1 5) (sourceB676 + difference 5 1) sourceC676) = raw11437 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11437; decide +kernel
    rw [ha]
    exact (canonical11437 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA676 + difference 2 0) (sourceB676 + difference 0 2) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA676 + difference 2 0) (sourceB676 + difference 0 2) sourceC676) = raw11438 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11438; decide +kernel
    rw [ha]
    exact (canonical11438 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA676 + difference 2 1) (sourceB676 + difference 1 2) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA676 + difference 2 1) (sourceB676 + difference 1 2) sourceC676) = raw11439 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11439; decide +kernel
    rw [ha]
    exact (canonical11439 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA676 + difference 2 3) (sourceB676 + difference 3 2) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA676 + difference 2 3) (sourceB676 + difference 3 2) sourceC676) = raw11440 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11440; decide +kernel
    rw [ha]
    exact (canonical11440 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA676 + difference 2 4) (sourceB676 + difference 4 2) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA676 + difference 2 4) (sourceB676 + difference 4 2) sourceC676) = raw11441 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11441; decide +kernel
    rw [ha]
    exact (canonical11441 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA676 + difference 2 5) (sourceB676 + difference 5 2) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA676 + difference 2 5) (sourceB676 + difference 5 2) sourceC676) = raw11442 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11442; decide +kernel
    rw [ha]
    exact (canonical11442 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA676 + difference 3 0) (sourceB676 + difference 0 3) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA676 + difference 3 0) (sourceB676 + difference 0 3) sourceC676) = raw11443 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11443; decide +kernel
    rw [ha]
    exact (canonical11443 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA676 + difference 3 1) (sourceB676 + difference 1 3) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA676 + difference 3 1) (sourceB676 + difference 1 3) sourceC676) = raw11444 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11444; decide +kernel
    rw [ha]
    exact (canonical11444 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA676 + difference 3 2) (sourceB676 + difference 2 3) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA676 + difference 3 2) (sourceB676 + difference 2 3) sourceC676) = raw11445 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11445; decide +kernel
    rw [ha]
    exact (canonical11445 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA676 + difference 3 4) (sourceB676 + difference 4 3) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA676 + difference 3 4) (sourceB676 + difference 4 3) sourceC676) = raw11446 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11446; decide +kernel
    rw [ha]
    exact (canonical11446 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA676 + difference 3 5) (sourceB676 + difference 5 3) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA676 + difference 3 5) (sourceB676 + difference 5 3) sourceC676) = raw11447 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11447; decide +kernel
    rw [ha]
    exact (canonical11447 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA676 + difference 4 0) (sourceB676 + difference 0 4) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA676 + difference 4 0) (sourceB676 + difference 0 4) sourceC676) = raw11448 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11448; decide +kernel
    rw [ha]
    exact (canonical11448 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA676 + difference 4 1) (sourceB676 + difference 1 4) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA676 + difference 4 1) (sourceB676 + difference 1 4) sourceC676) = raw11449 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11449; decide +kernel
    rw [ha]
    exact (canonical11449 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA676 + difference 4 2) (sourceB676 + difference 2 4) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA676 + difference 4 2) (sourceB676 + difference 2 4) sourceC676) = raw11450 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11450; decide +kernel
    rw [ha]
    exact (canonical11450 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA676 + difference 4 3) (sourceB676 + difference 3 4) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA676 + difference 4 3) (sourceB676 + difference 3 4) sourceC676) = raw11451 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11451; decide +kernel
    rw [ha]
    exact (canonical11451 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA676 + difference 4 5) (sourceB676 + difference 5 4) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA676 + difference 4 5) (sourceB676 + difference 5 4) sourceC676) = raw11452 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11452; decide +kernel
    rw [ha]
    exact (canonical11452 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA676 + difference 5 0) (sourceB676 + difference 0 5) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA676 + difference 5 0) (sourceB676 + difference 0 5) sourceC676) = raw11453 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11453; decide +kernel
    rw [ha]
    exact (canonical11453 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA676 + difference 5 1) (sourceB676 + difference 1 5) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA676 + difference 5 1) (sourceB676 + difference 1 5) sourceC676) = raw11454 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11454; decide +kernel
    rw [ha]
    exact (canonical11454 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA676 + difference 5 2) (sourceB676 + difference 2 5) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA676 + difference 5 2) (sourceB676 + difference 2 5) sourceC676) = raw11455 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11455; decide +kernel
    rw [ha]
    exact (canonical11455 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA676 + difference 5 3) (sourceB676 + difference 3 5) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA676 + difference 5 3) (sourceB676 + difference 3 5) sourceC676) = raw11456 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11456; decide +kernel
    rw [ha]
    exact (canonical11456 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA676 + difference 5 4) (sourceB676 + difference 4 5) sourceC676) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA676 + difference 5 4) (sourceB676 + difference 4 5) sourceC676) = raw11457 := by
      apply Matrix.ext; unfold tripleCharges sourceA676 sourceB676 sourceC676 difference raw11457; decide +kernel
    rw [ha]
    exact (canonical11457 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA676 sourceB676 sourceC676
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm676, Integer.Sparse.eval]
  linarith only [hs]

def sourceA677 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB677 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC677 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm677 : Integer.Sparse Master := [(Sum.inr 2107, 2), (Sum.inr 2112, 1), (Sum.inr 2116, 1), (Sum.inr 2265, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

theorem sourceEq677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm677 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA677 + difference 0 1) (sourceB677 + difference 1 0) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA677 + difference 0 1) (sourceB677 + difference 1 0) sourceC677) = raw11458 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11458; decide +kernel
    rw [ha]
    exact (canonical11458 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA677 + difference 1 1) (sourceB677 + difference 1 1) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA677 + difference 1 1) (sourceB677 + difference 1 1) sourceC677) = raw11459 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11459; decide +kernel
    rw [ha]
    exact (canonical11459 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA677 + difference 2 1) (sourceB677 + difference 1 2) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA677 + difference 2 1) (sourceB677 + difference 1 2) sourceC677) = raw11460 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11460; decide +kernel
    rw [ha]
    exact (canonical11460 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA677 + difference 3 1) (sourceB677 + difference 1 3) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA677 + difference 3 1) (sourceB677 + difference 1 3) sourceC677) = raw11461 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11461; decide +kernel
    rw [ha]
    exact (canonical11461 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA677 + difference 4 1) (sourceB677 + difference 1 4) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA677 + difference 4 1) (sourceB677 + difference 1 4) sourceC677) = raw11462 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11462; decide +kernel
    rw [ha]
    exact (canonical11462 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA677 + difference 5 1) (sourceB677 + difference 1 5) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA677 + difference 5 1) (sourceB677 + difference 1 5) sourceC677) = raw11463 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11463; decide +kernel
    rw [ha]
    exact (canonical11463 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA677 + sourceB677) sourceC677) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA677 + sourceB677) sourceC677) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA677 sourceB677 sourceC677 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA677 sourceB677 sourceC677
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm677, Integer.Sparse.eval]
  linarith only [hs]

def sourceA678 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceB678 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC678 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm678 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4495, 2), (Sum.inr 4498, 1), (Sum.inr 4499, 1), (Sum.inr 4503, 1), (Sum.inr 4831, 2), (Sum.inr 4834, 2), (Sum.inr 4835, 2), (Sum.inr 4839, 2), (Sum.inr 4888, 2), (Sum.inr 4889, 2), (Sum.inr 4894, 1), (Sum.inr 4895, 2), (Sum.inr 4896, 2), (Sum.inr 4898, 1), (Sum.inr 4901, 1), (Sum.inr 5259, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5309, 1)]

theorem sourceEq678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm678 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA678 + difference 0 1) (sourceB678 + difference 1 0) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA678 + difference 0 1) (sourceB678 + difference 1 0) sourceC678) = raw7659 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw7659; decide +kernel
    rw [ha]
    exact (canonical7659 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA678 + difference 0 2) (sourceB678 + difference 2 0) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA678 + difference 0 2) (sourceB678 + difference 2 0) sourceC678) = raw9907 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw9907; decide +kernel
    rw [ha]
    exact (canonical9907 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA678 + difference 0 3) (sourceB678 + difference 3 0) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA678 + difference 0 3) (sourceB678 + difference 3 0) sourceC678) = raw10155 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw10155; decide +kernel
    rw [ha]
    exact (canonical10155 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA678 + difference 0 4) (sourceB678 + difference 4 0) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA678 + difference 0 4) (sourceB678 + difference 4 0) sourceC678) = raw7923 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw7923; decide +kernel
    rw [ha]
    exact (canonical7923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA678 + difference 0 5) (sourceB678 + difference 5 0) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA678 + difference 0 5) (sourceB678 + difference 5 0) sourceC678) = raw7651 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw7651; decide +kernel
    rw [ha]
    exact (canonical7651 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA678 + difference 1 0) (sourceB678 + difference 0 1) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA678 + difference 1 0) (sourceB678 + difference 0 1) sourceC678) = raw10973 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw10973; decide +kernel
    rw [ha]
    exact (canonical10973 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA678 + difference 1 2) (sourceB678 + difference 2 1) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA678 + difference 1 2) (sourceB678 + difference 2 1) sourceC678) = raw10974 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw10974; decide +kernel
    rw [ha]
    exact (canonical10974 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA678 + difference 1 3) (sourceB678 + difference 3 1) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA678 + difference 1 3) (sourceB678 + difference 3 1) sourceC678) = raw9896 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw9896; decide +kernel
    rw [ha]
    exact (canonical9896 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA678 + difference 1 4) (sourceB678 + difference 4 1) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA678 + difference 1 4) (sourceB678 + difference 4 1) sourceC678) = raw11375 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw11375; decide +kernel
    rw [ha]
    exact (canonical11375 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA678 + difference 1 5) (sourceB678 + difference 5 1) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA678 + difference 1 5) (sourceB678 + difference 5 1) sourceC678) = raw10975 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw10975; decide +kernel
    rw [ha]
    exact (canonical10975 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA678 + difference 2 0) (sourceB678 + difference 0 2) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA678 + difference 2 0) (sourceB678 + difference 0 2) sourceC678) = raw11172 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw11172; decide +kernel
    rw [ha]
    exact (canonical11172 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA678 + difference 2 1) (sourceB678 + difference 1 2) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA678 + difference 2 1) (sourceB678 + difference 1 2) sourceC678) = raw11173 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw11173; decide +kernel
    rw [ha]
    exact (canonical11173 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA678 + difference 2 3) (sourceB678 + difference 3 2) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA678 + difference 2 3) (sourceB678 + difference 3 2) sourceC678) = raw9901 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw9901; decide +kernel
    rw [ha]
    exact (canonical9901 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA678 + difference 2 4) (sourceB678 + difference 4 2) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA678 + difference 2 4) (sourceB678 + difference 4 2) sourceC678) = raw5686 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw5686; decide +kernel
    rw [ha]
    exact (canonical5686 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA678 + difference 2 5) (sourceB678 + difference 5 2) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA678 + difference 2 5) (sourceB678 + difference 5 2) sourceC678) = raw5681 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw5681; decide +kernel
    rw [ha]
    exact (canonical5681 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA678 + difference 3 0) (sourceB678 + difference 0 3) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA678 + difference 3 0) (sourceB678 + difference 0 3) sourceC678) = raw11465 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw11465; decide +kernel
    rw [ha]
    exact (canonical11465 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA678 + difference 3 1) (sourceB678 + difference 1 3) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA678 + difference 3 1) (sourceB678 + difference 1 3) sourceC678) = raw7925 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw7925; decide +kernel
    rw [ha]
    exact (canonical7925 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA678 + difference 3 2) (sourceB678 + difference 2 3) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA678 + difference 3 2) (sourceB678 + difference 2 3) sourceC678) = raw11466 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw11466; decide +kernel
    rw [ha]
    exact (canonical11466 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA678 + difference 3 4) (sourceB678 + difference 4 3) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA678 + difference 3 4) (sourceB678 + difference 4 3) sourceC678) = raw5685 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw5685; decide +kernel
    rw [ha]
    exact (canonical5685 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA678 + difference 3 5) (sourceB678 + difference 5 3) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA678 + difference 3 5) (sourceB678 + difference 5 3) sourceC678) = raw5680 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw5680; decide +kernel
    rw [ha]
    exact (canonical5680 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA678 + difference 4 0) (sourceB678 + difference 0 4) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA678 + difference 4 0) (sourceB678 + difference 0 4) sourceC678) = raw11467 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw11467; decide +kernel
    rw [ha]
    exact (canonical11467 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA678 + difference 4 1) (sourceB678 + difference 1 4) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA678 + difference 4 1) (sourceB678 + difference 1 4) sourceC678) = raw7656 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw7656; decide +kernel
    rw [ha]
    exact (canonical7656 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA678 + difference 4 2) (sourceB678 + difference 2 4) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA678 + difference 4 2) (sourceB678 + difference 2 4) sourceC678) = raw11468 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw11468; decide +kernel
    rw [ha]
    exact (canonical11468 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA678 + difference 4 3) (sourceB678 + difference 3 4) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA678 + difference 4 3) (sourceB678 + difference 3 4) sourceC678) = raw9908 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw9908; decide +kernel
    rw [ha]
    exact (canonical9908 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA678 + difference 4 5) (sourceB678 + difference 5 4) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA678 + difference 4 5) (sourceB678 + difference 5 4) sourceC678) = raw7648 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw7648; decide +kernel
    rw [ha]
    exact (canonical7648 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA678 + difference 5 0) (sourceB678 + difference 0 5) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA678 + difference 5 0) (sourceB678 + difference 0 5) sourceC678) = raw11469 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw11469; decide +kernel
    rw [ha]
    exact (canonical11469 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA678 + difference 5 1) (sourceB678 + difference 1 5) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA678 + difference 5 1) (sourceB678 + difference 1 5) sourceC678) = raw10575 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw10575; decide +kernel
    rw [ha]
    exact (canonical10575 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA678 + difference 5 2) (sourceB678 + difference 2 5) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA678 + difference 5 2) (sourceB678 + difference 2 5) sourceC678) = raw11470 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw11470; decide +kernel
    rw [ha]
    exact (canonical11470 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA678 + difference 5 3) (sourceB678 + difference 3 5) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA678 + difference 5 3) (sourceB678 + difference 3 5) sourceC678) = raw9911 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw9911; decide +kernel
    rw [ha]
    exact (canonical9911 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA678 + difference 5 4) (sourceB678 + difference 4 5) sourceC678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA678 + difference 5 4) (sourceB678 + difference 4 5) sourceC678) = raw9668 := by
      apply Matrix.ext; unfold tripleCharges sourceA678 sourceB678 sourceC678 difference raw9668; decide +kernel
    rw [ha]
    exact (canonical9668 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA678 sourceB678 sourceC678
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm678, Integer.Sparse.eval]
  linarith only [hs]

def sourceA679 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB679 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC679 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm679 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4457, 2), (Sum.inr 4460, 1), (Sum.inr 4466, 1), (Sum.inr 4498, 1), (Sum.inr 4801, 2), (Sum.inr 4804, 2), (Sum.inr 4810, 2), (Sum.inr 4834, 2), (Sum.inr 4865, 2), (Sum.inr 4868, 1), (Sum.inr 4874, 1), (Sum.inr 4888, 2), (Sum.inr 4894, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4897, 1), (Sum.inr 5258, 2), (Sum.inr 5291, 1), (Sum.inr 5293, 1), (Sum.inr 5308, 1)]

theorem sourceEq679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm679 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA679 + difference 0 1) (sourceB679 + difference 1 0) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA679 + difference 0 1) (sourceB679 + difference 1 0) sourceC679) = raw11471 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11471; decide +kernel
    rw [ha]
    exact (canonical11471 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA679 + difference 0 2) (sourceB679 + difference 2 0) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA679 + difference 0 2) (sourceB679 + difference 2 0) sourceC679) = raw11472 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11472; decide +kernel
    rw [ha]
    exact (canonical11472 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA679 + difference 0 3) (sourceB679 + difference 3 0) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA679 + difference 0 3) (sourceB679 + difference 3 0) sourceC679) = raw11473 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11473; decide +kernel
    rw [ha]
    exact (canonical11473 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA679 + difference 0 4) (sourceB679 + difference 4 0) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA679 + difference 0 4) (sourceB679 + difference 4 0) sourceC679) = raw11474 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11474; decide +kernel
    rw [ha]
    exact (canonical11474 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA679 + difference 0 5) (sourceB679 + difference 5 0) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA679 + difference 0 5) (sourceB679 + difference 5 0) sourceC679) = raw11475 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11475; decide +kernel
    rw [ha]
    exact (canonical11475 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA679 + difference 1 0) (sourceB679 + difference 0 1) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA679 + difference 1 0) (sourceB679 + difference 0 1) sourceC679) = raw11476 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11476; decide +kernel
    rw [ha]
    exact (canonical11476 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA679 + difference 1 2) (sourceB679 + difference 2 1) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA679 + difference 1 2) (sourceB679 + difference 2 1) sourceC679) = raw11477 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11477; decide +kernel
    rw [ha]
    exact (canonical11477 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA679 + difference 1 3) (sourceB679 + difference 3 1) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA679 + difference 1 3) (sourceB679 + difference 3 1) sourceC679) = raw11478 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11478; decide +kernel
    rw [ha]
    exact (canonical11478 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA679 + difference 1 4) (sourceB679 + difference 4 1) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA679 + difference 1 4) (sourceB679 + difference 4 1) sourceC679) = raw11479 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11479; decide +kernel
    rw [ha]
    exact (canonical11479 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA679 + difference 1 5) (sourceB679 + difference 5 1) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA679 + difference 1 5) (sourceB679 + difference 5 1) sourceC679) = raw11480 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11480; decide +kernel
    rw [ha]
    exact (canonical11480 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA679 + difference 2 0) (sourceB679 + difference 0 2) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA679 + difference 2 0) (sourceB679 + difference 0 2) sourceC679) = raw11481 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11481; decide +kernel
    rw [ha]
    exact (canonical11481 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA679 + difference 2 1) (sourceB679 + difference 1 2) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA679 + difference 2 1) (sourceB679 + difference 1 2) sourceC679) = raw11482 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11482; decide +kernel
    rw [ha]
    exact (canonical11482 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA679 + difference 2 3) (sourceB679 + difference 3 2) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA679 + difference 2 3) (sourceB679 + difference 3 2) sourceC679) = raw11483 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11483; decide +kernel
    rw [ha]
    exact (canonical11483 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA679 + difference 2 4) (sourceB679 + difference 4 2) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA679 + difference 2 4) (sourceB679 + difference 4 2) sourceC679) = raw11484 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11484; decide +kernel
    rw [ha]
    exact (canonical11484 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA679 + difference 2 5) (sourceB679 + difference 5 2) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA679 + difference 2 5) (sourceB679 + difference 5 2) sourceC679) = raw11485 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11485; decide +kernel
    rw [ha]
    exact (canonical11485 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA679 + difference 3 0) (sourceB679 + difference 0 3) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA679 + difference 3 0) (sourceB679 + difference 0 3) sourceC679) = raw11486 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11486; decide +kernel
    rw [ha]
    exact (canonical11486 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA679 + difference 3 1) (sourceB679 + difference 1 3) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA679 + difference 3 1) (sourceB679 + difference 1 3) sourceC679) = raw11487 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11487; decide +kernel
    rw [ha]
    exact (canonical11487 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA679 + difference 3 2) (sourceB679 + difference 2 3) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA679 + difference 3 2) (sourceB679 + difference 2 3) sourceC679) = raw11488 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11488; decide +kernel
    rw [ha]
    exact (canonical11488 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA679 + difference 3 4) (sourceB679 + difference 4 3) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA679 + difference 3 4) (sourceB679 + difference 4 3) sourceC679) = raw11489 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11489; decide +kernel
    rw [ha]
    exact (canonical11489 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA679 + difference 3 5) (sourceB679 + difference 5 3) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA679 + difference 3 5) (sourceB679 + difference 5 3) sourceC679) = raw11490 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11490; decide +kernel
    rw [ha]
    exact (canonical11490 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA679 + difference 4 0) (sourceB679 + difference 0 4) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA679 + difference 4 0) (sourceB679 + difference 0 4) sourceC679) = raw11491 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11491; decide +kernel
    rw [ha]
    exact (canonical11491 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA679 + difference 4 1) (sourceB679 + difference 1 4) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA679 + difference 4 1) (sourceB679 + difference 1 4) sourceC679) = raw11492 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11492; decide +kernel
    rw [ha]
    exact (canonical11492 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA679 + difference 4 2) (sourceB679 + difference 2 4) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA679 + difference 4 2) (sourceB679 + difference 2 4) sourceC679) = raw11493 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11493; decide +kernel
    rw [ha]
    exact (canonical11493 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA679 + difference 4 3) (sourceB679 + difference 3 4) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA679 + difference 4 3) (sourceB679 + difference 3 4) sourceC679) = raw11494 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11494; decide +kernel
    rw [ha]
    exact (canonical11494 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA679 + difference 4 5) (sourceB679 + difference 5 4) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA679 + difference 4 5) (sourceB679 + difference 5 4) sourceC679) = raw11495 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11495; decide +kernel
    rw [ha]
    exact (canonical11495 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA679 + difference 5 0) (sourceB679 + difference 0 5) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA679 + difference 5 0) (sourceB679 + difference 0 5) sourceC679) = raw11496 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11496; decide +kernel
    rw [ha]
    exact (canonical11496 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA679 + difference 5 1) (sourceB679 + difference 1 5) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA679 + difference 5 1) (sourceB679 + difference 1 5) sourceC679) = raw11497 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11497; decide +kernel
    rw [ha]
    exact (canonical11497 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA679 + difference 5 2) (sourceB679 + difference 2 5) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA679 + difference 5 2) (sourceB679 + difference 2 5) sourceC679) = raw11498 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11498; decide +kernel
    rw [ha]
    exact (canonical11498 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA679 + difference 5 3) (sourceB679 + difference 3 5) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA679 + difference 5 3) (sourceB679 + difference 3 5) sourceC679) = raw11499 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11499; decide +kernel
    rw [ha]
    exact (canonical11499 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA679 + difference 5 4) (sourceB679 + difference 4 5) sourceC679) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA679 + difference 5 4) (sourceB679 + difference 4 5) sourceC679) = raw11500 := by
      apply Matrix.ext; unfold tripleCharges sourceA679 sourceB679 sourceC679 difference raw11500; decide +kernel
    rw [ha]
    exact (canonical11500 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA679 sourceB679 sourceC679
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm679, Integer.Sparse.eval]
  linarith only [hs]

def sourceA680 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB680 : Charge := ![0, 0, 0, 0, 1, -1]
def sourceC680 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm680 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4499, 3), (Sum.inr 4507, 1), (Sum.inr 4511, 1), (Sum.inr 4835, 6), (Sum.inr 4843, 3), (Sum.inr 4846, 3), (Sum.inr 4895, 3), (Sum.inr 4896, 3), (Sum.inr 4899, 1), (Sum.inr 5275, 3), (Sum.inr 5309, 1), (Sum.inr 5310, 1)]

theorem sourceEq680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm680 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA680 + difference 0 1) (sourceB680 + difference 1 0) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA680 + difference 0 1) (sourceB680 + difference 1 0) sourceC680) = raw11501 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11501; decide +kernel
    rw [ha]
    exact (canonical11501 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA680 + difference 0 2) (sourceB680 + difference 2 0) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA680 + difference 0 2) (sourceB680 + difference 2 0) sourceC680) = raw11502 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11502; decide +kernel
    rw [ha]
    exact (canonical11502 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA680 + difference 0 3) (sourceB680 + difference 3 0) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA680 + difference 0 3) (sourceB680 + difference 3 0) sourceC680) = raw11503 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11503; decide +kernel
    rw [ha]
    exact (canonical11503 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA680 + difference 0 4) (sourceB680 + difference 4 0) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA680 + difference 0 4) (sourceB680 + difference 4 0) sourceC680) = raw11504 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11504; decide +kernel
    rw [ha]
    exact (canonical11504 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA680 + difference 0 5) (sourceB680 + difference 5 0) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA680 + difference 0 5) (sourceB680 + difference 5 0) sourceC680) = raw11505 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11505; decide +kernel
    rw [ha]
    exact (canonical11505 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA680 + difference 1 0) (sourceB680 + difference 0 1) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA680 + difference 1 0) (sourceB680 + difference 0 1) sourceC680) = raw11506 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11506; decide +kernel
    rw [ha]
    exact (canonical11506 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA680 + difference 1 2) (sourceB680 + difference 2 1) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA680 + difference 1 2) (sourceB680 + difference 2 1) sourceC680) = raw11507 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11507; decide +kernel
    rw [ha]
    exact (canonical11507 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA680 + difference 1 3) (sourceB680 + difference 3 1) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA680 + difference 1 3) (sourceB680 + difference 3 1) sourceC680) = raw11508 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11508; decide +kernel
    rw [ha]
    exact (canonical11508 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA680 + difference 1 4) (sourceB680 + difference 4 1) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA680 + difference 1 4) (sourceB680 + difference 4 1) sourceC680) = raw11509 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11509; decide +kernel
    rw [ha]
    exact (canonical11509 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA680 + difference 1 5) (sourceB680 + difference 5 1) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA680 + difference 1 5) (sourceB680 + difference 5 1) sourceC680) = raw11510 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11510; decide +kernel
    rw [ha]
    exact (canonical11510 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA680 + difference 2 0) (sourceB680 + difference 0 2) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA680 + difference 2 0) (sourceB680 + difference 0 2) sourceC680) = raw11511 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11511; decide +kernel
    rw [ha]
    exact (canonical11511 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA680 + difference 2 1) (sourceB680 + difference 1 2) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA680 + difference 2 1) (sourceB680 + difference 1 2) sourceC680) = raw11512 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11512; decide +kernel
    rw [ha]
    exact (canonical11512 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA680 + difference 2 3) (sourceB680 + difference 3 2) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA680 + difference 2 3) (sourceB680 + difference 3 2) sourceC680) = raw11513 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11513; decide +kernel
    rw [ha]
    exact (canonical11513 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA680 + difference 2 4) (sourceB680 + difference 4 2) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA680 + difference 2 4) (sourceB680 + difference 4 2) sourceC680) = raw11514 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11514; decide +kernel
    rw [ha]
    exact (canonical11514 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA680 + difference 2 5) (sourceB680 + difference 5 2) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA680 + difference 2 5) (sourceB680 + difference 5 2) sourceC680) = raw11515 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11515; decide +kernel
    rw [ha]
    exact (canonical11515 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA680 + difference 3 0) (sourceB680 + difference 0 3) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA680 + difference 3 0) (sourceB680 + difference 0 3) sourceC680) = raw11516 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11516; decide +kernel
    rw [ha]
    exact (canonical11516 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA680 + difference 3 1) (sourceB680 + difference 1 3) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA680 + difference 3 1) (sourceB680 + difference 1 3) sourceC680) = raw11517 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11517; decide +kernel
    rw [ha]
    exact (canonical11517 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA680 + difference 3 2) (sourceB680 + difference 2 3) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA680 + difference 3 2) (sourceB680 + difference 2 3) sourceC680) = raw11518 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11518; decide +kernel
    rw [ha]
    exact (canonical11518 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA680 + difference 3 4) (sourceB680 + difference 4 3) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA680 + difference 3 4) (sourceB680 + difference 4 3) sourceC680) = raw11519 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11519; decide +kernel
    rw [ha]
    exact (canonical11519 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA680 + difference 3 5) (sourceB680 + difference 5 3) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA680 + difference 3 5) (sourceB680 + difference 5 3) sourceC680) = raw11520 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11520; decide +kernel
    rw [ha]
    exact (canonical11520 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA680 + difference 4 0) (sourceB680 + difference 0 4) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA680 + difference 4 0) (sourceB680 + difference 0 4) sourceC680) = raw11521 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11521; decide +kernel
    rw [ha]
    exact (canonical11521 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA680 + difference 4 1) (sourceB680 + difference 1 4) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA680 + difference 4 1) (sourceB680 + difference 1 4) sourceC680) = raw11522 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11522; decide +kernel
    rw [ha]
    exact (canonical11522 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA680 + difference 4 2) (sourceB680 + difference 2 4) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA680 + difference 4 2) (sourceB680 + difference 2 4) sourceC680) = raw11523 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11523; decide +kernel
    rw [ha]
    exact (canonical11523 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA680 + difference 4 3) (sourceB680 + difference 3 4) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA680 + difference 4 3) (sourceB680 + difference 3 4) sourceC680) = raw11524 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11524; decide +kernel
    rw [ha]
    exact (canonical11524 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA680 + difference 4 5) (sourceB680 + difference 5 4) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA680 + difference 4 5) (sourceB680 + difference 5 4) sourceC680) = raw11525 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11525; decide +kernel
    rw [ha]
    exact (canonical11525 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA680 + difference 5 0) (sourceB680 + difference 0 5) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA680 + difference 5 0) (sourceB680 + difference 0 5) sourceC680) = raw11526 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11526; decide +kernel
    rw [ha]
    exact (canonical11526 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA680 + difference 5 1) (sourceB680 + difference 1 5) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA680 + difference 5 1) (sourceB680 + difference 1 5) sourceC680) = raw11527 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11527; decide +kernel
    rw [ha]
    exact (canonical11527 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA680 + difference 5 2) (sourceB680 + difference 2 5) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA680 + difference 5 2) (sourceB680 + difference 2 5) sourceC680) = raw11528 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11528; decide +kernel
    rw [ha]
    exact (canonical11528 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA680 + difference 5 3) (sourceB680 + difference 3 5) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA680 + difference 5 3) (sourceB680 + difference 3 5) sourceC680) = raw11529 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11529; decide +kernel
    rw [ha]
    exact (canonical11529 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA680 + difference 5 4) (sourceB680 + difference 4 5) sourceC680) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA680 + difference 5 4) (sourceB680 + difference 4 5) sourceC680) = raw11530 := by
      apply Matrix.ext; unfold tripleCharges sourceA680 sourceB680 sourceC680 difference raw11530; decide +kernel
    rw [ha]
    exact (canonical11530 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA680 sourceB680 sourceC680
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm680, Integer.Sparse.eval]
  linarith only [hs]

def sourceA681 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB681 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC681 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm681 : Integer.Sparse Master := [(Sum.inr 4069, 3), (Sum.inr 4070, 1), (Sum.inr 4071, 1), (Sum.inr 4080, 6), (Sum.inr 4081, 3), (Sum.inr 4082, 3), (Sum.inr 4083, 3), (Sum.inr 4084, 4), (Sum.inr 4085, 1), (Sum.inr 4092, 3), (Sum.inr 4093, 1), (Sum.inr 4094, 1)]

theorem sourceEq681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm681 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA681 + difference 0 1) (sourceB681 + difference 1 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA681 + difference 0 1) (sourceB681 + difference 1 0) sourceC681) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA681 + difference 0 2) (sourceB681 + difference 2 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA681 + difference 0 2) (sourceB681 + difference 2 0) sourceC681) = raw2931 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2931; decide +kernel
    rw [ha]
    exact (canonical2931 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA681 + difference 0 3) (sourceB681 + difference 3 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA681 + difference 0 3) (sourceB681 + difference 3 0) sourceC681) = raw2932 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2932; decide +kernel
    rw [ha]
    exact (canonical2932 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA681 + difference 0 4) (sourceB681 + difference 4 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA681 + difference 0 4) (sourceB681 + difference 4 0) sourceC681) = raw3340 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3340; decide +kernel
    rw [ha]
    exact (canonical3340 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA681 + difference 0 5) (sourceB681 + difference 5 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA681 + difference 0 5) (sourceB681 + difference 5 0) sourceC681) = raw2933 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2933; decide +kernel
    rw [ha]
    exact (canonical2933 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA681 + difference 1 0) (sourceB681 + difference 0 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA681 + difference 1 0) (sourceB681 + difference 0 1) sourceC681) = raw11531 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11531; decide +kernel
    rw [ha]
    exact (canonical11531 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA681 + difference 1 2) (sourceB681 + difference 2 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 1 2) (sourceB681 + difference 2 1) sourceC681) = raw11532 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11532; decide +kernel
    rw [ha]
    exact (canonical11532 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA681 + difference 1 3) (sourceB681 + difference 3 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 1 3) (sourceB681 + difference 3 1) sourceC681) = raw11533 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11533; decide +kernel
    rw [ha]
    exact (canonical11533 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA681 + difference 1 4) (sourceB681 + difference 4 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA681 + difference 1 4) (sourceB681 + difference 4 1) sourceC681) = raw2914 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2914; decide +kernel
    rw [ha]
    exact (canonical2914 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA681 + difference 1 5) (sourceB681 + difference 5 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA681 + difference 1 5) (sourceB681 + difference 5 1) sourceC681) = raw3323 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3323; decide +kernel
    rw [ha]
    exact (canonical3323 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA681 + difference 2 0) (sourceB681 + difference 0 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA681 + difference 2 0) (sourceB681 + difference 0 2) sourceC681) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA681 + difference 2 1) (sourceB681 + difference 1 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 2 1) (sourceB681 + difference 1 2) sourceC681) = raw11535 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11535; decide +kernel
    rw [ha]
    exact (canonical11535 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA681 + difference 2 3) (sourceB681 + difference 3 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 2 3) (sourceB681 + difference 3 2) sourceC681) = raw11536 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11536; decide +kernel
    rw [ha]
    exact (canonical11536 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA681 + difference 2 4) (sourceB681 + difference 4 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA681 + difference 2 4) (sourceB681 + difference 4 2) sourceC681) = raw2919 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2919; decide +kernel
    rw [ha]
    exact (canonical2919 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA681 + difference 2 5) (sourceB681 + difference 5 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA681 + difference 2 5) (sourceB681 + difference 5 2) sourceC681) = raw3327 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3327; decide +kernel
    rw [ha]
    exact (canonical3327 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA681 + difference 3 0) (sourceB681 + difference 0 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA681 + difference 3 0) (sourceB681 + difference 0 3) sourceC681) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA681 + difference 3 1) (sourceB681 + difference 1 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 3 1) (sourceB681 + difference 1 3) sourceC681) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA681 + difference 3 2) (sourceB681 + difference 2 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 3 2) (sourceB681 + difference 2 3) sourceC681) = raw11539 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11539; decide +kernel
    rw [ha]
    exact (canonical11539 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA681 + difference 3 4) (sourceB681 + difference 4 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA681 + difference 3 4) (sourceB681 + difference 4 3) sourceC681) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA681 + difference 3 5) (sourceB681 + difference 5 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA681 + difference 3 5) (sourceB681 + difference 5 3) sourceC681) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA681 + difference 4 0) (sourceB681 + difference 0 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA681 + difference 4 0) (sourceB681 + difference 0 4) sourceC681) = raw11540 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11540; decide +kernel
    rw [ha]
    exact (canonical11540 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA681 + difference 4 1) (sourceB681 + difference 1 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA681 + difference 4 1) (sourceB681 + difference 1 4) sourceC681) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA681 + difference 4 2) (sourceB681 + difference 2 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA681 + difference 4 2) (sourceB681 + difference 2 4) sourceC681) = raw11542 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11542; decide +kernel
    rw [ha]
    exact (canonical11542 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA681 + difference 4 3) (sourceB681 + difference 3 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA681 + difference 4 3) (sourceB681 + difference 3 4) sourceC681) = raw11543 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11543; decide +kernel
    rw [ha]
    exact (canonical11543 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA681 + difference 4 5) (sourceB681 + difference 5 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA681 + difference 4 5) (sourceB681 + difference 5 4) sourceC681) = raw3335 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3335; decide +kernel
    rw [ha]
    exact (canonical3335 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA681 + difference 5 0) (sourceB681 + difference 0 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA681 + difference 5 0) (sourceB681 + difference 0 5) sourceC681) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA681 + difference 5 1) (sourceB681 + difference 1 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA681 + difference 5 1) (sourceB681 + difference 1 5) sourceC681) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA681 + difference 5 2) (sourceB681 + difference 2 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA681 + difference 5 2) (sourceB681 + difference 2 5) sourceC681) = raw5211 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw5211; decide +kernel
    rw [ha]
    exact (canonical5211 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA681 + difference 5 3) (sourceB681 + difference 3 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA681 + difference 5 3) (sourceB681 + difference 3 5) sourceC681) = raw5212 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw5212; decide +kernel
    rw [ha]
    exact (canonical5212 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA681 + difference 5 4) (sourceB681 + difference 4 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA681 + difference 5 4) (sourceB681 + difference 4 5) sourceC681) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA681 sourceB681 sourceC681
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm681, Integer.Sparse.eval]
  linarith only [hs]

def sourceA682 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB682 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC682 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm682 : Integer.Sparse Master := [(Sum.inr 4587, 2), (Sum.inr 4589, 1), (Sum.inr 4595, 1), (Sum.inr 4599, 1), (Sum.inr 5072, 1), (Sum.inr 5074, 2), (Sum.inr 5098, 1), (Sum.inr 5184, 1), (Sum.inr 5186, 2), (Sum.inr 5196, 1), (Sum.inr 5254, 2), (Sum.inr 5258, 2), (Sum.inr 5260, 2), (Sum.inr 5265, 1), (Sum.inr 5271, 2), (Sum.inr 5286, 1), (Sum.inr 5289, 2), (Sum.inr 5405, 1), (Sum.inr 5406, 1), (Sum.inr 5429, 1), (Sum.inr 5434, 2)]

theorem sourceEq682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm682 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA682 + difference 0 1) (sourceB682 + difference 1 0) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA682 + difference 0 1) (sourceB682 + difference 1 0) sourceC682) = raw11544 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11544; decide +kernel
    rw [ha]
    exact (canonical11544 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA682 + difference 0 2) (sourceB682 + difference 2 0) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA682 + difference 0 2) (sourceB682 + difference 2 0) sourceC682) = raw11545 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11545; decide +kernel
    rw [ha]
    exact (canonical11545 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA682 + difference 0 3) (sourceB682 + difference 3 0) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA682 + difference 0 3) (sourceB682 + difference 3 0) sourceC682) = raw11546 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11546; decide +kernel
    rw [ha]
    exact (canonical11546 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA682 + difference 0 4) (sourceB682 + difference 4 0) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA682 + difference 0 4) (sourceB682 + difference 4 0) sourceC682) = raw11547 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11547; decide +kernel
    rw [ha]
    exact (canonical11547 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA682 + difference 0 5) (sourceB682 + difference 5 0) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA682 + difference 0 5) (sourceB682 + difference 5 0) sourceC682) = raw11548 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11548; decide +kernel
    rw [ha]
    exact (canonical11548 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA682 + difference 1 0) (sourceB682 + difference 0 1) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4595) := by
    have ha : (tripleCharges (sourceA682 + difference 1 0) (sourceB682 + difference 0 1) sourceC682) = raw11549 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11549; decide +kernel
    rw [ha]
    exact (canonical11549 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA682 + difference 1 2) (sourceB682 + difference 2 1) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5196) := by
    have ha : (tripleCharges (sourceA682 + difference 1 2) (sourceB682 + difference 2 1) sourceC682) = raw11550 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11550; decide +kernel
    rw [ha]
    exact (canonical11550 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA682 + difference 1 3) (sourceB682 + difference 3 1) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA682 + difference 1 3) (sourceB682 + difference 3 1) sourceC682) = raw11551 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11551; decide +kernel
    rw [ha]
    exact (canonical11551 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA682 + difference 1 4) (sourceB682 + difference 4 1) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA682 + difference 1 4) (sourceB682 + difference 4 1) sourceC682) = raw11552 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11552; decide +kernel
    rw [ha]
    exact (canonical11552 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA682 + difference 1 5) (sourceB682 + difference 5 1) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA682 + difference 1 5) (sourceB682 + difference 5 1) sourceC682) = raw11553 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11553; decide +kernel
    rw [ha]
    exact (canonical11553 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA682 + difference 2 0) (sourceB682 + difference 0 2) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA682 + difference 2 0) (sourceB682 + difference 0 2) sourceC682) = raw11554 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11554; decide +kernel
    rw [ha]
    exact (canonical11554 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA682 + difference 2 1) (sourceB682 + difference 1 2) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA682 + difference 2 1) (sourceB682 + difference 1 2) sourceC682) = raw11555 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11555; decide +kernel
    rw [ha]
    exact (canonical11555 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA682 + difference 2 3) (sourceB682 + difference 3 2) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA682 + difference 2 3) (sourceB682 + difference 3 2) sourceC682) = raw11556 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11556; decide +kernel
    rw [ha]
    exact (canonical11556 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA682 + difference 2 4) (sourceB682 + difference 4 2) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA682 + difference 2 4) (sourceB682 + difference 4 2) sourceC682) = raw11557 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11557; decide +kernel
    rw [ha]
    exact (canonical11557 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA682 + difference 2 5) (sourceB682 + difference 5 2) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA682 + difference 2 5) (sourceB682 + difference 5 2) sourceC682) = raw11558 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11558; decide +kernel
    rw [ha]
    exact (canonical11558 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA682 + difference 3 0) (sourceB682 + difference 0 3) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4587) := by
    have ha : (tripleCharges (sourceA682 + difference 3 0) (sourceB682 + difference 0 3) sourceC682) = raw11559 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11559; decide +kernel
    rw [ha]
    exact (canonical11559 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA682 + difference 3 1) (sourceB682 + difference 1 3) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA682 + difference 3 1) (sourceB682 + difference 1 3) sourceC682) = raw11560 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11560; decide +kernel
    rw [ha]
    exact (canonical11560 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA682 + difference 3 2) (sourceB682 + difference 2 3) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5186) := by
    have ha : (tripleCharges (sourceA682 + difference 3 2) (sourceB682 + difference 2 3) sourceC682) = raw11561 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11561; decide +kernel
    rw [ha]
    exact (canonical11561 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA682 + difference 3 4) (sourceB682 + difference 4 3) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA682 + difference 3 4) (sourceB682 + difference 4 3) sourceC682) = raw11562 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11562; decide +kernel
    rw [ha]
    exact (canonical11562 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA682 + difference 3 5) (sourceB682 + difference 5 3) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA682 + difference 3 5) (sourceB682 + difference 5 3) sourceC682) = raw11563 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11563; decide +kernel
    rw [ha]
    exact (canonical11563 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA682 + difference 4 0) (sourceB682 + difference 0 4) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4587) := by
    have ha : (tripleCharges (sourceA682 + difference 4 0) (sourceB682 + difference 0 4) sourceC682) = raw11564 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11564; decide +kernel
    rw [ha]
    exact (canonical11564 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA682 + difference 4 1) (sourceB682 + difference 1 4) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA682 + difference 4 1) (sourceB682 + difference 1 4) sourceC682) = raw11565 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11565; decide +kernel
    rw [ha]
    exact (canonical11565 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA682 + difference 4 2) (sourceB682 + difference 2 4) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5186) := by
    have ha : (tripleCharges (sourceA682 + difference 4 2) (sourceB682 + difference 2 4) sourceC682) = raw11566 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11566; decide +kernel
    rw [ha]
    exact (canonical11566 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA682 + difference 4 3) (sourceB682 + difference 3 4) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA682 + difference 4 3) (sourceB682 + difference 3 4) sourceC682) = raw11567 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11567; decide +kernel
    rw [ha]
    exact (canonical11567 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA682 + difference 4 5) (sourceB682 + difference 5 4) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA682 + difference 4 5) (sourceB682 + difference 5 4) sourceC682) = raw11568 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11568; decide +kernel
    rw [ha]
    exact (canonical11568 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA682 + difference 5 0) (sourceB682 + difference 0 5) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA682 + difference 5 0) (sourceB682 + difference 0 5) sourceC682) = raw11569 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11569; decide +kernel
    rw [ha]
    exact (canonical11569 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA682 + difference 5 1) (sourceB682 + difference 1 5) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA682 + difference 5 1) (sourceB682 + difference 1 5) sourceC682) = raw11570 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11570; decide +kernel
    rw [ha]
    exact (canonical11570 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA682 + difference 5 2) (sourceB682 + difference 2 5) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA682 + difference 5 2) (sourceB682 + difference 2 5) sourceC682) = raw11571 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11571; decide +kernel
    rw [ha]
    exact (canonical11571 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA682 + difference 5 3) (sourceB682 + difference 3 5) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA682 + difference 5 3) (sourceB682 + difference 3 5) sourceC682) = raw11572 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11572; decide +kernel
    rw [ha]
    exact (canonical11572 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA682 + difference 5 4) (sourceB682 + difference 4 5) sourceC682) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA682 + difference 5 4) (sourceB682 + difference 4 5) sourceC682) = raw11573 := by
      apply Matrix.ext; unfold tripleCharges sourceA682 sourceB682 sourceC682 difference raw11573; decide +kernel
    rw [ha]
    exact (canonical11573 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA682 sourceB682 sourceC682
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm682, Integer.Sparse.eval]
  linarith only [hs]

def sourceA683 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB683 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC683 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm683 : Integer.Sparse Master := [(Sum.inr 1210, 2), (Sum.inr 1216, 1), (Sum.inr 1228, 1), (Sum.inr 1260, 1), (Sum.inr 2860, 2), (Sum.inr 2864, 1), (Sum.inr 2874, 1), (Sum.inr 2984, 2), (Sum.inr 2988, 1), (Sum.inr 2996, 1), (Sum.inr 3016, 2), (Sum.inr 3023, 1), (Sum.inr 3037, 1), (Sum.inr 3086, 2), (Sum.inr 3089, 2), (Sum.inr 3097, 2), (Sum.inr 3109, 2), (Sum.inr 3801, 1), (Sum.inr 3954, 1), (Sum.inr 3977, 1), (Sum.inr 3982, 2)]

theorem sourceEq683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm683 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA683 + difference 0 1) (sourceB683 + difference 1 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA683 + difference 0 1) (sourceB683 + difference 1 0) sourceC683) = raw11574 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11574; decide +kernel
    rw [ha]
    exact (canonical11574 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA683 + difference 0 2) (sourceB683 + difference 2 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA683 + difference 0 2) (sourceB683 + difference 2 0) sourceC683) = raw11575 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11575; decide +kernel
    rw [ha]
    exact (canonical11575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA683 + difference 0 3) (sourceB683 + difference 3 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA683 + difference 0 3) (sourceB683 + difference 3 0) sourceC683) = raw11576 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11576; decide +kernel
    rw [ha]
    exact (canonical11576 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA683 + difference 0 4) (sourceB683 + difference 4 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA683 + difference 0 4) (sourceB683 + difference 4 0) sourceC683) = raw11577 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11577; decide +kernel
    rw [ha]
    exact (canonical11577 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA683 + difference 0 5) (sourceB683 + difference 5 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA683 + difference 0 5) (sourceB683 + difference 5 0) sourceC683) = raw11578 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11578; decide +kernel
    rw [ha]
    exact (canonical11578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA683 + difference 1 0) (sourceB683 + difference 0 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA683 + difference 1 0) (sourceB683 + difference 0 1) sourceC683) = raw11579 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11579; decide +kernel
    rw [ha]
    exact (canonical11579 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA683 + difference 1 2) (sourceB683 + difference 2 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2874) := by
    have ha : (tripleCharges (sourceA683 + difference 1 2) (sourceB683 + difference 2 1) sourceC683) = raw11580 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11580; decide +kernel
    rw [ha]
    exact (canonical11580 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA683 + difference 1 3) (sourceB683 + difference 3 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA683 + difference 1 3) (sourceB683 + difference 3 1) sourceC683) = raw11581 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11581; decide +kernel
    rw [ha]
    exact (canonical11581 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA683 + difference 1 4) (sourceB683 + difference 4 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA683 + difference 1 4) (sourceB683 + difference 4 1) sourceC683) = raw11582 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11582; decide +kernel
    rw [ha]
    exact (canonical11582 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA683 + difference 1 5) (sourceB683 + difference 5 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA683 + difference 1 5) (sourceB683 + difference 5 1) sourceC683) = raw11583 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11583; decide +kernel
    rw [ha]
    exact (canonical11583 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA683 + difference 2 0) (sourceB683 + difference 0 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA683 + difference 2 0) (sourceB683 + difference 0 2) sourceC683) = raw11584 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11584; decide +kernel
    rw [ha]
    exact (canonical11584 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA683 + difference 2 1) (sourceB683 + difference 1 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2996) := by
    have ha : (tripleCharges (sourceA683 + difference 2 1) (sourceB683 + difference 1 2) sourceC683) = raw11585 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11585; decide +kernel
    rw [ha]
    exact (canonical11585 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA683 + difference 2 3) (sourceB683 + difference 3 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA683 + difference 2 3) (sourceB683 + difference 3 2) sourceC683) = raw11586 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11586; decide +kernel
    rw [ha]
    exact (canonical11586 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA683 + difference 2 4) (sourceB683 + difference 4 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA683 + difference 2 4) (sourceB683 + difference 4 2) sourceC683) = raw11587 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11587; decide +kernel
    rw [ha]
    exact (canonical11587 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA683 + difference 2 5) (sourceB683 + difference 5 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA683 + difference 2 5) (sourceB683 + difference 5 2) sourceC683) = raw11588 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11588; decide +kernel
    rw [ha]
    exact (canonical11588 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA683 + difference 3 0) (sourceB683 + difference 0 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA683 + difference 3 0) (sourceB683 + difference 0 3) sourceC683) = raw11589 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11589; decide +kernel
    rw [ha]
    exact (canonical11589 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA683 + difference 3 1) (sourceB683 + difference 1 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA683 + difference 3 1) (sourceB683 + difference 1 3) sourceC683) = raw11590 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11590; decide +kernel
    rw [ha]
    exact (canonical11590 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA683 + difference 3 2) (sourceB683 + difference 2 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2860) := by
    have ha : (tripleCharges (sourceA683 + difference 3 2) (sourceB683 + difference 2 3) sourceC683) = raw11591 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11591; decide +kernel
    rw [ha]
    exact (canonical11591 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA683 + difference 3 4) (sourceB683 + difference 4 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA683 + difference 3 4) (sourceB683 + difference 4 3) sourceC683) = raw11592 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11592; decide +kernel
    rw [ha]
    exact (canonical11592 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA683 + difference 3 5) (sourceB683 + difference 5 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA683 + difference 3 5) (sourceB683 + difference 5 3) sourceC683) = raw11593 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11593; decide +kernel
    rw [ha]
    exact (canonical11593 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA683 + difference 4 0) (sourceB683 + difference 0 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA683 + difference 4 0) (sourceB683 + difference 0 4) sourceC683) = raw11594 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11594; decide +kernel
    rw [ha]
    exact (canonical11594 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA683 + difference 4 1) (sourceB683 + difference 1 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA683 + difference 4 1) (sourceB683 + difference 1 4) sourceC683) = raw11595 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11595; decide +kernel
    rw [ha]
    exact (canonical11595 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA683 + difference 4 2) (sourceB683 + difference 2 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2860) := by
    have ha : (tripleCharges (sourceA683 + difference 4 2) (sourceB683 + difference 2 4) sourceC683) = raw11596 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11596; decide +kernel
    rw [ha]
    exact (canonical11596 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA683 + difference 4 3) (sourceB683 + difference 3 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA683 + difference 4 3) (sourceB683 + difference 3 4) sourceC683) = raw11597 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11597; decide +kernel
    rw [ha]
    exact (canonical11597 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA683 + difference 4 5) (sourceB683 + difference 5 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA683 + difference 4 5) (sourceB683 + difference 5 4) sourceC683) = raw11598 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11598; decide +kernel
    rw [ha]
    exact (canonical11598 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA683 + difference 5 0) (sourceB683 + difference 0 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA683 + difference 5 0) (sourceB683 + difference 0 5) sourceC683) = raw11599 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11599; decide +kernel
    rw [ha]
    exact (canonical11599 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA683 + difference 5 1) (sourceB683 + difference 1 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2988) := by
    have ha : (tripleCharges (sourceA683 + difference 5 1) (sourceB683 + difference 1 5) sourceC683) = raw11600 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11600; decide +kernel
    rw [ha]
    exact (canonical11600 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA683 + difference 5 2) (sourceB683 + difference 2 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA683 + difference 5 2) (sourceB683 + difference 2 5) sourceC683) = raw11601 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11601; decide +kernel
    rw [ha]
    exact (canonical11601 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA683 + difference 5 3) (sourceB683 + difference 3 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA683 + difference 5 3) (sourceB683 + difference 3 5) sourceC683) = raw11602 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11602; decide +kernel
    rw [ha]
    exact (canonical11602 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA683 + difference 5 4) (sourceB683 + difference 4 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA683 + difference 5 4) (sourceB683 + difference 4 5) sourceC683) = raw11603 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11603; decide +kernel
    rw [ha]
    exact (canonical11603 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA683 sourceB683 sourceC683
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm683, Integer.Sparse.eval]
  linarith only [hs]

def sourceA684 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB684 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC684 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm684 : Integer.Sparse Master := [(Sum.inr 3285, 2), (Sum.inr 3286, 1), (Sum.inr 3288, 1), (Sum.inr 3289, 1), (Sum.inr 3459, 1), (Sum.inr 3460, 1), (Sum.inr 3463, 2), (Sum.inr 3524, 1), (Sum.inr 3526, 1), (Sum.inr 3527, 2), (Sum.inr 3528, 2), (Sum.inr 3533, 2), (Sum.inr 3534, 2), (Sum.inr 3540, 2), (Sum.inr 3566, 1), (Sum.inr 3567, 1), (Sum.inr 3572, 2), (Sum.inr 3800, 1), (Sum.inr 3846, 1), (Sum.inr 3847, 1), (Sum.inr 3852, 2)]

theorem sourceEq684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm684 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA684 + difference 0 1) (sourceB684 + difference 1 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA684 + difference 0 1) (sourceB684 + difference 1 0) sourceC684) = raw11604 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11604; decide +kernel
    rw [ha]
    exact (canonical11604 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA684 + difference 0 2) (sourceB684 + difference 2 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA684 + difference 0 2) (sourceB684 + difference 2 0) sourceC684) = raw11605 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11605; decide +kernel
    rw [ha]
    exact (canonical11605 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA684 + difference 0 3) (sourceB684 + difference 3 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA684 + difference 0 3) (sourceB684 + difference 3 0) sourceC684) = raw11606 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11606; decide +kernel
    rw [ha]
    exact (canonical11606 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA684 + difference 0 4) (sourceB684 + difference 4 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA684 + difference 0 4) (sourceB684 + difference 4 0) sourceC684) = raw11607 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11607; decide +kernel
    rw [ha]
    exact (canonical11607 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA684 + difference 0 5) (sourceB684 + difference 5 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA684 + difference 0 5) (sourceB684 + difference 5 0) sourceC684) = raw11608 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11608; decide +kernel
    rw [ha]
    exact (canonical11608 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA684 + difference 1 0) (sourceB684 + difference 0 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA684 + difference 1 0) (sourceB684 + difference 0 1) sourceC684) = raw11609 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11609; decide +kernel
    rw [ha]
    exact (canonical11609 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA684 + difference 1 2) (sourceB684 + difference 2 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3566) := by
    have ha : (tripleCharges (sourceA684 + difference 1 2) (sourceB684 + difference 2 1) sourceC684) = raw11610 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11610; decide +kernel
    rw [ha]
    exact (canonical11610 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA684 + difference 1 3) (sourceB684 + difference 3 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA684 + difference 1 3) (sourceB684 + difference 3 1) sourceC684) = raw11611 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11611; decide +kernel
    rw [ha]
    exact (canonical11611 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA684 + difference 1 4) (sourceB684 + difference 4 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA684 + difference 1 4) (sourceB684 + difference 4 1) sourceC684) = raw11612 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11612; decide +kernel
    rw [ha]
    exact (canonical11612 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA684 + difference 1 5) (sourceB684 + difference 5 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA684 + difference 1 5) (sourceB684 + difference 5 1) sourceC684) = raw11613 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11613; decide +kernel
    rw [ha]
    exact (canonical11613 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA684 + difference 2 0) (sourceB684 + difference 0 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA684 + difference 2 0) (sourceB684 + difference 0 2) sourceC684) = raw11614 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11614; decide +kernel
    rw [ha]
    exact (canonical11614 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA684 + difference 2 1) (sourceB684 + difference 1 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA684 + difference 2 1) (sourceB684 + difference 1 2) sourceC684) = raw11615 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11615; decide +kernel
    rw [ha]
    exact (canonical11615 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA684 + difference 2 3) (sourceB684 + difference 3 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA684 + difference 2 3) (sourceB684 + difference 3 2) sourceC684) = raw11616 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11616; decide +kernel
    rw [ha]
    exact (canonical11616 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA684 + difference 2 4) (sourceB684 + difference 4 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA684 + difference 2 4) (sourceB684 + difference 4 2) sourceC684) = raw11617 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11617; decide +kernel
    rw [ha]
    exact (canonical11617 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA684 + difference 2 5) (sourceB684 + difference 5 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA684 + difference 2 5) (sourceB684 + difference 5 2) sourceC684) = raw11618 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11618; decide +kernel
    rw [ha]
    exact (canonical11618 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA684 + difference 3 0) (sourceB684 + difference 0 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA684 + difference 3 0) (sourceB684 + difference 0 3) sourceC684) = raw11619 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11619; decide +kernel
    rw [ha]
    exact (canonical11619 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA684 + difference 3 1) (sourceB684 + difference 1 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA684 + difference 3 1) (sourceB684 + difference 1 3) sourceC684) = raw11620 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11620; decide +kernel
    rw [ha]
    exact (canonical11620 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA684 + difference 3 2) (sourceB684 + difference 2 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA684 + difference 3 2) (sourceB684 + difference 2 3) sourceC684) = raw11621 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11621; decide +kernel
    rw [ha]
    exact (canonical11621 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA684 + difference 3 4) (sourceB684 + difference 4 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA684 + difference 3 4) (sourceB684 + difference 4 3) sourceC684) = raw11622 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11622; decide +kernel
    rw [ha]
    exact (canonical11622 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA684 + difference 3 5) (sourceB684 + difference 5 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA684 + difference 3 5) (sourceB684 + difference 5 3) sourceC684) = raw11623 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11623; decide +kernel
    rw [ha]
    exact (canonical11623 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA684 + difference 4 0) (sourceB684 + difference 0 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA684 + difference 4 0) (sourceB684 + difference 0 4) sourceC684) = raw11624 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11624; decide +kernel
    rw [ha]
    exact (canonical11624 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA684 + difference 4 1) (sourceB684 + difference 1 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA684 + difference 4 1) (sourceB684 + difference 1 4) sourceC684) = raw11625 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11625; decide +kernel
    rw [ha]
    exact (canonical11625 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA684 + difference 4 2) (sourceB684 + difference 2 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA684 + difference 4 2) (sourceB684 + difference 2 4) sourceC684) = raw11626 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11626; decide +kernel
    rw [ha]
    exact (canonical11626 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA684 + difference 4 3) (sourceB684 + difference 3 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA684 + difference 4 3) (sourceB684 + difference 3 4) sourceC684) = raw11627 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11627; decide +kernel
    rw [ha]
    exact (canonical11627 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA684 + difference 4 5) (sourceB684 + difference 5 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA684 + difference 4 5) (sourceB684 + difference 5 4) sourceC684) = raw11628 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11628; decide +kernel
    rw [ha]
    exact (canonical11628 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA684 + difference 5 0) (sourceB684 + difference 0 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA684 + difference 5 0) (sourceB684 + difference 0 5) sourceC684) = raw11629 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11629; decide +kernel
    rw [ha]
    exact (canonical11629 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA684 + difference 5 1) (sourceB684 + difference 1 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA684 + difference 5 1) (sourceB684 + difference 1 5) sourceC684) = raw11630 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11630; decide +kernel
    rw [ha]
    exact (canonical11630 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA684 + difference 5 2) (sourceB684 + difference 2 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA684 + difference 5 2) (sourceB684 + difference 2 5) sourceC684) = raw11631 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11631; decide +kernel
    rw [ha]
    exact (canonical11631 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA684 + difference 5 3) (sourceB684 + difference 3 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA684 + difference 5 3) (sourceB684 + difference 3 5) sourceC684) = raw11632 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11632; decide +kernel
    rw [ha]
    exact (canonical11632 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA684 + difference 5 4) (sourceB684 + difference 4 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA684 + difference 5 4) (sourceB684 + difference 4 5) sourceC684) = raw11633 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11633; decide +kernel
    rw [ha]
    exact (canonical11633 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA684 sourceB684 sourceC684
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm684, Integer.Sparse.eval]
  linarith only [hs]

def sourceA685 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB685 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC685 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm685 : Integer.Sparse Master := [(Sum.inr 2720, 1), (Sum.inr 3805, 1), (Sum.inr 3812, 1), (Sum.inr 3874, 1), (Sum.inr 3903, 2), (Sum.inr 4092, -1)]

theorem sourceEq685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm685 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA685 + difference 0 0) (sourceB685 + difference 0 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA685 + difference 0 0) (sourceB685 + difference 0 0) sourceC685) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA685 + difference 0 1) (sourceB685 + difference 1 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA685 + difference 0 1) (sourceB685 + difference 1 0) sourceC685) = raw11635 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11635; decide +kernel
    rw [ha]
    exact (canonical11635 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA685 + difference 0 2) (sourceB685 + difference 2 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA685 + difference 0 2) (sourceB685 + difference 2 0) sourceC685) = raw11636 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11636; decide +kernel
    rw [ha]
    exact (canonical11636 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA685 + difference 0 3) (sourceB685 + difference 3 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA685 + difference 0 3) (sourceB685 + difference 3 0) sourceC685) = raw11637 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11637; decide +kernel
    rw [ha]
    exact (canonical11637 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA685 + difference 0 4) (sourceB685 + difference 4 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA685 + difference 0 4) (sourceB685 + difference 4 0) sourceC685) = raw11638 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11638; decide +kernel
    rw [ha]
    exact (canonical11638 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA685 + difference 0 5) (sourceB685 + difference 5 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA685 + difference 0 5) (sourceB685 + difference 5 0) sourceC685) = raw11639 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11639; decide +kernel
    rw [ha]
    exact (canonical11639 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA685 + sourceB685) sourceC685) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA685 + sourceB685) sourceC685) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA685 sourceB685 sourceC685 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA685 sourceB685 sourceC685
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm685, Integer.Sparse.eval]
  linarith only [hs]

def sourceA686 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB686 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC686 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm686 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1214, 2), (Sum.inr 1233, 1), (Sum.inr 1259, 1), (Sum.inr 2720, 1), (Sum.inr 4092, -1)]

theorem sourceEq686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm686 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA686 + difference 0 0) (sourceB686 + difference 0 0) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA686 + difference 0 0) (sourceB686 + difference 0 0) sourceC686) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA686 + difference 1 0) (sourceB686 + difference 0 1) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1259) := by
    have ha : (tripleCharges (sourceA686 + difference 1 0) (sourceB686 + difference 0 1) sourceC686) = raw11641 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11641; decide +kernel
    rw [ha]
    exact (canonical11641 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA686 + difference 2 0) (sourceB686 + difference 0 2) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA686 + difference 2 0) (sourceB686 + difference 0 2) sourceC686) = raw11642 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11642; decide +kernel
    rw [ha]
    exact (canonical11642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA686 + difference 3 0) (sourceB686 + difference 0 3) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1214) := by
    have ha : (tripleCharges (sourceA686 + difference 3 0) (sourceB686 + difference 0 3) sourceC686) = raw11643 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11643; decide +kernel
    rw [ha]
    exact (canonical11643 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA686 + difference 4 0) (sourceB686 + difference 0 4) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1214) := by
    have ha : (tripleCharges (sourceA686 + difference 4 0) (sourceB686 + difference 0 4) sourceC686) = raw11644 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11644; decide +kernel
    rw [ha]
    exact (canonical11644 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA686 + difference 5 0) (sourceB686 + difference 0 5) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA686 + difference 5 0) (sourceB686 + difference 0 5) sourceC686) = raw11645 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11645; decide +kernel
    rw [ha]
    exact (canonical11645 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA686 + sourceB686) sourceC686) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA686 + sourceB686) sourceC686) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA686 sourceB686 sourceC686 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA686 sourceB686 sourceC686
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm686, Integer.Sparse.eval]
  linarith only [hs]

def sourceA687 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB687 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC687 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm687 : Integer.Sparse Master := [(Sum.inr 1259, 1), (Sum.inr 2630, 1), (Sum.inr 2720, 1), (Sum.inr 2757, 1), (Sum.inr 2763, 2), (Sum.inr 4092, -1)]

theorem sourceEq687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm687 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA687 + difference 1 0) (sourceB687 + difference 0 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1259) := by
    have ha : (tripleCharges (sourceA687 + difference 1 0) (sourceB687 + difference 0 1) sourceC687) = raw11641 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11641; decide +kernel
    rw [ha]
    exact (canonical11641 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA687 + difference 1 1) (sourceB687 + difference 1 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA687 + difference 1 1) (sourceB687 + difference 1 1) sourceC687) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA687 + difference 1 2) (sourceB687 + difference 2 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2630) := by
    have ha : (tripleCharges (sourceA687 + difference 1 2) (sourceB687 + difference 2 1) sourceC687) = raw11646 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11646; decide +kernel
    rw [ha]
    exact (canonical11646 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA687 + difference 1 3) (sourceB687 + difference 3 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA687 + difference 1 3) (sourceB687 + difference 3 1) sourceC687) = raw11647 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11647; decide +kernel
    rw [ha]
    exact (canonical11647 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA687 + difference 1 4) (sourceB687 + difference 4 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA687 + difference 1 4) (sourceB687 + difference 4 1) sourceC687) = raw11648 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11648; decide +kernel
    rw [ha]
    exact (canonical11648 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA687 + difference 1 5) (sourceB687 + difference 5 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA687 + difference 1 5) (sourceB687 + difference 5 1) sourceC687) = raw11649 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11649; decide +kernel
    rw [ha]
    exact (canonical11649 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA687 + sourceB687) sourceC687) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA687 + sourceB687) sourceC687) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA687 sourceB687 sourceC687 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA687 sourceB687 sourceC687
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm687, Integer.Sparse.eval]
  linarith only [hs]

def sourceA688 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB688 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC688 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm688 : Integer.Sparse Master := [(Sum.inr 2479, 1), (Sum.inr 2481, 2), (Sum.inr 2508, 1), (Sum.inr 2720, 1), (Sum.inr 3805, 1), (Sum.inr 4092, -1)]

theorem sourceEq688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm688 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA688 + difference 0 1) (sourceB688 + difference 1 0) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA688 + difference 0 1) (sourceB688 + difference 1 0) sourceC688) = raw11635 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11635; decide +kernel
    rw [ha]
    exact (canonical11635 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA688 + difference 1 1) (sourceB688 + difference 1 1) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA688 + difference 1 1) (sourceB688 + difference 1 1) sourceC688) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA688 + difference 2 1) (sourceB688 + difference 1 2) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA688 + difference 2 1) (sourceB688 + difference 1 2) sourceC688) = raw11650 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11650; decide +kernel
    rw [ha]
    exact (canonical11650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA688 + difference 3 1) (sourceB688 + difference 1 3) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA688 + difference 3 1) (sourceB688 + difference 1 3) sourceC688) = raw11651 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11651; decide +kernel
    rw [ha]
    exact (canonical11651 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA688 + difference 4 1) (sourceB688 + difference 1 4) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA688 + difference 4 1) (sourceB688 + difference 1 4) sourceC688) = raw11652 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11652; decide +kernel
    rw [ha]
    exact (canonical11652 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA688 + difference 5 1) (sourceB688 + difference 1 5) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA688 + difference 5 1) (sourceB688 + difference 1 5) sourceC688) = raw11653 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11653; decide +kernel
    rw [ha]
    exact (canonical11653 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA688 + sourceB688) sourceC688) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA688 + sourceB688) sourceC688) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA688 sourceB688 sourceC688 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA688 sourceB688 sourceC688
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm688, Integer.Sparse.eval]
  linarith only [hs]

def sourceA689 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB689 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC689 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm689 : Integer.Sparse Master := [(Sum.inr 1233, 1), (Sum.inr 2508, 1), (Sum.inr 2720, 1), (Sum.inr 2730, 1), (Sum.inr 2739, 2), (Sum.inr 4092, -1)]

theorem sourceEq689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm689 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA689 + difference 2 0) (sourceB689 + difference 0 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA689 + difference 2 0) (sourceB689 + difference 0 2) sourceC689) = raw11642 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11642; decide +kernel
    rw [ha]
    exact (canonical11642 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA689 + difference 2 1) (sourceB689 + difference 1 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA689 + difference 2 1) (sourceB689 + difference 1 2) sourceC689) = raw11650 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11650; decide +kernel
    rw [ha]
    exact (canonical11650 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA689 + difference 2 2) (sourceB689 + difference 2 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA689 + difference 2 2) (sourceB689 + difference 2 2) sourceC689) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA689 + difference 2 3) (sourceB689 + difference 3 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA689 + difference 2 3) (sourceB689 + difference 3 2) sourceC689) = raw11654 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11654; decide +kernel
    rw [ha]
    exact (canonical11654 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA689 + difference 2 4) (sourceB689 + difference 4 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA689 + difference 2 4) (sourceB689 + difference 4 2) sourceC689) = raw11655 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11655; decide +kernel
    rw [ha]
    exact (canonical11655 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA689 + difference 2 5) (sourceB689 + difference 5 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA689 + difference 2 5) (sourceB689 + difference 5 2) sourceC689) = raw11656 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11656; decide +kernel
    rw [ha]
    exact (canonical11656 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA689 + sourceB689) sourceC689) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA689 + sourceB689) sourceC689) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA689 sourceB689 sourceC689 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA689 sourceB689 sourceC689
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm689, Integer.Sparse.eval]
  linarith only [hs]

def sourceA690 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB690 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC690 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm690 : Integer.Sparse Master := [(Sum.inr 2614, 1), (Sum.inr 2616, 2), (Sum.inr 2630, 1), (Sum.inr 2720, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

theorem sourceEq690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm690 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA690 + difference 0 2) (sourceB690 + difference 2 0) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA690 + difference 0 2) (sourceB690 + difference 2 0) sourceC690) = raw11636 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11636; decide +kernel
    rw [ha]
    exact (canonical11636 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA690 + difference 1 2) (sourceB690 + difference 2 1) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2630) := by
    have ha : (tripleCharges (sourceA690 + difference 1 2) (sourceB690 + difference 2 1) sourceC690) = raw11646 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11646; decide +kernel
    rw [ha]
    exact (canonical11646 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA690 + difference 2 2) (sourceB690 + difference 2 2) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA690 + difference 2 2) (sourceB690 + difference 2 2) sourceC690) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA690 + difference 3 2) (sourceB690 + difference 2 3) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA690 + difference 3 2) (sourceB690 + difference 2 3) sourceC690) = raw11657 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11657; decide +kernel
    rw [ha]
    exact (canonical11657 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA690 + difference 4 2) (sourceB690 + difference 2 4) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA690 + difference 4 2) (sourceB690 + difference 2 4) sourceC690) = raw11658 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11658; decide +kernel
    rw [ha]
    exact (canonical11658 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA690 + difference 5 2) (sourceB690 + difference 2 5) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA690 + difference 5 2) (sourceB690 + difference 2 5) sourceC690) = raw11659 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11659; decide +kernel
    rw [ha]
    exact (canonical11659 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA690 + sourceB690) sourceC690) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA690 + sourceB690) sourceC690) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA690 sourceB690 sourceC690 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA690 sourceB690 sourceC690
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm690, Integer.Sparse.eval]
  linarith only [hs]

def sourceA691 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB691 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC691 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm691 : Integer.Sparse Master := [(Sum.inr 4792, 1), (Sum.inr 4795, 1), (Sum.inr 4802, 2), (Sum.inr 4888, 1), (Sum.inr 5066, 1), (Sum.inr 5077, 2), (Sum.inr 5226, 2), (Sum.inr 5230, 1), (Sum.inr 5255, 4), (Sum.inr 5257, 3), (Sum.inr 5262, 2), (Sum.inr 5263, 1), (Sum.inr 5265, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 2), (Sum.inr 5289, 2), (Sum.inr 5290, 1), (Sum.inr 5292, 1), (Sum.inr 5306, 1)]

theorem sourceEq691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm691 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA691 + difference 0 1) (sourceB691 + difference 1 0) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA691 + difference 0 1) (sourceB691 + difference 1 0) sourceC691) = raw11660 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11660; decide +kernel
    rw [ha]
    exact (canonical11660 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA691 + difference 0 2) (sourceB691 + difference 2 0) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA691 + difference 0 2) (sourceB691 + difference 2 0) sourceC691) = raw11661 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11661; decide +kernel
    rw [ha]
    exact (canonical11661 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA691 + difference 0 3) (sourceB691 + difference 3 0) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA691 + difference 0 3) (sourceB691 + difference 3 0) sourceC691) = raw11662 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11662; decide +kernel
    rw [ha]
    exact (canonical11662 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA691 + difference 0 4) (sourceB691 + difference 4 0) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA691 + difference 0 4) (sourceB691 + difference 4 0) sourceC691) = raw11663 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11663; decide +kernel
    rw [ha]
    exact (canonical11663 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA691 + difference 0 5) (sourceB691 + difference 5 0) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA691 + difference 0 5) (sourceB691 + difference 5 0) sourceC691) = raw11664 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11664; decide +kernel
    rw [ha]
    exact (canonical11664 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA691 + difference 1 0) (sourceB691 + difference 0 1) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA691 + difference 1 0) (sourceB691 + difference 0 1) sourceC691) = raw11665 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11665; decide +kernel
    rw [ha]
    exact (canonical11665 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA691 + difference 1 2) (sourceB691 + difference 2 1) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA691 + difference 1 2) (sourceB691 + difference 2 1) sourceC691) = raw11666 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11666; decide +kernel
    rw [ha]
    exact (canonical11666 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA691 + difference 1 3) (sourceB691 + difference 3 1) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA691 + difference 1 3) (sourceB691 + difference 3 1) sourceC691) = raw11667 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11667; decide +kernel
    rw [ha]
    exact (canonical11667 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA691 + difference 1 4) (sourceB691 + difference 4 1) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA691 + difference 1 4) (sourceB691 + difference 4 1) sourceC691) = raw11668 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11668; decide +kernel
    rw [ha]
    exact (canonical11668 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA691 + difference 1 5) (sourceB691 + difference 5 1) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA691 + difference 1 5) (sourceB691 + difference 5 1) sourceC691) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA691 + difference 2 0) (sourceB691 + difference 0 2) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA691 + difference 2 0) (sourceB691 + difference 0 2) sourceC691) = raw11670 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11670; decide +kernel
    rw [ha]
    exact (canonical11670 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA691 + difference 2 1) (sourceB691 + difference 1 2) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5230) := by
    have ha : (tripleCharges (sourceA691 + difference 2 1) (sourceB691 + difference 1 2) sourceC691) = raw11671 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11671; decide +kernel
    rw [ha]
    exact (canonical11671 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA691 + difference 2 3) (sourceB691 + difference 3 2) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5262) := by
    have ha : (tripleCharges (sourceA691 + difference 2 3) (sourceB691 + difference 3 2) sourceC691) = raw11672 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11672; decide +kernel
    rw [ha]
    exact (canonical11672 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA691 + difference 2 4) (sourceB691 + difference 4 2) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5262) := by
    have ha : (tripleCharges (sourceA691 + difference 2 4) (sourceB691 + difference 4 2) sourceC691) = raw11673 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11673; decide +kernel
    rw [ha]
    exact (canonical11673 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA691 + difference 2 5) (sourceB691 + difference 5 2) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA691 + difference 2 5) (sourceB691 + difference 5 2) sourceC691) = raw11674 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11674; decide +kernel
    rw [ha]
    exact (canonical11674 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA691 + difference 3 0) (sourceB691 + difference 0 3) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA691 + difference 3 0) (sourceB691 + difference 0 3) sourceC691) = raw11675 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11675; decide +kernel
    rw [ha]
    exact (canonical11675 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA691 + difference 3 1) (sourceB691 + difference 1 3) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA691 + difference 3 1) (sourceB691 + difference 1 3) sourceC691) = raw11676 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11676; decide +kernel
    rw [ha]
    exact (canonical11676 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA691 + difference 3 2) (sourceB691 + difference 2 3) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA691 + difference 3 2) (sourceB691 + difference 2 3) sourceC691) = raw11677 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11677; decide +kernel
    rw [ha]
    exact (canonical11677 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA691 + difference 3 4) (sourceB691 + difference 4 3) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA691 + difference 3 4) (sourceB691 + difference 4 3) sourceC691) = raw11678 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11678; decide +kernel
    rw [ha]
    exact (canonical11678 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA691 + difference 3 5) (sourceB691 + difference 5 3) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA691 + difference 3 5) (sourceB691 + difference 5 3) sourceC691) = raw11679 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11679; decide +kernel
    rw [ha]
    exact (canonical11679 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA691 + difference 4 0) (sourceB691 + difference 0 4) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA691 + difference 4 0) (sourceB691 + difference 0 4) sourceC691) = raw11680 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11680; decide +kernel
    rw [ha]
    exact (canonical11680 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA691 + difference 4 1) (sourceB691 + difference 1 4) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA691 + difference 4 1) (sourceB691 + difference 1 4) sourceC691) = raw11681 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11681; decide +kernel
    rw [ha]
    exact (canonical11681 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA691 + difference 4 2) (sourceB691 + difference 2 4) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA691 + difference 4 2) (sourceB691 + difference 2 4) sourceC691) = raw11682 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11682; decide +kernel
    rw [ha]
    exact (canonical11682 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA691 + difference 4 3) (sourceB691 + difference 3 4) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA691 + difference 4 3) (sourceB691 + difference 3 4) sourceC691) = raw11683 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11683; decide +kernel
    rw [ha]
    exact (canonical11683 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA691 + difference 4 5) (sourceB691 + difference 5 4) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA691 + difference 4 5) (sourceB691 + difference 5 4) sourceC691) = raw11684 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11684; decide +kernel
    rw [ha]
    exact (canonical11684 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA691 + difference 5 0) (sourceB691 + difference 0 5) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA691 + difference 5 0) (sourceB691 + difference 0 5) sourceC691) = raw11685 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11685; decide +kernel
    rw [ha]
    exact (canonical11685 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA691 + difference 5 1) (sourceB691 + difference 1 5) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5066) := by
    have ha : (tripleCharges (sourceA691 + difference 5 1) (sourceB691 + difference 1 5) sourceC691) = raw11686 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11686; decide +kernel
    rw [ha]
    exact (canonical11686 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA691 + difference 5 2) (sourceB691 + difference 2 5) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA691 + difference 5 2) (sourceB691 + difference 2 5) sourceC691) = raw11687 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11687; decide +kernel
    rw [ha]
    exact (canonical11687 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA691 + difference 5 3) (sourceB691 + difference 3 5) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5077) := by
    have ha : (tripleCharges (sourceA691 + difference 5 3) (sourceB691 + difference 3 5) sourceC691) = raw11688 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11688; decide +kernel
    rw [ha]
    exact (canonical11688 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA691 + difference 5 4) (sourceB691 + difference 4 5) sourceC691) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5077) := by
    have ha : (tripleCharges (sourceA691 + difference 5 4) (sourceB691 + difference 4 5) sourceC691) = raw11689 := by
      apply Matrix.ext; unfold tripleCharges sourceA691 sourceB691 sourceC691 difference raw11689; decide +kernel
    rw [ha]
    exact (canonical11689 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA691 sourceB691 sourceC691
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm691, Integer.Sparse.eval]
  linarith only [hs]

def sourceA692 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB692 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC692 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm692 : Integer.Sparse Master := [(Sum.inr 2201, 1), (Sum.inr 2202, 2), (Sum.inr 2213, 1), (Sum.inr 2262, 1), (Sum.inr 2668, 1), (Sum.inr 2669, 2), (Sum.inr 2675, 1), (Sum.inr 2717, 2), (Sum.inr 2718, 2), (Sum.inr 2721, 2), (Sum.inr 2727, 2), (Sum.inr 2730, 1), (Sum.inr 2738, 1), (Sum.inr 2739, 2), (Sum.inr 2763, 2), (Sum.inr 2766, 1), (Sum.inr 2784, 1), (Sum.inr 3036, 1), (Sum.inr 3084, 2), (Sum.inr 3087, 1), (Sum.inr 3099, 1)]

theorem sourceEq692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm692 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA692 + difference 0 1) (sourceB692 + difference 1 0) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA692 + difference 0 1) (sourceB692 + difference 1 0) sourceC692) = raw11690 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11690; decide +kernel
    rw [ha]
    exact (canonical11690 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA692 + difference 0 2) (sourceB692 + difference 2 0) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA692 + difference 0 2) (sourceB692 + difference 2 0) sourceC692) = raw11691 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11691; decide +kernel
    rw [ha]
    exact (canonical11691 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA692 + difference 0 3) (sourceB692 + difference 3 0) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA692 + difference 0 3) (sourceB692 + difference 3 0) sourceC692) = raw11692 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11692; decide +kernel
    rw [ha]
    exact (canonical11692 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA692 + difference 0 4) (sourceB692 + difference 4 0) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA692 + difference 0 4) (sourceB692 + difference 4 0) sourceC692) = raw11693 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11693; decide +kernel
    rw [ha]
    exact (canonical11693 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA692 + difference 0 5) (sourceB692 + difference 5 0) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA692 + difference 0 5) (sourceB692 + difference 5 0) sourceC692) = raw11694 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11694; decide +kernel
    rw [ha]
    exact (canonical11694 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA692 + difference 1 0) (sourceB692 + difference 0 1) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA692 + difference 1 0) (sourceB692 + difference 0 1) sourceC692) = raw11695 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11695; decide +kernel
    rw [ha]
    exact (canonical11695 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA692 + difference 1 2) (sourceB692 + difference 2 1) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA692 + difference 1 2) (sourceB692 + difference 2 1) sourceC692) = raw11696 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11696; decide +kernel
    rw [ha]
    exact (canonical11696 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA692 + difference 1 3) (sourceB692 + difference 3 1) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA692 + difference 1 3) (sourceB692 + difference 3 1) sourceC692) = raw11697 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11697; decide +kernel
    rw [ha]
    exact (canonical11697 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA692 + difference 1 4) (sourceB692 + difference 4 1) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA692 + difference 1 4) (sourceB692 + difference 4 1) sourceC692) = raw11698 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11698; decide +kernel
    rw [ha]
    exact (canonical11698 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA692 + difference 1 5) (sourceB692 + difference 5 1) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA692 + difference 1 5) (sourceB692 + difference 5 1) sourceC692) = raw11699 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11699; decide +kernel
    rw [ha]
    exact (canonical11699 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA692 + difference 2 0) (sourceB692 + difference 0 2) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA692 + difference 2 0) (sourceB692 + difference 0 2) sourceC692) = raw11700 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11700; decide +kernel
    rw [ha]
    exact (canonical11700 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA692 + difference 2 1) (sourceB692 + difference 1 2) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2675) := by
    have ha : (tripleCharges (sourceA692 + difference 2 1) (sourceB692 + difference 1 2) sourceC692) = raw11701 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11701; decide +kernel
    rw [ha]
    exact (canonical11701 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA692 + difference 2 3) (sourceB692 + difference 3 2) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2727) := by
    have ha : (tripleCharges (sourceA692 + difference 2 3) (sourceB692 + difference 3 2) sourceC692) = raw11702 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11702; decide +kernel
    rw [ha]
    exact (canonical11702 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA692 + difference 2 4) (sourceB692 + difference 4 2) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2727) := by
    have ha : (tripleCharges (sourceA692 + difference 2 4) (sourceB692 + difference 4 2) sourceC692) = raw11703 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11703; decide +kernel
    rw [ha]
    exact (canonical11703 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA692 + difference 2 5) (sourceB692 + difference 5 2) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA692 + difference 2 5) (sourceB692 + difference 5 2) sourceC692) = raw11704 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11704; decide +kernel
    rw [ha]
    exact (canonical11704 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA692 + difference 3 0) (sourceB692 + difference 0 3) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA692 + difference 3 0) (sourceB692 + difference 0 3) sourceC692) = raw11705 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11705; decide +kernel
    rw [ha]
    exact (canonical11705 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA692 + difference 3 1) (sourceB692 + difference 1 3) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA692 + difference 3 1) (sourceB692 + difference 1 3) sourceC692) = raw11706 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11706; decide +kernel
    rw [ha]
    exact (canonical11706 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA692 + difference 3 2) (sourceB692 + difference 2 3) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA692 + difference 3 2) (sourceB692 + difference 2 3) sourceC692) = raw11707 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11707; decide +kernel
    rw [ha]
    exact (canonical11707 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA692 + difference 3 4) (sourceB692 + difference 4 3) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA692 + difference 3 4) (sourceB692 + difference 4 3) sourceC692) = raw11708 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11708; decide +kernel
    rw [ha]
    exact (canonical11708 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA692 + difference 3 5) (sourceB692 + difference 5 3) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA692 + difference 3 5) (sourceB692 + difference 5 3) sourceC692) = raw11709 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11709; decide +kernel
    rw [ha]
    exact (canonical11709 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA692 + difference 4 0) (sourceB692 + difference 0 4) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA692 + difference 4 0) (sourceB692 + difference 0 4) sourceC692) = raw11710 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11710; decide +kernel
    rw [ha]
    exact (canonical11710 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA692 + difference 4 1) (sourceB692 + difference 1 4) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA692 + difference 4 1) (sourceB692 + difference 1 4) sourceC692) = raw11711 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11711; decide +kernel
    rw [ha]
    exact (canonical11711 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA692 + difference 4 2) (sourceB692 + difference 2 4) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA692 + difference 4 2) (sourceB692 + difference 2 4) sourceC692) = raw11712 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11712; decide +kernel
    rw [ha]
    exact (canonical11712 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA692 + difference 4 3) (sourceB692 + difference 3 4) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA692 + difference 4 3) (sourceB692 + difference 3 4) sourceC692) = raw11713 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11713; decide +kernel
    rw [ha]
    exact (canonical11713 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA692 + difference 4 5) (sourceB692 + difference 5 4) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA692 + difference 4 5) (sourceB692 + difference 5 4) sourceC692) = raw11714 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11714; decide +kernel
    rw [ha]
    exact (canonical11714 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA692 + difference 5 0) (sourceB692 + difference 0 5) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA692 + difference 5 0) (sourceB692 + difference 0 5) sourceC692) = raw11715 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11715; decide +kernel
    rw [ha]
    exact (canonical11715 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA692 + difference 5 1) (sourceB692 + difference 1 5) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2668) := by
    have ha : (tripleCharges (sourceA692 + difference 5 1) (sourceB692 + difference 1 5) sourceC692) = raw11716 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11716; decide +kernel
    rw [ha]
    exact (canonical11716 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA692 + difference 5 2) (sourceB692 + difference 2 5) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA692 + difference 5 2) (sourceB692 + difference 2 5) sourceC692) = raw11717 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11717; decide +kernel
    rw [ha]
    exact (canonical11717 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA692 + difference 5 3) (sourceB692 + difference 3 5) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2717) := by
    have ha : (tripleCharges (sourceA692 + difference 5 3) (sourceB692 + difference 3 5) sourceC692) = raw11718 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11718; decide +kernel
    rw [ha]
    exact (canonical11718 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA692 + difference 5 4) (sourceB692 + difference 4 5) sourceC692) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2717) := by
    have ha : (tripleCharges (sourceA692 + difference 5 4) (sourceB692 + difference 4 5) sourceC692) = raw11719 := by
      apply Matrix.ext; unfold tripleCharges sourceA692 sourceB692 sourceC692 difference raw11719; decide +kernel
    rw [ha]
    exact (canonical11719 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA692 sourceB692 sourceC692
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm692, Integer.Sparse.eval]
  linarith only [hs]

def sourceA693 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB693 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC693 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm693 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 2472, 1), (Sum.inr 2484, 2), (Sum.inr 2718, 2), (Sum.inr 2721, 1), (Sum.inr 2728, 1), (Sum.inr 2754, 1), (Sum.inr 2764, 1), (Sum.inr 3034, 2), (Sum.inr 3037, 1), (Sum.inr 3041, 1), (Sum.inr 3084, 2), (Sum.inr 3087, 2), (Sum.inr 3091, 2), (Sum.inr 3097, 2), (Sum.inr 3100, 1), (Sum.inr 3109, 2), (Sum.inr 3120, 1), (Sum.inr 3199, 1), (Sum.inr 3204, 2), (Sum.inr 3227, 1)]

theorem sourceEq693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm693 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA693 + difference 0 1) (sourceB693 + difference 1 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA693 + difference 0 1) (sourceB693 + difference 1 0) sourceC693) = raw11720 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11720; decide +kernel
    rw [ha]
    exact (canonical11720 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA693 + difference 0 2) (sourceB693 + difference 2 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA693 + difference 0 2) (sourceB693 + difference 2 0) sourceC693) = raw11721 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11721; decide +kernel
    rw [ha]
    exact (canonical11721 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA693 + difference 0 3) (sourceB693 + difference 3 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA693 + difference 0 3) (sourceB693 + difference 3 0) sourceC693) = raw11722 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11722; decide +kernel
    rw [ha]
    exact (canonical11722 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA693 + difference 0 4) (sourceB693 + difference 4 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA693 + difference 0 4) (sourceB693 + difference 4 0) sourceC693) = raw11723 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11723; decide +kernel
    rw [ha]
    exact (canonical11723 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA693 + difference 0 5) (sourceB693 + difference 5 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA693 + difference 0 5) (sourceB693 + difference 5 0) sourceC693) = raw11724 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11724; decide +kernel
    rw [ha]
    exact (canonical11724 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA693 + difference 1 0) (sourceB693 + difference 0 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA693 + difference 1 0) (sourceB693 + difference 0 1) sourceC693) = raw11725 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11725; decide +kernel
    rw [ha]
    exact (canonical11725 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA693 + difference 1 2) (sourceB693 + difference 2 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA693 + difference 1 2) (sourceB693 + difference 2 1) sourceC693) = raw11726 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11726; decide +kernel
    rw [ha]
    exact (canonical11726 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA693 + difference 1 3) (sourceB693 + difference 3 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA693 + difference 1 3) (sourceB693 + difference 3 1) sourceC693) = raw11727 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11727; decide +kernel
    rw [ha]
    exact (canonical11727 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA693 + difference 1 4) (sourceB693 + difference 4 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA693 + difference 1 4) (sourceB693 + difference 4 1) sourceC693) = raw11728 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11728; decide +kernel
    rw [ha]
    exact (canonical11728 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA693 + difference 1 5) (sourceB693 + difference 5 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA693 + difference 1 5) (sourceB693 + difference 5 1) sourceC693) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA693 + difference 2 0) (sourceB693 + difference 0 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA693 + difference 2 0) (sourceB693 + difference 0 2) sourceC693) = raw11730 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11730; decide +kernel
    rw [ha]
    exact (canonical11730 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA693 + difference 2 1) (sourceB693 + difference 1 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3041) := by
    have ha : (tripleCharges (sourceA693 + difference 2 1) (sourceB693 + difference 1 2) sourceC693) = raw11731 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11731; decide +kernel
    rw [ha]
    exact (canonical11731 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA693 + difference 2 3) (sourceB693 + difference 3 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA693 + difference 2 3) (sourceB693 + difference 3 2) sourceC693) = raw11732 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11732; decide +kernel
    rw [ha]
    exact (canonical11732 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA693 + difference 2 4) (sourceB693 + difference 4 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA693 + difference 2 4) (sourceB693 + difference 4 2) sourceC693) = raw11733 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11733; decide +kernel
    rw [ha]
    exact (canonical11733 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA693 + difference 2 5) (sourceB693 + difference 5 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA693 + difference 2 5) (sourceB693 + difference 5 2) sourceC693) = raw11734 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11734; decide +kernel
    rw [ha]
    exact (canonical11734 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA693 + difference 3 0) (sourceB693 + difference 0 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA693 + difference 3 0) (sourceB693 + difference 0 3) sourceC693) = raw11735 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11735; decide +kernel
    rw [ha]
    exact (canonical11735 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA693 + difference 3 1) (sourceB693 + difference 1 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA693 + difference 3 1) (sourceB693 + difference 1 3) sourceC693) = raw11736 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11736; decide +kernel
    rw [ha]
    exact (canonical11736 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA693 + difference 3 2) (sourceB693 + difference 2 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA693 + difference 3 2) (sourceB693 + difference 2 3) sourceC693) = raw11737 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11737; decide +kernel
    rw [ha]
    exact (canonical11737 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA693 + difference 3 4) (sourceB693 + difference 4 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA693 + difference 3 4) (sourceB693 + difference 4 3) sourceC693) = raw11738 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11738; decide +kernel
    rw [ha]
    exact (canonical11738 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA693 + difference 3 5) (sourceB693 + difference 5 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA693 + difference 3 5) (sourceB693 + difference 5 3) sourceC693) = raw11739 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11739; decide +kernel
    rw [ha]
    exact (canonical11739 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA693 + difference 4 0) (sourceB693 + difference 0 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA693 + difference 4 0) (sourceB693 + difference 0 4) sourceC693) = raw11740 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11740; decide +kernel
    rw [ha]
    exact (canonical11740 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA693 + difference 4 1) (sourceB693 + difference 1 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA693 + difference 4 1) (sourceB693 + difference 1 4) sourceC693) = raw11741 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11741; decide +kernel
    rw [ha]
    exact (canonical11741 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA693 + difference 4 2) (sourceB693 + difference 2 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA693 + difference 4 2) (sourceB693 + difference 2 4) sourceC693) = raw11742 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11742; decide +kernel
    rw [ha]
    exact (canonical11742 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA693 + difference 4 3) (sourceB693 + difference 3 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA693 + difference 4 3) (sourceB693 + difference 3 4) sourceC693) = raw11743 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11743; decide +kernel
    rw [ha]
    exact (canonical11743 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA693 + difference 4 5) (sourceB693 + difference 5 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA693 + difference 4 5) (sourceB693 + difference 5 4) sourceC693) = raw11744 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11744; decide +kernel
    rw [ha]
    exact (canonical11744 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA693 + difference 5 0) (sourceB693 + difference 0 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA693 + difference 5 0) (sourceB693 + difference 0 5) sourceC693) = raw11745 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11745; decide +kernel
    rw [ha]
    exact (canonical11745 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA693 + difference 5 1) (sourceB693 + difference 1 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2472) := by
    have ha : (tripleCharges (sourceA693 + difference 5 1) (sourceB693 + difference 1 5) sourceC693) = raw11746 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11746; decide +kernel
    rw [ha]
    exact (canonical11746 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA693 + difference 5 2) (sourceB693 + difference 2 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA693 + difference 5 2) (sourceB693 + difference 2 5) sourceC693) = raw11747 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11747; decide +kernel
    rw [ha]
    exact (canonical11747 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA693 + difference 5 3) (sourceB693 + difference 3 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2484) := by
    have ha : (tripleCharges (sourceA693 + difference 5 3) (sourceB693 + difference 3 5) sourceC693) = raw11748 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11748; decide +kernel
    rw [ha]
    exact (canonical11748 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA693 + difference 5 4) (sourceB693 + difference 4 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2484) := by
    have ha : (tripleCharges (sourceA693 + difference 5 4) (sourceB693 + difference 4 5) sourceC693) = raw11749 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11749; decide +kernel
    rw [ha]
    exact (canonical11749 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA693 sourceB693 sourceC693
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm693, Integer.Sparse.eval]
  linarith only [hs]

def sourceA694 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB694 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC694 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm694 : Integer.Sparse Master := [(Sum.inr 3503, 2), (Sum.inr 3505, 1), (Sum.inr 3525, 1), (Sum.inr 3532, 1), (Sum.inr 3581, 1), (Sum.inr 4083, -1)]

theorem sourceEq694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm694 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA694 + difference 0 0) (sourceB694 + difference 0 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA694 + difference 0 0) (sourceB694 + difference 0 0) sourceC694) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA694 + difference 0 1) (sourceB694 + difference 1 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA694 + difference 0 1) (sourceB694 + difference 1 0) sourceC694) = raw11751 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11751; decide +kernel
    rw [ha]
    exact (canonical11751 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA694 + difference 0 2) (sourceB694 + difference 2 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA694 + difference 0 2) (sourceB694 + difference 2 0) sourceC694) = raw11752 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11752; decide +kernel
    rw [ha]
    exact (canonical11752 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA694 + difference 0 3) (sourceB694 + difference 3 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA694 + difference 0 3) (sourceB694 + difference 3 0) sourceC694) = raw11753 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11753; decide +kernel
    rw [ha]
    exact (canonical11753 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA694 + difference 0 4) (sourceB694 + difference 4 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA694 + difference 0 4) (sourceB694 + difference 4 0) sourceC694) = raw11754 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11754; decide +kernel
    rw [ha]
    exact (canonical11754 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA694 + difference 0 5) (sourceB694 + difference 5 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA694 + difference 0 5) (sourceB694 + difference 5 0) sourceC694) = raw11755 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11755; decide +kernel
    rw [ha]
    exact (canonical11755 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA694 + sourceB694) sourceC694) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA694 + sourceB694) sourceC694) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA694 sourceB694 sourceC694 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA694 sourceB694 sourceC694
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm694, Integer.Sparse.eval]
  linarith only [hs]

def sourceA695 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB695 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC695 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm695 : Integer.Sparse Master := [(Sum.inr 2980, 1), (Sum.inr 3373, 1), (Sum.inr 3376, 2), (Sum.inr 3505, 1), (Sum.inr 3525, 1), (Sum.inr 4083, -1)]

theorem sourceEq695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm695 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA695 + difference 0 1) (sourceB695 + difference 1 0) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA695 + difference 0 1) (sourceB695 + difference 1 0) sourceC695) = raw11751 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11751; decide +kernel
    rw [ha]
    exact (canonical11751 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA695 + difference 1 1) (sourceB695 + difference 1 1) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA695 + difference 1 1) (sourceB695 + difference 1 1) sourceC695) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA695 + difference 2 1) (sourceB695 + difference 1 2) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3373) := by
    have ha : (tripleCharges (sourceA695 + difference 2 1) (sourceB695 + difference 1 2) sourceC695) = raw11757 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11757; decide +kernel
    rw [ha]
    exact (canonical11757 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA695 + difference 3 1) (sourceB695 + difference 1 3) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA695 + difference 3 1) (sourceB695 + difference 1 3) sourceC695) = raw11758 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11758; decide +kernel
    rw [ha]
    exact (canonical11758 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA695 + difference 4 1) (sourceB695 + difference 1 4) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA695 + difference 4 1) (sourceB695 + difference 1 4) sourceC695) = raw11759 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11759; decide +kernel
    rw [ha]
    exact (canonical11759 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA695 + difference 5 1) (sourceB695 + difference 1 5) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2980) := by
    have ha : (tripleCharges (sourceA695 + difference 5 1) (sourceB695 + difference 1 5) sourceC695) = raw11760 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11760; decide +kernel
    rw [ha]
    exact (canonical11760 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA695 + sourceB695) sourceC695) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA695 + sourceB695) sourceC695) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA695 sourceB695 sourceC695 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA695 sourceB695 sourceC695
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm695, Integer.Sparse.eval]
  linarith only [hs]

def sourceA696 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB696 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC696 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm696 : Integer.Sparse Master := [(Sum.inr 2012, 1), (Sum.inr 3373, 1), (Sum.inr 3500, 2), (Sum.inr 3525, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

theorem sourceEq696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm696 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA696 + difference 2 0) (sourceB696 + difference 0 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA696 + difference 2 0) (sourceB696 + difference 0 2) sourceC696) = raw11761 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11761; decide +kernel
    rw [ha]
    exact (canonical11761 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA696 + difference 2 1) (sourceB696 + difference 1 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3373) := by
    have ha : (tripleCharges (sourceA696 + difference 2 1) (sourceB696 + difference 1 2) sourceC696) = raw11757 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11757; decide +kernel
    rw [ha]
    exact (canonical11757 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA696 + difference 2 2) (sourceB696 + difference 2 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA696 + difference 2 2) (sourceB696 + difference 2 2) sourceC696) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA696 + difference 2 3) (sourceB696 + difference 3 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA696 + difference 2 3) (sourceB696 + difference 3 2) sourceC696) = raw11762 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11762; decide +kernel
    rw [ha]
    exact (canonical11762 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA696 + difference 2 4) (sourceB696 + difference 4 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA696 + difference 2 4) (sourceB696 + difference 4 2) sourceC696) = raw11763 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11763; decide +kernel
    rw [ha]
    exact (canonical11763 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA696 + difference 2 5) (sourceB696 + difference 5 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA696 + difference 2 5) (sourceB696 + difference 5 2) sourceC696) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA696 + sourceB696) sourceC696) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA696 + sourceB696) sourceC696) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA696 sourceB696 sourceC696 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA696 sourceB696 sourceC696
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm696, Integer.Sparse.eval]
  linarith only [hs]

def sourceA697 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB697 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC697 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm697 : Integer.Sparse Master := [(Sum.inr 2020, 1), (Sum.inr 3376, 1), (Sum.inr 3503, 1), (Sum.inr 3525, 1), (Sum.inr 3532, 1), (Sum.inr 3534, 1), (Sum.inr 4083, -1)]

theorem sourceEq697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm697 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA697 + difference 3 0) (sourceB697 + difference 0 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA697 + difference 3 0) (sourceB697 + difference 0 3) sourceC697) = raw11765 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11765; decide +kernel
    rw [ha]
    exact (canonical11765 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA697 + difference 3 1) (sourceB697 + difference 1 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA697 + difference 3 1) (sourceB697 + difference 1 3) sourceC697) = raw11758 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11758; decide +kernel
    rw [ha]
    exact (canonical11758 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA697 + difference 3 2) (sourceB697 + difference 2 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA697 + difference 3 2) (sourceB697 + difference 2 3) sourceC697) = raw11766 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11766; decide +kernel
    rw [ha]
    exact (canonical11766 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA697 + difference 3 3) (sourceB697 + difference 3 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA697 + difference 3 3) (sourceB697 + difference 3 3) sourceC697) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA697 + difference 3 4) (sourceB697 + difference 4 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA697 + difference 3 4) (sourceB697 + difference 4 3) sourceC697) = raw11767 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11767; decide +kernel
    rw [ha]
    exact (canonical11767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA697 + difference 3 5) (sourceB697 + difference 5 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA697 + difference 3 5) (sourceB697 + difference 5 3) sourceC697) = raw11768 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11768; decide +kernel
    rw [ha]
    exact (canonical11768 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA697 + sourceB697) sourceC697) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA697 + sourceB697) sourceC697) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA697 sourceB697 sourceC697 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA697 sourceB697 sourceC697
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm697, Integer.Sparse.eval]
  linarith only [hs]

def sourceA698 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB698 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC698 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm698 : Integer.Sparse Master := [(Sum.inr 2983, 1), (Sum.inr 3500, 1), (Sum.inr 3503, 2), (Sum.inr 3525, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

theorem sourceEq698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm698 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA698 + difference 0 3) (sourceB698 + difference 3 0) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA698 + difference 0 3) (sourceB698 + difference 3 0) sourceC698) = raw11753 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11753; decide +kernel
    rw [ha]
    exact (canonical11753 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA698 + difference 1 3) (sourceB698 + difference 3 1) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA698 + difference 1 3) (sourceB698 + difference 3 1) sourceC698) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA698 + difference 2 3) (sourceB698 + difference 3 2) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA698 + difference 2 3) (sourceB698 + difference 3 2) sourceC698) = raw11762 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11762; decide +kernel
    rw [ha]
    exact (canonical11762 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA698 + difference 3 3) (sourceB698 + difference 3 3) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA698 + difference 3 3) (sourceB698 + difference 3 3) sourceC698) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA698 + difference 4 3) (sourceB698 + difference 3 4) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA698 + difference 4 3) (sourceB698 + difference 3 4) sourceC698) = raw11770 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11770; decide +kernel
    rw [ha]
    exact (canonical11770 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA698 + difference 5 3) (sourceB698 + difference 3 5) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA698 + difference 5 3) (sourceB698 + difference 3 5) sourceC698) = raw11771 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11771; decide +kernel
    rw [ha]
    exact (canonical11771 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA698 + sourceB698) sourceC698) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA698 + sourceB698) sourceC698) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA698 sourceB698 sourceC698 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA698 sourceB698 sourceC698
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm698, Integer.Sparse.eval]
  linarith only [hs]

def sourceA699 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB699 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC699 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceForm699 : Integer.Sparse Master := [(Sum.inr 4561, 2), (Sum.inr 4563, 1), (Sum.inr 4566, 1), (Sum.inr 4599, 1), (Sum.inr 5085, 1), (Sum.inr 5086, 2), (Sum.inr 5098, 1), (Sum.inr 5208, 2), (Sum.inr 5209, 2), (Sum.inr 5254, 2), (Sum.inr 5256, 1), (Sum.inr 5265, 1), (Sum.inr 5266, 2), (Sum.inr 5267, 2), (Sum.inr 5271, 2), (Sum.inr 5286, 1), (Sum.inr 5299, 2), (Sum.inr 5406, 2), (Sum.inr 5435, 2)]

theorem sourceEq699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm699 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA699 + difference 0 1) (sourceB699 + difference 1 0) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA699 + difference 0 1) (sourceB699 + difference 1 0) sourceC699) = raw11772 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11772; decide +kernel
    rw [ha]
    exact (canonical11772 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA699 + difference 0 2) (sourceB699 + difference 2 0) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA699 + difference 0 2) (sourceB699 + difference 2 0) sourceC699) = raw11773 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11773; decide +kernel
    rw [ha]
    exact (canonical11773 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA699 + difference 0 3) (sourceB699 + difference 3 0) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA699 + difference 0 3) (sourceB699 + difference 3 0) sourceC699) = raw11774 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11774; decide +kernel
    rw [ha]
    exact (canonical11774 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA699 + difference 0 4) (sourceB699 + difference 4 0) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA699 + difference 0 4) (sourceB699 + difference 4 0) sourceC699) = raw11775 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11775; decide +kernel
    rw [ha]
    exact (canonical11775 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA699 + difference 0 5) (sourceB699 + difference 5 0) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA699 + difference 0 5) (sourceB699 + difference 5 0) sourceC699) = raw11776 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11776; decide +kernel
    rw [ha]
    exact (canonical11776 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA699 + difference 1 0) (sourceB699 + difference 0 1) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4566) := by
    have ha : (tripleCharges (sourceA699 + difference 1 0) (sourceB699 + difference 0 1) sourceC699) = raw11777 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11777; decide +kernel
    rw [ha]
    exact (canonical11777 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA699 + difference 1 2) (sourceB699 + difference 2 1) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5208) := by
    have ha : (tripleCharges (sourceA699 + difference 1 2) (sourceB699 + difference 2 1) sourceC699) = raw11778 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11778; decide +kernel
    rw [ha]
    exact (canonical11778 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA699 + difference 1 3) (sourceB699 + difference 3 1) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA699 + difference 1 3) (sourceB699 + difference 3 1) sourceC699) = raw11779 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11779; decide +kernel
    rw [ha]
    exact (canonical11779 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA699 + difference 1 4) (sourceB699 + difference 4 1) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA699 + difference 1 4) (sourceB699 + difference 4 1) sourceC699) = raw11780 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11780; decide +kernel
    rw [ha]
    exact (canonical11780 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA699 + difference 1 5) (sourceB699 + difference 5 1) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA699 + difference 1 5) (sourceB699 + difference 5 1) sourceC699) = raw11781 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11781; decide +kernel
    rw [ha]
    exact (canonical11781 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA699 + difference 2 0) (sourceB699 + difference 0 2) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA699 + difference 2 0) (sourceB699 + difference 0 2) sourceC699) = raw11782 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11782; decide +kernel
    rw [ha]
    exact (canonical11782 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA699 + difference 2 1) (sourceB699 + difference 1 2) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA699 + difference 2 1) (sourceB699 + difference 1 2) sourceC699) = raw11783 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11783; decide +kernel
    rw [ha]
    exact (canonical11783 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA699 + difference 2 3) (sourceB699 + difference 3 2) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA699 + difference 2 3) (sourceB699 + difference 3 2) sourceC699) = raw11784 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11784; decide +kernel
    rw [ha]
    exact (canonical11784 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA699 + difference 2 4) (sourceB699 + difference 4 2) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA699 + difference 2 4) (sourceB699 + difference 4 2) sourceC699) = raw11785 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11785; decide +kernel
    rw [ha]
    exact (canonical11785 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA699 + difference 2 5) (sourceB699 + difference 5 2) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA699 + difference 2 5) (sourceB699 + difference 5 2) sourceC699) = raw11786 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11786; decide +kernel
    rw [ha]
    exact (canonical11786 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA699 + difference 3 0) (sourceB699 + difference 0 3) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4561) := by
    have ha : (tripleCharges (sourceA699 + difference 3 0) (sourceB699 + difference 0 3) sourceC699) = raw11787 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11787; decide +kernel
    rw [ha]
    exact (canonical11787 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA699 + difference 3 1) (sourceB699 + difference 1 3) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA699 + difference 3 1) (sourceB699 + difference 1 3) sourceC699) = raw11788 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11788; decide +kernel
    rw [ha]
    exact (canonical11788 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA699 + difference 3 2) (sourceB699 + difference 2 3) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5209) := by
    have ha : (tripleCharges (sourceA699 + difference 3 2) (sourceB699 + difference 2 3) sourceC699) = raw11789 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11789; decide +kernel
    rw [ha]
    exact (canonical11789 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA699 + difference 3 4) (sourceB699 + difference 4 3) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA699 + difference 3 4) (sourceB699 + difference 4 3) sourceC699) = raw11790 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11790; decide +kernel
    rw [ha]
    exact (canonical11790 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA699 + difference 3 5) (sourceB699 + difference 5 3) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA699 + difference 3 5) (sourceB699 + difference 5 3) sourceC699) = raw11791 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11791; decide +kernel
    rw [ha]
    exact (canonical11791 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA699 + difference 4 0) (sourceB699 + difference 0 4) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4561) := by
    have ha : (tripleCharges (sourceA699 + difference 4 0) (sourceB699 + difference 0 4) sourceC699) = raw11792 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11792; decide +kernel
    rw [ha]
    exact (canonical11792 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA699 + difference 4 1) (sourceB699 + difference 1 4) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA699 + difference 4 1) (sourceB699 + difference 1 4) sourceC699) = raw11793 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11793; decide +kernel
    rw [ha]
    exact (canonical11793 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA699 + difference 4 2) (sourceB699 + difference 2 4) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5209) := by
    have ha : (tripleCharges (sourceA699 + difference 4 2) (sourceB699 + difference 2 4) sourceC699) = raw11794 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11794; decide +kernel
    rw [ha]
    exact (canonical11794 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA699 + difference 4 3) (sourceB699 + difference 3 4) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA699 + difference 4 3) (sourceB699 + difference 3 4) sourceC699) = raw11795 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11795; decide +kernel
    rw [ha]
    exact (canonical11795 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA699 + difference 4 5) (sourceB699 + difference 5 4) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA699 + difference 4 5) (sourceB699 + difference 5 4) sourceC699) = raw11796 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11796; decide +kernel
    rw [ha]
    exact (canonical11796 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA699 + difference 5 0) (sourceB699 + difference 0 5) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4563) := by
    have ha : (tripleCharges (sourceA699 + difference 5 0) (sourceB699 + difference 0 5) sourceC699) = raw11797 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11797; decide +kernel
    rw [ha]
    exact (canonical11797 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA699 + difference 5 1) (sourceB699 + difference 1 5) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA699 + difference 5 1) (sourceB699 + difference 1 5) sourceC699) = raw11798 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11798; decide +kernel
    rw [ha]
    exact (canonical11798 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA699 + difference 5 2) (sourceB699 + difference 2 5) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5208) := by
    have ha : (tripleCharges (sourceA699 + difference 5 2) (sourceB699 + difference 2 5) sourceC699) = raw11799 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11799; decide +kernel
    rw [ha]
    exact (canonical11799 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA699 + difference 5 3) (sourceB699 + difference 3 5) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA699 + difference 5 3) (sourceB699 + difference 3 5) sourceC699) = raw11800 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11800; decide +kernel
    rw [ha]
    exact (canonical11800 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA699 + difference 5 4) (sourceB699 + difference 4 5) sourceC699) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA699 + difference 5 4) (sourceB699 + difference 4 5) sourceC699) = raw11801 := by
      apply Matrix.ext; unfold tripleCharges sourceA699 sourceB699 sourceC699 difference raw11801; decide +kernel
    rw [ha]
    exact (canonical11801 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA699 sourceB699 sourceC699
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm699, Integer.Sparse.eval]
  linarith only [hs]

def sourceA700 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB700 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC700 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceForm700 : Integer.Sparse Master := [(Sum.inr 1178, 2), (Sum.inr 1180, 1), (Sum.inr 1183, 1), (Sum.inr 1260, 1), (Sum.inr 2833, 2), (Sum.inr 2834, 1), (Sum.inr 2836, 1), (Sum.inr 2974, 2), (Sum.inr 2976, 1), (Sum.inr 2996, 1), (Sum.inr 3016, 2), (Sum.inr 3023, 1), (Sum.inr 3038, 2), (Sum.inr 3039, 2), (Sum.inr 3051, 2), (Sum.inr 3085, 1), (Sum.inr 3109, 2), (Sum.inr 3526, 1), (Sum.inr 3801, 1), (Sum.inr 3847, 1), (Sum.inr 3853, 2)]

theorem sourceEq700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm700 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA700 + difference 0 1) (sourceB700 + difference 1 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA700 + difference 0 1) (sourceB700 + difference 1 0) sourceC700) = raw11802 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11802; decide +kernel
    rw [ha]
    exact (canonical11802 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA700 + difference 0 2) (sourceB700 + difference 2 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA700 + difference 0 2) (sourceB700 + difference 2 0) sourceC700) = raw11803 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11803; decide +kernel
    rw [ha]
    exact (canonical11803 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA700 + difference 0 3) (sourceB700 + difference 3 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA700 + difference 0 3) (sourceB700 + difference 3 0) sourceC700) = raw11804 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11804; decide +kernel
    rw [ha]
    exact (canonical11804 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA700 + difference 0 4) (sourceB700 + difference 4 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA700 + difference 0 4) (sourceB700 + difference 4 0) sourceC700) = raw11805 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11805; decide +kernel
    rw [ha]
    exact (canonical11805 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA700 + difference 0 5) (sourceB700 + difference 5 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA700 + difference 0 5) (sourceB700 + difference 5 0) sourceC700) = raw11806 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11806; decide +kernel
    rw [ha]
    exact (canonical11806 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA700 + difference 1 0) (sourceB700 + difference 0 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1183) := by
    have ha : (tripleCharges (sourceA700 + difference 1 0) (sourceB700 + difference 0 1) sourceC700) = raw11807 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11807; decide +kernel
    rw [ha]
    exact (canonical11807 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA700 + difference 1 2) (sourceB700 + difference 2 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2836) := by
    have ha : (tripleCharges (sourceA700 + difference 1 2) (sourceB700 + difference 2 1) sourceC700) = raw11808 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11808; decide +kernel
    rw [ha]
    exact (canonical11808 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA700 + difference 1 3) (sourceB700 + difference 3 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA700 + difference 1 3) (sourceB700 + difference 3 1) sourceC700) = raw11809 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11809; decide +kernel
    rw [ha]
    exact (canonical11809 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA700 + difference 1 4) (sourceB700 + difference 4 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA700 + difference 1 4) (sourceB700 + difference 4 1) sourceC700) = raw11810 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11810; decide +kernel
    rw [ha]
    exact (canonical11810 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA700 + difference 1 5) (sourceB700 + difference 5 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA700 + difference 1 5) (sourceB700 + difference 5 1) sourceC700) = raw11811 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11811; decide +kernel
    rw [ha]
    exact (canonical11811 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA700 + difference 2 0) (sourceB700 + difference 0 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA700 + difference 2 0) (sourceB700 + difference 0 2) sourceC700) = raw11812 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11812; decide +kernel
    rw [ha]
    exact (canonical11812 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA700 + difference 2 1) (sourceB700 + difference 1 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2996) := by
    have ha : (tripleCharges (sourceA700 + difference 2 1) (sourceB700 + difference 1 2) sourceC700) = raw11813 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11813; decide +kernel
    rw [ha]
    exact (canonical11813 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA700 + difference 2 3) (sourceB700 + difference 3 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA700 + difference 2 3) (sourceB700 + difference 3 2) sourceC700) = raw11814 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11814; decide +kernel
    rw [ha]
    exact (canonical11814 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA700 + difference 2 4) (sourceB700 + difference 4 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA700 + difference 2 4) (sourceB700 + difference 4 2) sourceC700) = raw11815 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11815; decide +kernel
    rw [ha]
    exact (canonical11815 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA700 + difference 2 5) (sourceB700 + difference 5 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA700 + difference 2 5) (sourceB700 + difference 5 2) sourceC700) = raw11816 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11816; decide +kernel
    rw [ha]
    exact (canonical11816 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA700 + difference 3 0) (sourceB700 + difference 0 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1178) := by
    have ha : (tripleCharges (sourceA700 + difference 3 0) (sourceB700 + difference 0 3) sourceC700) = raw11817 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11817; decide +kernel
    rw [ha]
    exact (canonical11817 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA700 + difference 3 1) (sourceB700 + difference 1 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA700 + difference 3 1) (sourceB700 + difference 1 3) sourceC700) = raw11818 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11818; decide +kernel
    rw [ha]
    exact (canonical11818 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA700 + difference 3 2) (sourceB700 + difference 2 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA700 + difference 3 2) (sourceB700 + difference 2 3) sourceC700) = raw11819 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11819; decide +kernel
    rw [ha]
    exact (canonical11819 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA700 + difference 3 4) (sourceB700 + difference 4 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA700 + difference 3 4) (sourceB700 + difference 4 3) sourceC700) = raw11820 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11820; decide +kernel
    rw [ha]
    exact (canonical11820 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA700 + difference 3 5) (sourceB700 + difference 5 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA700 + difference 3 5) (sourceB700 + difference 5 3) sourceC700) = raw11821 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11821; decide +kernel
    rw [ha]
    exact (canonical11821 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA700 + difference 4 0) (sourceB700 + difference 0 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1178) := by
    have ha : (tripleCharges (sourceA700 + difference 4 0) (sourceB700 + difference 0 4) sourceC700) = raw11822 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11822; decide +kernel
    rw [ha]
    exact (canonical11822 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA700 + difference 4 1) (sourceB700 + difference 1 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA700 + difference 4 1) (sourceB700 + difference 1 4) sourceC700) = raw11823 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11823; decide +kernel
    rw [ha]
    exact (canonical11823 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA700 + difference 4 2) (sourceB700 + difference 2 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA700 + difference 4 2) (sourceB700 + difference 2 4) sourceC700) = raw11824 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11824; decide +kernel
    rw [ha]
    exact (canonical11824 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA700 + difference 4 3) (sourceB700 + difference 3 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA700 + difference 4 3) (sourceB700 + difference 3 4) sourceC700) = raw11825 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11825; decide +kernel
    rw [ha]
    exact (canonical11825 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA700 + difference 4 5) (sourceB700 + difference 5 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA700 + difference 4 5) (sourceB700 + difference 5 4) sourceC700) = raw11826 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11826; decide +kernel
    rw [ha]
    exact (canonical11826 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA700 + difference 5 0) (sourceB700 + difference 0 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA700 + difference 5 0) (sourceB700 + difference 0 5) sourceC700) = raw11827 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11827; decide +kernel
    rw [ha]
    exact (canonical11827 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA700 + difference 5 1) (sourceB700 + difference 1 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA700 + difference 5 1) (sourceB700 + difference 1 5) sourceC700) = raw11828 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11828; decide +kernel
    rw [ha]
    exact (canonical11828 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA700 + difference 5 2) (sourceB700 + difference 2 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2834) := by
    have ha : (tripleCharges (sourceA700 + difference 5 2) (sourceB700 + difference 2 5) sourceC700) = raw11829 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11829; decide +kernel
    rw [ha]
    exact (canonical11829 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA700 + difference 5 3) (sourceB700 + difference 3 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA700 + difference 5 3) (sourceB700 + difference 3 5) sourceC700) = raw11830 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11830; decide +kernel
    rw [ha]
    exact (canonical11830 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA700 + difference 5 4) (sourceB700 + difference 4 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA700 + difference 5 4) (sourceB700 + difference 4 5) sourceC700) = raw11831 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11831; decide +kernel
    rw [ha]
    exact (canonical11831 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA700 sourceB700 sourceC700
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm700, Integer.Sparse.eval]
  linarith only [hs]

def sourceA701 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB701 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC701 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceForm701 : Integer.Sparse Master := [(Sum.inr 2833, 2), (Sum.inr 2834, 1), (Sum.inr 2836, 1), (Sum.inr 3037, 1), (Sum.inr 3238, 2), (Sum.inr 3239, 1), (Sum.inr 3241, 1), (Sum.inr 3289, 1), (Sum.inr 3460, 1), (Sum.inr 3461, 1), (Sum.inr 3464, 2), (Sum.inr 3525, 1), (Sum.inr 3528, 2), (Sum.inr 3534, 2), (Sum.inr 3535, 2), (Sum.inr 3541, 2), (Sum.inr 3567, 1), (Sum.inr 3573, 2), (Sum.inr 3801, 1), (Sum.inr 3847, 1), (Sum.inr 3853, 2)]

theorem sourceEq701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm701 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA701 + difference 0 1) (sourceB701 + difference 1 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA701 + difference 0 1) (sourceB701 + difference 1 0) sourceC701) = raw11832 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11832; decide +kernel
    rw [ha]
    exact (canonical11832 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA701 + difference 0 2) (sourceB701 + difference 2 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA701 + difference 0 2) (sourceB701 + difference 2 0) sourceC701) = raw11833 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11833; decide +kernel
    rw [ha]
    exact (canonical11833 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA701 + difference 0 3) (sourceB701 + difference 3 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA701 + difference 0 3) (sourceB701 + difference 3 0) sourceC701) = raw11834 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11834; decide +kernel
    rw [ha]
    exact (canonical11834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA701 + difference 0 4) (sourceB701 + difference 4 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA701 + difference 0 4) (sourceB701 + difference 4 0) sourceC701) = raw11835 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11835; decide +kernel
    rw [ha]
    exact (canonical11835 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA701 + difference 0 5) (sourceB701 + difference 5 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA701 + difference 0 5) (sourceB701 + difference 5 0) sourceC701) = raw11836 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11836; decide +kernel
    rw [ha]
    exact (canonical11836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA701 + difference 1 0) (sourceB701 + difference 0 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA701 + difference 1 0) (sourceB701 + difference 0 1) sourceC701) = raw11837 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11837; decide +kernel
    rw [ha]
    exact (canonical11837 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA701 + difference 1 2) (sourceB701 + difference 2 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2834) := by
    have ha : (tripleCharges (sourceA701 + difference 1 2) (sourceB701 + difference 2 1) sourceC701) = raw11838 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11838; decide +kernel
    rw [ha]
    exact (canonical11838 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA701 + difference 1 3) (sourceB701 + difference 3 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA701 + difference 1 3) (sourceB701 + difference 3 1) sourceC701) = raw11839 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11839; decide +kernel
    rw [ha]
    exact (canonical11839 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA701 + difference 1 4) (sourceB701 + difference 4 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA701 + difference 1 4) (sourceB701 + difference 4 1) sourceC701) = raw11840 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11840; decide +kernel
    rw [ha]
    exact (canonical11840 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA701 + difference 1 5) (sourceB701 + difference 5 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA701 + difference 1 5) (sourceB701 + difference 5 1) sourceC701) = raw11841 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11841; decide +kernel
    rw [ha]
    exact (canonical11841 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA701 + difference 2 0) (sourceB701 + difference 0 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA701 + difference 2 0) (sourceB701 + difference 0 2) sourceC701) = raw11842 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11842; decide +kernel
    rw [ha]
    exact (canonical11842 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA701 + difference 2 1) (sourceB701 + difference 1 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA701 + difference 2 1) (sourceB701 + difference 1 2) sourceC701) = raw11843 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11843; decide +kernel
    rw [ha]
    exact (canonical11843 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA701 + difference 2 3) (sourceB701 + difference 3 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA701 + difference 2 3) (sourceB701 + difference 3 2) sourceC701) = raw11844 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11844; decide +kernel
    rw [ha]
    exact (canonical11844 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA701 + difference 2 4) (sourceB701 + difference 4 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA701 + difference 2 4) (sourceB701 + difference 4 2) sourceC701) = raw11845 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11845; decide +kernel
    rw [ha]
    exact (canonical11845 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA701 + difference 2 5) (sourceB701 + difference 5 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA701 + difference 2 5) (sourceB701 + difference 5 2) sourceC701) = raw11846 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11846; decide +kernel
    rw [ha]
    exact (canonical11846 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA701 + difference 3 0) (sourceB701 + difference 0 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3238) := by
    have ha : (tripleCharges (sourceA701 + difference 3 0) (sourceB701 + difference 0 3) sourceC701) = raw11847 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11847; decide +kernel
    rw [ha]
    exact (canonical11847 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA701 + difference 3 1) (sourceB701 + difference 1 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA701 + difference 3 1) (sourceB701 + difference 1 3) sourceC701) = raw11848 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11848; decide +kernel
    rw [ha]
    exact (canonical11848 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA701 + difference 3 2) (sourceB701 + difference 2 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA701 + difference 3 2) (sourceB701 + difference 2 3) sourceC701) = raw11849 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11849; decide +kernel
    rw [ha]
    exact (canonical11849 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA701 + difference 3 4) (sourceB701 + difference 4 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA701 + difference 3 4) (sourceB701 + difference 4 3) sourceC701) = raw11850 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11850; decide +kernel
    rw [ha]
    exact (canonical11850 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA701 + difference 3 5) (sourceB701 + difference 5 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA701 + difference 3 5) (sourceB701 + difference 5 3) sourceC701) = raw11851 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11851; decide +kernel
    rw [ha]
    exact (canonical11851 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA701 + difference 4 0) (sourceB701 + difference 0 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3238) := by
    have ha : (tripleCharges (sourceA701 + difference 4 0) (sourceB701 + difference 0 4) sourceC701) = raw11852 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11852; decide +kernel
    rw [ha]
    exact (canonical11852 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA701 + difference 4 1) (sourceB701 + difference 1 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA701 + difference 4 1) (sourceB701 + difference 1 4) sourceC701) = raw11853 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11853; decide +kernel
    rw [ha]
    exact (canonical11853 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA701 + difference 4 2) (sourceB701 + difference 2 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA701 + difference 4 2) (sourceB701 + difference 2 4) sourceC701) = raw11854 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11854; decide +kernel
    rw [ha]
    exact (canonical11854 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA701 + difference 4 3) (sourceB701 + difference 3 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA701 + difference 4 3) (sourceB701 + difference 3 4) sourceC701) = raw11855 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11855; decide +kernel
    rw [ha]
    exact (canonical11855 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA701 + difference 4 5) (sourceB701 + difference 5 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA701 + difference 4 5) (sourceB701 + difference 5 4) sourceC701) = raw11856 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11856; decide +kernel
    rw [ha]
    exact (canonical11856 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA701 + difference 5 0) (sourceB701 + difference 0 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3241) := by
    have ha : (tripleCharges (sourceA701 + difference 5 0) (sourceB701 + difference 0 5) sourceC701) = raw11857 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11857; decide +kernel
    rw [ha]
    exact (canonical11857 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA701 + difference 5 1) (sourceB701 + difference 1 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA701 + difference 5 1) (sourceB701 + difference 1 5) sourceC701) = raw11858 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11858; decide +kernel
    rw [ha]
    exact (canonical11858 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA701 + difference 5 2) (sourceB701 + difference 2 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2836) := by
    have ha : (tripleCharges (sourceA701 + difference 5 2) (sourceB701 + difference 2 5) sourceC701) = raw11859 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11859; decide +kernel
    rw [ha]
    exact (canonical11859 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA701 + difference 5 3) (sourceB701 + difference 3 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA701 + difference 5 3) (sourceB701 + difference 3 5) sourceC701) = raw11860 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11860; decide +kernel
    rw [ha]
    exact (canonical11860 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA701 + difference 5 4) (sourceB701 + difference 4 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA701 + difference 5 4) (sourceB701 + difference 4 5) sourceC701) = raw11861 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11861; decide +kernel
    rw [ha]
    exact (canonical11861 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA701 sourceB701 sourceC701
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm701, Integer.Sparse.eval]
  linarith only [hs]

def sourceA702 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB702 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC702 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceForm702 : Integer.Sparse Master := [(Sum.inr 2730, 2), (Sum.inr 3812, 2), (Sum.inr 3906, 2), (Sum.inr 4092, -1)]

theorem sourceEq702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm702 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA702 + difference 0 0) (sourceB702 + difference 0 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA702 + difference 0 0) (sourceB702 + difference 0 0) sourceC702) = raw11862 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11862; decide +kernel
    rw [ha]
    exact (canonical11862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA702 + difference 0 1) (sourceB702 + difference 1 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA702 + difference 0 1) (sourceB702 + difference 1 0) sourceC702) = raw11863 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11863; decide +kernel
    rw [ha]
    exact (canonical11863 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA702 + difference 0 2) (sourceB702 + difference 2 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA702 + difference 0 2) (sourceB702 + difference 2 0) sourceC702) = raw11864 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11864; decide +kernel
    rw [ha]
    exact (canonical11864 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA702 + difference 0 3) (sourceB702 + difference 3 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA702 + difference 0 3) (sourceB702 + difference 3 0) sourceC702) = raw11865 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11865; decide +kernel
    rw [ha]
    exact (canonical11865 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA702 + difference 0 4) (sourceB702 + difference 4 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA702 + difference 0 4) (sourceB702 + difference 4 0) sourceC702) = raw11866 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11866; decide +kernel
    rw [ha]
    exact (canonical11866 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA702 + difference 0 5) (sourceB702 + difference 5 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA702 + difference 0 5) (sourceB702 + difference 5 0) sourceC702) = raw11867 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11867; decide +kernel
    rw [ha]
    exact (canonical11867 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA702 + sourceB702) sourceC702) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA702 + sourceB702) sourceC702) = raw11868 := by
      apply Matrix.ext; unfold doubleCharges sourceA702 sourceB702 sourceC702 raw11868; decide +kernel
    rw [ha]
    exact (canonical11868 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA702 sourceB702 sourceC702
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm702, Integer.Sparse.eval]
  linarith only [hs]

def sourceA703 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB703 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC703 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceForm703 : Integer.Sparse Master := [(Sum.inr 1222, 1), (Sum.inr 1223, 2), (Sum.inr 1233, 1), (Sum.inr 1276, 1), (Sum.inr 2730, 1), (Sum.inr 4092, -1)]

theorem sourceEq703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm703 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA703 + difference 0 0) (sourceB703 + difference 0 0) sourceC703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA703 + difference 0 0) (sourceB703 + difference 0 0) sourceC703) = raw11862 := by
      apply Matrix.ext; unfold tripleCharges sourceA703 sourceB703 sourceC703 difference raw11862; decide +kernel
    rw [ha]
    exact (canonical11862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA703 + difference 1 0) (sourceB703 + difference 0 1) sourceC703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1276) := by
    have ha : (tripleCharges (sourceA703 + difference 1 0) (sourceB703 + difference 0 1) sourceC703) = raw11869 := by
      apply Matrix.ext; unfold tripleCharges sourceA703 sourceB703 sourceC703 difference raw11869; decide +kernel
    rw [ha]
    exact (canonical11869 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA703 + difference 2 0) (sourceB703 + difference 0 2) sourceC703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA703 + difference 2 0) (sourceB703 + difference 0 2) sourceC703) = raw11870 := by
      apply Matrix.ext; unfold tripleCharges sourceA703 sourceB703 sourceC703 difference raw11870; decide +kernel
    rw [ha]
    exact (canonical11870 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA703 + difference 3 0) (sourceB703 + difference 0 3) sourceC703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1223) := by
    have ha : (tripleCharges (sourceA703 + difference 3 0) (sourceB703 + difference 0 3) sourceC703) = raw11871 := by
      apply Matrix.ext; unfold tripleCharges sourceA703 sourceB703 sourceC703 difference raw11871; decide +kernel
    rw [ha]
    exact (canonical11871 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA703 + difference 4 0) (sourceB703 + difference 0 4) sourceC703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1223) := by
    have ha : (tripleCharges (sourceA703 + difference 4 0) (sourceB703 + difference 0 4) sourceC703) = raw11872 := by
      apply Matrix.ext; unfold tripleCharges sourceA703 sourceB703 sourceC703 difference raw11872; decide +kernel
    rw [ha]
    exact (canonical11872 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA703 + difference 5 0) (sourceB703 + difference 0 5) sourceC703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1222) := by
    have ha : (tripleCharges (sourceA703 + difference 5 0) (sourceB703 + difference 0 5) sourceC703) = raw11873 := by
      apply Matrix.ext; unfold tripleCharges sourceA703 sourceB703 sourceC703 difference raw11873; decide +kernel
    rw [ha]
    exact (canonical11873 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA703 + sourceB703) sourceC703) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA703 + sourceB703) sourceC703) = raw11868 := by
      apply Matrix.ext; unfold doubleCharges sourceA703 sourceB703 sourceC703 raw11868; decide +kernel
    rw [ha]
    exact (canonical11868 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA703 sourceB703 sourceC703
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm703, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
