import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical128
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical137
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical272
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical273
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical274
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical275
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical276

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2528 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2528 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2528 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm2528 : Integer.Sparse Master := [(Sum.inr 1815, 2), (Sum.inr 1818, 2), (Sum.inr 2116, 1), (Sum.inr 2341, 4), (Sum.inr 2345, 2), (Sum.inr 2604, 2), (Sum.inr 2818, 2), (Sum.inr 2969, 1), (Sum.inr 3709, 2), (Sum.inr 3737, 4), (Sum.inr 3790, 2), (Sum.inr 3888, 2), (Sum.inr 3933, 2), (Sum.inr 4001, 2)]

theorem sourceEq2528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2528 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2528 + difference 0 1) (sourceB2528 + difference 1 0) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA2528 + difference 0 1) (sourceB2528 + difference 1 0) sourceC2528) = raw34866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34866; decide +kernel
    rw [ha]
    exact (canonical34866 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2528 + difference 0 2) (sourceB2528 + difference 2 0) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2528 + difference 0 2) (sourceB2528 + difference 2 0) sourceC2528) = raw34867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34867; decide +kernel
    rw [ha]
    exact (canonical34867 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2528 + difference 0 3) (sourceB2528 + difference 3 0) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2528 + difference 0 3) (sourceB2528 + difference 3 0) sourceC2528) = raw34868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34868; decide +kernel
    rw [ha]
    exact (canonical34868 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2528 + difference 0 4) (sourceB2528 + difference 4 0) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2528 + difference 0 4) (sourceB2528 + difference 4 0) sourceC2528) = raw34869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34869; decide +kernel
    rw [ha]
    exact (canonical34869 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2528 + difference 0 5) (sourceB2528 + difference 5 0) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2528 + difference 0 5) (sourceB2528 + difference 5 0) sourceC2528) = raw34870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34870; decide +kernel
    rw [ha]
    exact (canonical34870 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2528 + difference 1 0) (sourceB2528 + difference 0 1) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA2528 + difference 1 0) (sourceB2528 + difference 0 1) sourceC2528) = raw22586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw22586; decide +kernel
    rw [ha]
    exact (canonical22586 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2528 + difference 1 2) (sourceB2528 + difference 2 1) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3933) := by
    have ha : (tripleCharges (sourceA2528 + difference 1 2) (sourceB2528 + difference 2 1) sourceC2528) = raw29637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw29637; decide +kernel
    rw [ha]
    exact (canonical29637 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2528 + difference 1 3) (sourceB2528 + difference 3 1) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3933) := by
    have ha : (tripleCharges (sourceA2528 + difference 1 3) (sourceB2528 + difference 3 1) sourceC2528) = raw29638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw29638; decide +kernel
    rw [ha]
    exact (canonical29638 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2528 + difference 1 4) (sourceB2528 + difference 4 1) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA2528 + difference 1 4) (sourceB2528 + difference 4 1) sourceC2528) = raw27626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw27626; decide +kernel
    rw [ha]
    exact (canonical27626 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2528 + difference 1 5) (sourceB2528 + difference 5 1) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA2528 + difference 1 5) (sourceB2528 + difference 5 1) sourceC2528) = raw29639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw29639; decide +kernel
    rw [ha]
    exact (canonical29639 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2528 + difference 2 0) (sourceB2528 + difference 0 2) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2818) := by
    have ha : (tripleCharges (sourceA2528 + difference 2 0) (sourceB2528 + difference 0 2) sourceC2528) = raw29640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw29640; decide +kernel
    rw [ha]
    exact (canonical29640 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2528 + difference 2 1) (sourceB2528 + difference 1 2) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1815) := by
    have ha : (tripleCharges (sourceA2528 + difference 2 1) (sourceB2528 + difference 1 2) sourceC2528) = raw34871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34871; decide +kernel
    rw [ha]
    exact (canonical34871 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2528 + difference 2 3) (sourceB2528 + difference 3 2) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3709) := by
    have ha : (tripleCharges (sourceA2528 + difference 2 3) (sourceB2528 + difference 3 2) sourceC2528) = raw34872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34872; decide +kernel
    rw [ha]
    exact (canonical34872 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2528 + difference 2 4) (sourceB2528 + difference 4 2) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2528 + difference 2 4) (sourceB2528 + difference 4 2) sourceC2528) = raw34873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34873; decide +kernel
    rw [ha]
    exact (canonical34873 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2528 + difference 2 5) (sourceB2528 + difference 5 2) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2528 + difference 2 5) (sourceB2528 + difference 5 2) sourceC2528) = raw34874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34874; decide +kernel
    rw [ha]
    exact (canonical34874 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2528 + difference 3 0) (sourceB2528 + difference 0 3) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2818) := by
    have ha : (tripleCharges (sourceA2528 + difference 3 0) (sourceB2528 + difference 0 3) sourceC2528) = raw29643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw29643; decide +kernel
    rw [ha]
    exact (canonical29643 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2528 + difference 3 1) (sourceB2528 + difference 1 3) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1815) := by
    have ha : (tripleCharges (sourceA2528 + difference 3 1) (sourceB2528 + difference 1 3) sourceC2528) = raw34875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34875; decide +kernel
    rw [ha]
    exact (canonical34875 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2528 + difference 3 2) (sourceB2528 + difference 2 3) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3709) := by
    have ha : (tripleCharges (sourceA2528 + difference 3 2) (sourceB2528 + difference 2 3) sourceC2528) = raw34876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34876; decide +kernel
    rw [ha]
    exact (canonical34876 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2528 + difference 3 4) (sourceB2528 + difference 4 3) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2528 + difference 3 4) (sourceB2528 + difference 4 3) sourceC2528) = raw32076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw32076; decide +kernel
    rw [ha]
    exact (canonical32076 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2528 + difference 3 5) (sourceB2528 + difference 5 3) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2528 + difference 3 5) (sourceB2528 + difference 5 3) sourceC2528) = raw34877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34877; decide +kernel
    rw [ha]
    exact (canonical34877 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2528 + difference 4 0) (sourceB2528 + difference 0 4) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2345) := by
    have ha : (tripleCharges (sourceA2528 + difference 4 0) (sourceB2528 + difference 0 4) sourceC2528) = raw29646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw29646; decide +kernel
    rw [ha]
    exact (canonical29646 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2528 + difference 4 1) (sourceB2528 + difference 1 4) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1818) := by
    have ha : (tripleCharges (sourceA2528 + difference 4 1) (sourceB2528 + difference 1 4) sourceC2528) = raw34878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34878; decide +kernel
    rw [ha]
    exact (canonical34878 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2528 + difference 4 2) (sourceB2528 + difference 2 4) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2528 + difference 4 2) (sourceB2528 + difference 2 4) sourceC2528) = raw34879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34879; decide +kernel
    rw [ha]
    exact (canonical34879 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2528 + difference 4 3) (sourceB2528 + difference 3 4) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2528 + difference 4 3) (sourceB2528 + difference 3 4) sourceC2528) = raw34880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34880; decide +kernel
    rw [ha]
    exact (canonical34880 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2528 + difference 4 5) (sourceB2528 + difference 5 4) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2528 + difference 4 5) (sourceB2528 + difference 5 4) sourceC2528) = raw34881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34881; decide +kernel
    rw [ha]
    exact (canonical34881 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2528 + difference 5 0) (sourceB2528 + difference 0 5) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2345) := by
    have ha : (tripleCharges (sourceA2528 + difference 5 0) (sourceB2528 + difference 0 5) sourceC2528) = raw27632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw27632; decide +kernel
    rw [ha]
    exact (canonical27632 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2528 + difference 5 1) (sourceB2528 + difference 1 5) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1818) := by
    have ha : (tripleCharges (sourceA2528 + difference 5 1) (sourceB2528 + difference 1 5) sourceC2528) = raw34882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34882; decide +kernel
    rw [ha]
    exact (canonical34882 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2528 + difference 5 2) (sourceB2528 + difference 2 5) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2528 + difference 5 2) (sourceB2528 + difference 2 5) sourceC2528) = raw34883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34883; decide +kernel
    rw [ha]
    exact (canonical34883 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2528 + difference 5 3) (sourceB2528 + difference 3 5) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2528 + difference 5 3) (sourceB2528 + difference 3 5) sourceC2528) = raw34884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw34884; decide +kernel
    rw [ha]
    exact (canonical34884 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2528 + difference 5 4) (sourceB2528 + difference 4 5) sourceC2528) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2528 + difference 5 4) (sourceB2528 + difference 4 5) sourceC2528) = raw27623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2528 sourceB2528 sourceC2528 difference raw27623; decide +kernel
    rw [ha]
    exact (canonical27623 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2528 sourceB2528 sourceC2528
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2528, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2529 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2529 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2529 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceForm2529 : Integer.Sparse Master := [(Sum.inr 5236, 4), (Sum.inr 5238, 4), (Sum.inr 5303, 1), (Sum.inr 5355, 8), (Sum.inr 5356, 4), (Sum.inr 5371, 4), (Sum.inr 5377, 2), (Sum.inr 5389, 2), (Sum.inr 5466, 1)]

theorem sourceEq2529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2529 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2529 + difference 0 1) (sourceB2529 + difference 1 0) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5466) := by
    have ha : (tripleCharges (sourceA2529 + difference 0 1) (sourceB2529 + difference 1 0) sourceC2529) = raw34885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34885; decide +kernel
    rw [ha]
    exact (canonical34885 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2529 + difference 0 2) (sourceB2529 + difference 2 0) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2529 + difference 0 2) (sourceB2529 + difference 2 0) sourceC2529) = raw34886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34886; decide +kernel
    rw [ha]
    exact (canonical34886 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2529 + difference 0 3) (sourceB2529 + difference 3 0) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2529 + difference 0 3) (sourceB2529 + difference 3 0) sourceC2529) = raw34887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34887; decide +kernel
    rw [ha]
    exact (canonical34887 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2529 + difference 0 4) (sourceB2529 + difference 4 0) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2529 + difference 0 4) (sourceB2529 + difference 4 0) sourceC2529) = raw34821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34821; decide +kernel
    rw [ha]
    exact (canonical34821 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2529 + difference 0 5) (sourceB2529 + difference 5 0) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2529 + difference 0 5) (sourceB2529 + difference 5 0) sourceC2529) = raw34888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34888; decide +kernel
    rw [ha]
    exact (canonical34888 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2529 + difference 1 0) (sourceB2529 + difference 0 1) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5303) := by
    have ha : (tripleCharges (sourceA2529 + difference 1 0) (sourceB2529 + difference 0 1) sourceC2529) = raw34889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34889; decide +kernel
    rw [ha]
    exact (canonical34889 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2529 + difference 1 2) (sourceB2529 + difference 2 1) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2529 + difference 1 2) (sourceB2529 + difference 2 1) sourceC2529) = raw34890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34890; decide +kernel
    rw [ha]
    exact (canonical34890 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2529 + difference 1 3) (sourceB2529 + difference 3 1) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2529 + difference 1 3) (sourceB2529 + difference 3 1) sourceC2529) = raw34891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34891; decide +kernel
    rw [ha]
    exact (canonical34891 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2529 + difference 1 4) (sourceB2529 + difference 4 1) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2529 + difference 1 4) (sourceB2529 + difference 4 1) sourceC2529) = raw34826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34826; decide +kernel
    rw [ha]
    exact (canonical34826 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2529 + difference 1 5) (sourceB2529 + difference 5 1) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2529 + difference 1 5) (sourceB2529 + difference 5 1) sourceC2529) = raw34892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34892; decide +kernel
    rw [ha]
    exact (canonical34892 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2529 + difference 2 0) (sourceB2529 + difference 0 2) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2529 + difference 2 0) (sourceB2529 + difference 0 2) sourceC2529) = raw34893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34893; decide +kernel
    rw [ha]
    exact (canonical34893 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2529 + difference 2 1) (sourceB2529 + difference 1 2) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2529 + difference 2 1) (sourceB2529 + difference 1 2) sourceC2529) = raw34894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34894; decide +kernel
    rw [ha]
    exact (canonical34894 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2529 + difference 2 3) (sourceB2529 + difference 3 2) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA2529 + difference 2 3) (sourceB2529 + difference 3 2) sourceC2529) = raw34895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34895; decide +kernel
    rw [ha]
    exact (canonical34895 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2529 + difference 2 4) (sourceB2529 + difference 4 2) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2529 + difference 2 4) (sourceB2529 + difference 4 2) sourceC2529) = raw34831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34831; decide +kernel
    rw [ha]
    exact (canonical34831 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2529 + difference 2 5) (sourceB2529 + difference 5 2) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2529 + difference 2 5) (sourceB2529 + difference 5 2) sourceC2529) = raw34896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34896; decide +kernel
    rw [ha]
    exact (canonical34896 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2529 + difference 3 0) (sourceB2529 + difference 0 3) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2529 + difference 3 0) (sourceB2529 + difference 0 3) sourceC2529) = raw34897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34897; decide +kernel
    rw [ha]
    exact (canonical34897 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2529 + difference 3 1) (sourceB2529 + difference 1 3) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2529 + difference 3 1) (sourceB2529 + difference 1 3) sourceC2529) = raw34898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34898; decide +kernel
    rw [ha]
    exact (canonical34898 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2529 + difference 3 2) (sourceB2529 + difference 2 3) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA2529 + difference 3 2) (sourceB2529 + difference 2 3) sourceC2529) = raw34899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34899; decide +kernel
    rw [ha]
    exact (canonical34899 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2529 + difference 3 4) (sourceB2529 + difference 4 3) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2529 + difference 3 4) (sourceB2529 + difference 4 3) sourceC2529) = raw34836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34836; decide +kernel
    rw [ha]
    exact (canonical34836 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2529 + difference 3 5) (sourceB2529 + difference 5 3) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2529 + difference 3 5) (sourceB2529 + difference 5 3) sourceC2529) = raw34900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34900; decide +kernel
    rw [ha]
    exact (canonical34900 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2529 + difference 4 0) (sourceB2529 + difference 0 4) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2529 + difference 4 0) (sourceB2529 + difference 0 4) sourceC2529) = raw34901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34901; decide +kernel
    rw [ha]
    exact (canonical34901 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2529 + difference 4 1) (sourceB2529 + difference 1 4) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2529 + difference 4 1) (sourceB2529 + difference 1 4) sourceC2529) = raw34902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34902; decide +kernel
    rw [ha]
    exact (canonical34902 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2529 + difference 4 2) (sourceB2529 + difference 2 4) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2529 + difference 4 2) (sourceB2529 + difference 2 4) sourceC2529) = raw34903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34903; decide +kernel
    rw [ha]
    exact (canonical34903 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2529 + difference 4 3) (sourceB2529 + difference 3 4) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2529 + difference 4 3) (sourceB2529 + difference 3 4) sourceC2529) = raw34904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34904; decide +kernel
    rw [ha]
    exact (canonical34904 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2529 + difference 4 5) (sourceB2529 + difference 5 4) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2529 + difference 4 5) (sourceB2529 + difference 5 4) sourceC2529) = raw34905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34905; decide +kernel
    rw [ha]
    exact (canonical34905 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2529 + difference 5 0) (sourceB2529 + difference 0 5) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2529 + difference 5 0) (sourceB2529 + difference 0 5) sourceC2529) = raw34837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34837; decide +kernel
    rw [ha]
    exact (canonical34837 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2529 + difference 5 1) (sourceB2529 + difference 1 5) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2529 + difference 5 1) (sourceB2529 + difference 1 5) sourceC2529) = raw34838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34838; decide +kernel
    rw [ha]
    exact (canonical34838 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2529 + difference 5 2) (sourceB2529 + difference 2 5) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2529 + difference 5 2) (sourceB2529 + difference 2 5) sourceC2529) = raw34839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34839; decide +kernel
    rw [ha]
    exact (canonical34839 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2529 + difference 5 3) (sourceB2529 + difference 3 5) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2529 + difference 5 3) (sourceB2529 + difference 3 5) sourceC2529) = raw34840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34840; decide +kernel
    rw [ha]
    exact (canonical34840 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2529 + difference 5 4) (sourceB2529 + difference 4 5) sourceC2529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2529 + difference 5 4) (sourceB2529 + difference 4 5) sourceC2529) = raw34906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2529 sourceB2529 sourceC2529 difference raw34906; decide +kernel
    rw [ha]
    exact (canonical34906 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2529 sourceB2529 sourceC2529
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2529, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2530 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2530 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC2530 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm2530 : Integer.Sparse Master := [(Sum.inr 4634, 1), (Sum.inr 4636, 1), (Sum.inr 4638, 1), (Sum.inr 4653, 1), (Sum.inr 4661, 1), (Sum.inr 4662, 1), (Sum.inr 4684, 1), (Sum.inr 4810, 1), (Sum.inr 4828, 1), (Sum.inr 4905, 1), (Sum.inr 4908, 1), (Sum.inr 4922, 1), (Sum.inr 4961, 1), (Sum.inr 4977, 1), (Sum.inr 5080, 1), (Sum.inr 5152, 1), (Sum.inr 5333, 1), (Sum.inr 5336, 1), (Sum.inr 5349, 1), (Sum.inr 5354, 1), (Sum.inr 5364, 1), (Sum.inr 5370, 1), (Sum.inr 5378, 1), (Sum.inr 5380, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 1), (Sum.inr 5432, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5438, 1)]

theorem sourceEq2530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2530 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2530 + difference 0 1) (sourceB2530 + difference 1 0) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2530 + difference 0 1) (sourceB2530 + difference 1 0) sourceC2530) = raw34907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34907; decide +kernel
    rw [ha]
    exact (canonical34907 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2530 + difference 0 2) (sourceB2530 + difference 2 0) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2530 + difference 0 2) (sourceB2530 + difference 2 0) sourceC2530) = raw34908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34908; decide +kernel
    rw [ha]
    exact (canonical34908 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2530 + difference 0 3) (sourceB2530 + difference 3 0) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA2530 + difference 0 3) (sourceB2530 + difference 3 0) sourceC2530) = raw34909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34909; decide +kernel
    rw [ha]
    exact (canonical34909 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2530 + difference 0 4) (sourceB2530 + difference 4 0) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2530 + difference 0 4) (sourceB2530 + difference 4 0) sourceC2530) = raw15017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw15017; decide +kernel
    rw [ha]
    exact (canonical15017 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2530 + difference 0 5) (sourceB2530 + difference 5 0) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2530 + difference 0 5) (sourceB2530 + difference 5 0) sourceC2530) = raw34910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34910; decide +kernel
    rw [ha]
    exact (canonical34910 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2530 + difference 1 0) (sourceB2530 + difference 0 1) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2530 + difference 1 0) (sourceB2530 + difference 0 1) sourceC2530) = raw7827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw7827; decide +kernel
    rw [ha]
    exact (canonical7827 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2530 + difference 1 2) (sourceB2530 + difference 2 1) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2530 + difference 1 2) (sourceB2530 + difference 2 1) sourceC2530) = raw15032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw15032; decide +kernel
    rw [ha]
    exact (canonical15032 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2530 + difference 1 3) (sourceB2530 + difference 3 1) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2530 + difference 1 3) (sourceB2530 + difference 3 1) sourceC2530) = raw15033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw15033; decide +kernel
    rw [ha]
    exact (canonical15033 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2530 + difference 1 4) (sourceB2530 + difference 4 1) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2530 + difference 1 4) (sourceB2530 + difference 4 1) sourceC2530) = raw7806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw7806; decide +kernel
    rw [ha]
    exact (canonical7806 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2530 + difference 1 5) (sourceB2530 + difference 5 1) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2530 + difference 1 5) (sourceB2530 + difference 5 1) sourceC2530) = raw15034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw15034; decide +kernel
    rw [ha]
    exact (canonical15034 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2530 + difference 2 0) (sourceB2530 + difference 0 2) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2530 + difference 2 0) (sourceB2530 + difference 0 2) sourceC2530) = raw29715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw29715; decide +kernel
    rw [ha]
    exact (canonical29715 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2530 + difference 2 1) (sourceB2530 + difference 1 2) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2530 + difference 2 1) (sourceB2530 + difference 1 2) sourceC2530) = raw34911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34911; decide +kernel
    rw [ha]
    exact (canonical34911 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2530 + difference 2 3) (sourceB2530 + difference 3 2) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2530 + difference 2 3) (sourceB2530 + difference 3 2) sourceC2530) = raw34912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34912; decide +kernel
    rw [ha]
    exact (canonical34912 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2530 + difference 2 4) (sourceB2530 + difference 4 2) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2530 + difference 2 4) (sourceB2530 + difference 4 2) sourceC2530) = raw15023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw15023; decide +kernel
    rw [ha]
    exact (canonical15023 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2530 + difference 2 5) (sourceB2530 + difference 5 2) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2530 + difference 2 5) (sourceB2530 + difference 5 2) sourceC2530) = raw34913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34913; decide +kernel
    rw [ha]
    exact (canonical34913 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2530 + difference 3 0) (sourceB2530 + difference 0 3) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2530 + difference 3 0) (sourceB2530 + difference 0 3) sourceC2530) = raw29718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw29718; decide +kernel
    rw [ha]
    exact (canonical29718 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2530 + difference 3 1) (sourceB2530 + difference 1 3) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2530 + difference 3 1) (sourceB2530 + difference 1 3) sourceC2530) = raw34914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34914; decide +kernel
    rw [ha]
    exact (canonical34914 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2530 + difference 3 2) (sourceB2530 + difference 2 3) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2530 + difference 3 2) (sourceB2530 + difference 2 3) sourceC2530) = raw34915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34915; decide +kernel
    rw [ha]
    exact (canonical34915 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2530 + difference 3 4) (sourceB2530 + difference 4 3) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2530 + difference 3 4) (sourceB2530 + difference 4 3) sourceC2530) = raw15027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw15027; decide +kernel
    rw [ha]
    exact (canonical15027 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2530 + difference 3 5) (sourceB2530 + difference 5 3) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2530 + difference 3 5) (sourceB2530 + difference 5 3) sourceC2530) = raw34916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34916; decide +kernel
    rw [ha]
    exact (canonical34916 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2530 + difference 4 0) (sourceB2530 + difference 0 4) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4638) := by
    have ha : (tripleCharges (sourceA2530 + difference 4 0) (sourceB2530 + difference 0 4) sourceC2530) = raw29721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw29721; decide +kernel
    rw [ha]
    exact (canonical29721 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2530 + difference 4 1) (sourceB2530 + difference 1 4) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4636) := by
    have ha : (tripleCharges (sourceA2530 + difference 4 1) (sourceB2530 + difference 1 4) sourceC2530) = raw34917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34917; decide +kernel
    rw [ha]
    exact (canonical34917 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2530 + difference 4 2) (sourceB2530 + difference 2 4) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4634) := by
    have ha : (tripleCharges (sourceA2530 + difference 4 2) (sourceB2530 + difference 2 4) sourceC2530) = raw34918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34918; decide +kernel
    rw [ha]
    exact (canonical34918 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2530 + difference 4 3) (sourceB2530 + difference 3 4) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4653) := by
    have ha : (tripleCharges (sourceA2530 + difference 4 3) (sourceB2530 + difference 3 4) sourceC2530) = raw34919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34919; decide +kernel
    rw [ha]
    exact (canonical34919 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2530 + difference 4 5) (sourceB2530 + difference 5 4) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2530 + difference 4 5) (sourceB2530 + difference 5 4) sourceC2530) = raw34920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34920; decide +kernel
    rw [ha]
    exact (canonical34920 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2530 + difference 5 0) (sourceB2530 + difference 0 5) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4908) := by
    have ha : (tripleCharges (sourceA2530 + difference 5 0) (sourceB2530 + difference 0 5) sourceC2530) = raw27842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw27842; decide +kernel
    rw [ha]
    exact (canonical27842 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2530 + difference 5 1) (sourceB2530 + difference 1 5) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4662) := by
    have ha : (tripleCharges (sourceA2530 + difference 5 1) (sourceB2530 + difference 1 5) sourceC2530) = raw34921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34921; decide +kernel
    rw [ha]
    exact (canonical34921 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2530 + difference 5 2) (sourceB2530 + difference 2 5) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4905) := by
    have ha : (tripleCharges (sourceA2530 + difference 5 2) (sourceB2530 + difference 2 5) sourceC2530) = raw34922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34922; decide +kernel
    rw [ha]
    exact (canonical34922 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2530 + difference 5 3) (sourceB2530 + difference 3 5) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4922) := by
    have ha : (tripleCharges (sourceA2530 + difference 5 3) (sourceB2530 + difference 3 5) sourceC2530) = raw34923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw34923; decide +kernel
    rw [ha]
    exact (canonical34923 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2530 + difference 5 4) (sourceB2530 + difference 4 5) sourceC2530) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2530 + difference 5 4) (sourceB2530 + difference 4 5) sourceC2530) = raw15035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2530 sourceB2530 sourceC2530 difference raw15035; decide +kernel
    rw [ha]
    exact (canonical15035 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2530 sourceB2530 sourceC2530
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2530, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2531 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2531 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC2531 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm2531 : Integer.Sparse Master := [(Sum.inr 1763, 1), (Sum.inr 1765, 1), (Sum.inr 1767, 1), (Sum.inr 1781, 1), (Sum.inr 1787, 1), (Sum.inr 1788, 1), (Sum.inr 1810, 1), (Sum.inr 2028, 1), (Sum.inr 2082, 1), (Sum.inr 2298, 1), (Sum.inr 2301, 1), (Sum.inr 2313, 1), (Sum.inr 2488, 1), (Sum.inr 2796, 1), (Sum.inr 2813, 1), (Sum.inr 2931, 1), (Sum.inr 3668, 1), (Sum.inr 3671, 1), (Sum.inr 3687, 1), (Sum.inr 3692, 1), (Sum.inr 3702, 1), (Sum.inr 3706, 1), (Sum.inr 3719, 1), (Sum.inr 3721, 1), (Sum.inr 3736, 1), (Sum.inr 3737, 1), (Sum.inr 3850, 1), (Sum.inr 3853, 1), (Sum.inr 3876, 1), (Sum.inr 3982, 1)]

theorem sourceEq2531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2531 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2531 + difference 0 1) (sourceB2531 + difference 1 0) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2531 + difference 0 1) (sourceB2531 + difference 1 0) sourceC2531) = raw34924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34924; decide +kernel
    rw [ha]
    exact (canonical34924 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2531 + difference 0 2) (sourceB2531 + difference 2 0) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3687) := by
    have ha : (tripleCharges (sourceA2531 + difference 0 2) (sourceB2531 + difference 2 0) sourceC2531) = raw34925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34925; decide +kernel
    rw [ha]
    exact (canonical34925 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2531 + difference 0 3) (sourceB2531 + difference 3 0) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3702) := by
    have ha : (tripleCharges (sourceA2531 + difference 0 3) (sourceB2531 + difference 3 0) sourceC2531) = raw34926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34926; decide +kernel
    rw [ha]
    exact (canonical34926 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2531 + difference 0 4) (sourceB2531 + difference 4 0) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA2531 + difference 0 4) (sourceB2531 + difference 4 0) sourceC2531) = raw15039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw15039; decide +kernel
    rw [ha]
    exact (canonical15039 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2531 + difference 0 5) (sourceB2531 + difference 5 0) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA2531 + difference 0 5) (sourceB2531 + difference 5 0) sourceC2531) = raw34927 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34927; decide +kernel
    rw [ha]
    exact (canonical34927 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2531 + difference 1 0) (sourceB2531 + difference 0 1) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2531 + difference 1 0) (sourceB2531 + difference 0 1) sourceC2531) = raw7857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw7857; decide +kernel
    rw [ha]
    exact (canonical7857 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2531 + difference 1 2) (sourceB2531 + difference 2 1) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA2531 + difference 1 2) (sourceB2531 + difference 2 1) sourceC2531) = raw15054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw15054; decide +kernel
    rw [ha]
    exact (canonical15054 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2531 + difference 1 3) (sourceB2531 + difference 3 1) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2531 + difference 1 3) (sourceB2531 + difference 3 1) sourceC2531) = raw15055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw15055; decide +kernel
    rw [ha]
    exact (canonical15055 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2531 + difference 1 4) (sourceB2531 + difference 4 1) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA2531 + difference 1 4) (sourceB2531 + difference 4 1) sourceC2531) = raw7836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw7836; decide +kernel
    rw [ha]
    exact (canonical7836 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2531 + difference 1 5) (sourceB2531 + difference 5 1) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2531 + difference 1 5) (sourceB2531 + difference 5 1) sourceC2531) = raw15056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw15056; decide +kernel
    rw [ha]
    exact (canonical15056 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2531 + difference 2 0) (sourceB2531 + difference 0 2) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2796) := by
    have ha : (tripleCharges (sourceA2531 + difference 2 0) (sourceB2531 + difference 0 2) sourceC2531) = raw29725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw29725; decide +kernel
    rw [ha]
    exact (canonical29725 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2531 + difference 2 1) (sourceB2531 + difference 1 2) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1787) := by
    have ha : (tripleCharges (sourceA2531 + difference 2 1) (sourceB2531 + difference 1 2) sourceC2531) = raw34928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34928; decide +kernel
    rw [ha]
    exact (canonical34928 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2531 + difference 2 3) (sourceB2531 + difference 3 2) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3668) := by
    have ha : (tripleCharges (sourceA2531 + difference 2 3) (sourceB2531 + difference 3 2) sourceC2531) = raw34929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34929; decide +kernel
    rw [ha]
    exact (canonical34929 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2531 + difference 2 4) (sourceB2531 + difference 4 2) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2531 + difference 2 4) (sourceB2531 + difference 4 2) sourceC2531) = raw15045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw15045; decide +kernel
    rw [ha]
    exact (canonical15045 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2531 + difference 2 5) (sourceB2531 + difference 5 2) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2531 + difference 2 5) (sourceB2531 + difference 5 2) sourceC2531) = raw34930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34930; decide +kernel
    rw [ha]
    exact (canonical34930 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2531 + difference 3 0) (sourceB2531 + difference 0 3) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2531 + difference 3 0) (sourceB2531 + difference 0 3) sourceC2531) = raw29728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw29728; decide +kernel
    rw [ha]
    exact (canonical29728 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2531 + difference 3 1) (sourceB2531 + difference 1 3) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2531 + difference 3 1) (sourceB2531 + difference 1 3) sourceC2531) = raw34931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34931; decide +kernel
    rw [ha]
    exact (canonical34931 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2531 + difference 3 2) (sourceB2531 + difference 2 3) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3671) := by
    have ha : (tripleCharges (sourceA2531 + difference 3 2) (sourceB2531 + difference 2 3) sourceC2531) = raw34932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34932; decide +kernel
    rw [ha]
    exact (canonical34932 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2531 + difference 3 4) (sourceB2531 + difference 4 3) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2531 + difference 3 4) (sourceB2531 + difference 4 3) sourceC2531) = raw15049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw15049; decide +kernel
    rw [ha]
    exact (canonical15049 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2531 + difference 3 5) (sourceB2531 + difference 5 3) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3736) := by
    have ha : (tripleCharges (sourceA2531 + difference 3 5) (sourceB2531 + difference 5 3) sourceC2531) = raw34933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34933; decide +kernel
    rw [ha]
    exact (canonical34933 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2531 + difference 4 0) (sourceB2531 + difference 0 4) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1767) := by
    have ha : (tripleCharges (sourceA2531 + difference 4 0) (sourceB2531 + difference 0 4) sourceC2531) = raw29731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw29731; decide +kernel
    rw [ha]
    exact (canonical29731 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2531 + difference 4 1) (sourceB2531 + difference 1 4) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1765) := by
    have ha : (tripleCharges (sourceA2531 + difference 4 1) (sourceB2531 + difference 1 4) sourceC2531) = raw34934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34934; decide +kernel
    rw [ha]
    exact (canonical34934 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2531 + difference 4 2) (sourceB2531 + difference 2 4) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1763) := by
    have ha : (tripleCharges (sourceA2531 + difference 4 2) (sourceB2531 + difference 2 4) sourceC2531) = raw34935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34935; decide +kernel
    rw [ha]
    exact (canonical34935 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2531 + difference 4 3) (sourceB2531 + difference 3 4) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1781) := by
    have ha : (tripleCharges (sourceA2531 + difference 4 3) (sourceB2531 + difference 3 4) sourceC2531) = raw34936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34936; decide +kernel
    rw [ha]
    exact (canonical34936 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2531 + difference 4 5) (sourceB2531 + difference 5 4) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2531 + difference 4 5) (sourceB2531 + difference 5 4) sourceC2531) = raw34937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34937; decide +kernel
    rw [ha]
    exact (canonical34937 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2531 + difference 5 0) (sourceB2531 + difference 0 5) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2301) := by
    have ha : (tripleCharges (sourceA2531 + difference 5 0) (sourceB2531 + difference 0 5) sourceC2531) = raw27855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw27855; decide +kernel
    rw [ha]
    exact (canonical27855 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2531 + difference 5 1) (sourceB2531 + difference 1 5) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1788) := by
    have ha : (tripleCharges (sourceA2531 + difference 5 1) (sourceB2531 + difference 1 5) sourceC2531) = raw34938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34938; decide +kernel
    rw [ha]
    exact (canonical34938 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2531 + difference 5 2) (sourceB2531 + difference 2 5) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2298) := by
    have ha : (tripleCharges (sourceA2531 + difference 5 2) (sourceB2531 + difference 2 5) sourceC2531) = raw34939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34939; decide +kernel
    rw [ha]
    exact (canonical34939 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2531 + difference 5 3) (sourceB2531 + difference 3 5) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2313) := by
    have ha : (tripleCharges (sourceA2531 + difference 5 3) (sourceB2531 + difference 3 5) sourceC2531) = raw34940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw34940; decide +kernel
    rw [ha]
    exact (canonical34940 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2531 + difference 5 4) (sourceB2531 + difference 4 5) sourceC2531) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2531 + difference 5 4) (sourceB2531 + difference 4 5) sourceC2531) = raw15057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2531 sourceB2531 sourceC2531 difference raw15057; decide +kernel
    rw [ha]
    exact (canonical15057 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2531 sourceB2531 sourceC2531
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2531, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2532 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2532 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2532 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm2532 : Integer.Sparse Master := [(Sum.inr 4668, 1), (Sum.inr 4669, 1), (Sum.inr 4670, 1), (Sum.inr 4690, 1), (Sum.inr 4856, 1), (Sum.inr 4931, 1), (Sum.inr 4934, 1), (Sum.inr 4949, 1), (Sum.inr 4955, 1), (Sum.inr 4957, 1), (Sum.inr 4959, 1), (Sum.inr 4966, 1), (Sum.inr 4973, 1), (Sum.inr 5080, 1), (Sum.inr 5141, 1), (Sum.inr 5188, 1), (Sum.inr 5336, 1), (Sum.inr 5339, 1), (Sum.inr 5351, 1), (Sum.inr 5353, 1), (Sum.inr 5367, 1), (Sum.inr 5370, 1), (Sum.inr 5378, 1), (Sum.inr 5379, 1), (Sum.inr 5384, 1), (Sum.inr 5385, 1), (Sum.inr 5409, 1), (Sum.inr 5411, 1), (Sum.inr 5428, 1), (Sum.inr 5446, 1)]

theorem sourceEq2532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2532 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 1) (sourceB2532 + difference 1 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 1) (sourceB2532 + difference 1 0) sourceC2532) = raw34941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34941; decide +kernel
    rw [ha]
    exact (canonical34941 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 2) (sourceB2532 + difference 2 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 2) (sourceB2532 + difference 2 0) sourceC2532) = raw34942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34942; decide +kernel
    rw [ha]
    exact (canonical34942 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 3) (sourceB2532 + difference 3 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 3) (sourceB2532 + difference 3 0) sourceC2532) = raw34943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34943; decide +kernel
    rw [ha]
    exact (canonical34943 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 4) (sourceB2532 + difference 4 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 4) (sourceB2532 + difference 4 0) sourceC2532) = raw16442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16442; decide +kernel
    rw [ha]
    exact (canonical16442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 5) (sourceB2532 + difference 5 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 5) (sourceB2532 + difference 5 0) sourceC2532) = raw34944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34944; decide +kernel
    rw [ha]
    exact (canonical34944 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 0) (sourceB2532 + difference 0 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 0) (sourceB2532 + difference 0 1) sourceC2532) = raw16462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16462; decide +kernel
    rw [ha]
    exact (canonical16462 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 2) (sourceB2532 + difference 2 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 2) (sourceB2532 + difference 2 1) sourceC2532) = raw16464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16464; decide +kernel
    rw [ha]
    exact (canonical16464 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 3) (sourceB2532 + difference 3 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 3) (sourceB2532 + difference 3 1) sourceC2532) = raw16465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16465; decide +kernel
    rw [ha]
    exact (canonical16465 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 4) (sourceB2532 + difference 4 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 4) (sourceB2532 + difference 4 1) sourceC2532) = raw34945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34945; decide +kernel
    rw [ha]
    exact (canonical34945 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 5) (sourceB2532 + difference 5 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 5) (sourceB2532 + difference 5 1) sourceC2532) = raw16466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16466; decide +kernel
    rw [ha]
    exact (canonical16466 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 0) (sourceB2532 + difference 0 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4668) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 0) (sourceB2532 + difference 0 2) sourceC2532) = raw34946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34946; decide +kernel
    rw [ha]
    exact (canonical34946 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 1) (sourceB2532 + difference 1 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4955) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 1) (sourceB2532 + difference 1 2) sourceC2532) = raw34947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34947; decide +kernel
    rw [ha]
    exact (canonical34947 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 3) (sourceB2532 + difference 3 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 3) (sourceB2532 + difference 3 2) sourceC2532) = raw34948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34948; decide +kernel
    rw [ha]
    exact (canonical34948 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 4) (sourceB2532 + difference 4 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 4) (sourceB2532 + difference 4 2) sourceC2532) = raw16453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16453; decide +kernel
    rw [ha]
    exact (canonical16453 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 5) (sourceB2532 + difference 5 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 5) (sourceB2532 + difference 5 2) sourceC2532) = raw34949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34949; decide +kernel
    rw [ha]
    exact (canonical34949 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 0) (sourceB2532 + difference 0 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4690) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 0) (sourceB2532 + difference 0 3) sourceC2532) = raw34950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34950; decide +kernel
    rw [ha]
    exact (canonical34950 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 1) (sourceB2532 + difference 1 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4966) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 1) (sourceB2532 + difference 1 3) sourceC2532) = raw34951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34951; decide +kernel
    rw [ha]
    exact (canonical34951 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 2) (sourceB2532 + difference 2 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5339) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 2) (sourceB2532 + difference 2 3) sourceC2532) = raw34952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34952; decide +kernel
    rw [ha]
    exact (canonical34952 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 4) (sourceB2532 + difference 4 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 4) (sourceB2532 + difference 4 3) sourceC2532) = raw16458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16458; decide +kernel
    rw [ha]
    exact (canonical16458 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 5) (sourceB2532 + difference 5 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 5) (sourceB2532 + difference 5 3) sourceC2532) = raw34953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34953; decide +kernel
    rw [ha]
    exact (canonical34953 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 0) (sourceB2532 + difference 0 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4670) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 0) (sourceB2532 + difference 0 4) sourceC2532) = raw34954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34954; decide +kernel
    rw [ha]
    exact (canonical34954 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 1) (sourceB2532 + difference 1 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 1) (sourceB2532 + difference 1 4) sourceC2532) = raw34955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34955; decide +kernel
    rw [ha]
    exact (canonical34955 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 2) (sourceB2532 + difference 2 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 2) (sourceB2532 + difference 2 4) sourceC2532) = raw34956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34956; decide +kernel
    rw [ha]
    exact (canonical34956 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 3) (sourceB2532 + difference 3 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 3) (sourceB2532 + difference 3 4) sourceC2532) = raw34957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34957; decide +kernel
    rw [ha]
    exact (canonical34957 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 5) (sourceB2532 + difference 5 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 5) (sourceB2532 + difference 5 4) sourceC2532) = raw34958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34958; decide +kernel
    rw [ha]
    exact (canonical34958 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 0) (sourceB2532 + difference 0 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4669) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 0) (sourceB2532 + difference 0 5) sourceC2532) = raw34959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34959; decide +kernel
    rw [ha]
    exact (canonical34959 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 1) (sourceB2532 + difference 1 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4959) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 1) (sourceB2532 + difference 1 5) sourceC2532) = raw34960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34960; decide +kernel
    rw [ha]
    exact (canonical34960 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 2) (sourceB2532 + difference 2 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4957) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 2) (sourceB2532 + difference 2 5) sourceC2532) = raw34961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34961; decide +kernel
    rw [ha]
    exact (canonical34961 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 3) (sourceB2532 + difference 3 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 3) (sourceB2532 + difference 3 5) sourceC2532) = raw34962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34962; decide +kernel
    rw [ha]
    exact (canonical34962 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 4) (sourceB2532 + difference 4 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 4) (sourceB2532 + difference 4 5) sourceC2532) = raw16468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16468; decide +kernel
    rw [ha]
    exact (canonical16468 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2532 sourceB2532 sourceC2532
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2532, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2533 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2533 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2533 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm2533 : Integer.Sparse Master := [(Sum.inr 1794, 1), (Sum.inr 1795, 1), (Sum.inr 1796, 1), (Sum.inr 1816, 1), (Sum.inr 2094, 1), (Sum.inr 2350, 1), (Sum.inr 2352, 1), (Sum.inr 2359, 1), (Sum.inr 2620, 1), (Sum.inr 2801, 1), (Sum.inr 2802, 1), (Sum.inr 2819, 1), (Sum.inr 2824, 1), (Sum.inr 2829, 1), (Sum.inr 2943, 1), (Sum.inr 2990, 1), (Sum.inr 3710, 1), (Sum.inr 3711, 1), (Sum.inr 3724, 1), (Sum.inr 3727, 1), (Sum.inr 3733, 1), (Sum.inr 3738, 1), (Sum.inr 3783, 1), (Sum.inr 3831, 1), (Sum.inr 3881, 1), (Sum.inr 3883, 1), (Sum.inr 3937, 1), (Sum.inr 3941, 1), (Sum.inr 4003, 1), (Sum.inr 4035, 1)]

theorem sourceEq2533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2533 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2533 + difference 0 1) (sourceB2533 + difference 1 0) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA2533 + difference 0 1) (sourceB2533 + difference 1 0) sourceC2533) = raw34963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34963; decide +kernel
    rw [ha]
    exact (canonical34963 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2533 + difference 0 2) (sourceB2533 + difference 2 0) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3937) := by
    have ha : (tripleCharges (sourceA2533 + difference 0 2) (sourceB2533 + difference 2 0) sourceC2533) = raw34964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34964; decide +kernel
    rw [ha]
    exact (canonical34964 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2533 + difference 0 3) (sourceB2533 + difference 3 0) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3941) := by
    have ha : (tripleCharges (sourceA2533 + difference 0 3) (sourceB2533 + difference 3 0) sourceC2533) = raw34965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34965; decide +kernel
    rw [ha]
    exact (canonical34965 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2533 + difference 0 4) (sourceB2533 + difference 4 0) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA2533 + difference 0 4) (sourceB2533 + difference 4 0) sourceC2533) = raw16472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw16472; decide +kernel
    rw [ha]
    exact (canonical16472 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2533 + difference 0 5) (sourceB2533 + difference 5 0) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4035) := by
    have ha : (tripleCharges (sourceA2533 + difference 0 5) (sourceB2533 + difference 5 0) sourceC2533) = raw34966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34966; decide +kernel
    rw [ha]
    exact (canonical34966 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2533 + difference 1 0) (sourceB2533 + difference 0 1) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA2533 + difference 1 0) (sourceB2533 + difference 0 1) sourceC2533) = raw16492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw16492; decide +kernel
    rw [ha]
    exact (canonical16492 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2533 + difference 1 2) (sourceB2533 + difference 2 1) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA2533 + difference 1 2) (sourceB2533 + difference 2 1) sourceC2533) = raw16494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw16494; decide +kernel
    rw [ha]
    exact (canonical16494 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2533 + difference 1 3) (sourceB2533 + difference 3 1) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3831) := by
    have ha : (tripleCharges (sourceA2533 + difference 1 3) (sourceB2533 + difference 3 1) sourceC2533) = raw16495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw16495; decide +kernel
    rw [ha]
    exact (canonical16495 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2533 + difference 1 4) (sourceB2533 + difference 4 1) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA2533 + difference 1 4) (sourceB2533 + difference 4 1) sourceC2533) = raw34967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34967; decide +kernel
    rw [ha]
    exact (canonical34967 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2533 + difference 1 5) (sourceB2533 + difference 5 1) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA2533 + difference 1 5) (sourceB2533 + difference 5 1) sourceC2533) = raw16496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw16496; decide +kernel
    rw [ha]
    exact (canonical16496 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2533 + difference 2 0) (sourceB2533 + difference 0 2) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1794) := by
    have ha : (tripleCharges (sourceA2533 + difference 2 0) (sourceB2533 + difference 0 2) sourceC2533) = raw34968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34968; decide +kernel
    rw [ha]
    exact (canonical34968 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2533 + difference 2 1) (sourceB2533 + difference 1 2) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2801) := by
    have ha : (tripleCharges (sourceA2533 + difference 2 1) (sourceB2533 + difference 1 2) sourceC2533) = raw34969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34969; decide +kernel
    rw [ha]
    exact (canonical34969 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2533 + difference 2 3) (sourceB2533 + difference 3 2) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3711) := by
    have ha : (tripleCharges (sourceA2533 + difference 2 3) (sourceB2533 + difference 3 2) sourceC2533) = raw34970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34970; decide +kernel
    rw [ha]
    exact (canonical34970 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2533 + difference 2 4) (sourceB2533 + difference 4 2) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA2533 + difference 2 4) (sourceB2533 + difference 4 2) sourceC2533) = raw16483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw16483; decide +kernel
    rw [ha]
    exact (canonical16483 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2533 + difference 2 5) (sourceB2533 + difference 5 2) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3727) := by
    have ha : (tripleCharges (sourceA2533 + difference 2 5) (sourceB2533 + difference 5 2) sourceC2533) = raw34971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34971; decide +kernel
    rw [ha]
    exact (canonical34971 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2533 + difference 3 0) (sourceB2533 + difference 0 3) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1816) := by
    have ha : (tripleCharges (sourceA2533 + difference 3 0) (sourceB2533 + difference 0 3) sourceC2533) = raw34972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34972; decide +kernel
    rw [ha]
    exact (canonical34972 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2533 + difference 3 1) (sourceB2533 + difference 1 3) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2819) := by
    have ha : (tripleCharges (sourceA2533 + difference 3 1) (sourceB2533 + difference 1 3) sourceC2533) = raw34973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34973; decide +kernel
    rw [ha]
    exact (canonical34973 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2533 + difference 3 2) (sourceB2533 + difference 2 3) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3710) := by
    have ha : (tripleCharges (sourceA2533 + difference 3 2) (sourceB2533 + difference 2 3) sourceC2533) = raw34974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34974; decide +kernel
    rw [ha]
    exact (canonical34974 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2533 + difference 3 4) (sourceB2533 + difference 4 3) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA2533 + difference 3 4) (sourceB2533 + difference 4 3) sourceC2533) = raw16488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw16488; decide +kernel
    rw [ha]
    exact (canonical16488 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2533 + difference 3 5) (sourceB2533 + difference 5 3) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3738) := by
    have ha : (tripleCharges (sourceA2533 + difference 3 5) (sourceB2533 + difference 5 3) sourceC2533) = raw34975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34975; decide +kernel
    rw [ha]
    exact (canonical34975 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2533 + difference 4 0) (sourceB2533 + difference 0 4) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1796) := by
    have ha : (tripleCharges (sourceA2533 + difference 4 0) (sourceB2533 + difference 0 4) sourceC2533) = raw34976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34976; decide +kernel
    rw [ha]
    exact (canonical34976 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2533 + difference 4 1) (sourceB2533 + difference 1 4) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA2533 + difference 4 1) (sourceB2533 + difference 1 4) sourceC2533) = raw34977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34977; decide +kernel
    rw [ha]
    exact (canonical34977 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2533 + difference 4 2) (sourceB2533 + difference 2 4) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2824) := by
    have ha : (tripleCharges (sourceA2533 + difference 4 2) (sourceB2533 + difference 2 4) sourceC2533) = raw34978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34978; decide +kernel
    rw [ha]
    exact (canonical34978 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2533 + difference 4 3) (sourceB2533 + difference 3 4) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2829) := by
    have ha : (tripleCharges (sourceA2533 + difference 4 3) (sourceB2533 + difference 3 4) sourceC2533) = raw34979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34979; decide +kernel
    rw [ha]
    exact (canonical34979 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2533 + difference 4 5) (sourceB2533 + difference 5 4) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2990) := by
    have ha : (tripleCharges (sourceA2533 + difference 4 5) (sourceB2533 + difference 5 4) sourceC2533) = raw34980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34980; decide +kernel
    rw [ha]
    exact (canonical34980 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2533 + difference 5 0) (sourceB2533 + difference 0 5) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1795) := by
    have ha : (tripleCharges (sourceA2533 + difference 5 0) (sourceB2533 + difference 0 5) sourceC2533) = raw34981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34981; decide +kernel
    rw [ha]
    exact (canonical34981 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2533 + difference 5 1) (sourceB2533 + difference 1 5) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2352) := by
    have ha : (tripleCharges (sourceA2533 + difference 5 1) (sourceB2533 + difference 1 5) sourceC2533) = raw34982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34982; decide +kernel
    rw [ha]
    exact (canonical34982 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2533 + difference 5 2) (sourceB2533 + difference 2 5) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2350) := by
    have ha : (tripleCharges (sourceA2533 + difference 5 2) (sourceB2533 + difference 2 5) sourceC2533) = raw34983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34983; decide +kernel
    rw [ha]
    exact (canonical34983 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2533 + difference 5 3) (sourceB2533 + difference 3 5) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2359) := by
    have ha : (tripleCharges (sourceA2533 + difference 5 3) (sourceB2533 + difference 3 5) sourceC2533) = raw34984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw34984; decide +kernel
    rw [ha]
    exact (canonical34984 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2533 + difference 5 4) (sourceB2533 + difference 4 5) sourceC2533) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA2533 + difference 5 4) (sourceB2533 + difference 4 5) sourceC2533) = raw16498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2533 sourceB2533 sourceC2533 difference raw16498; decide +kernel
    rw [ha]
    exact (canonical16498 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2533 sourceB2533 sourceC2533
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2533, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2534 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2534 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2534 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm2534 : Integer.Sparse Master := [(Sum.inr 2154, 1), (Sum.inr 2155, 1), (Sum.inr 2158, 1), (Sum.inr 2164, 1), (Sum.inr 2274, 1), (Sum.inr 3406, 1), (Sum.inr 3415, 1), (Sum.inr 3417, 1), (Sum.inr 3478, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3512, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3555, 1), (Sum.inr 3591, 1), (Sum.inr 3754, 1), (Sum.inr 3757, 1), (Sum.inr 3760, 1), (Sum.inr 3761, 1), (Sum.inr 3766, 1), (Sum.inr 3771, 1), (Sum.inr 3795, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3845, 1), (Sum.inr 3868, 1), (Sum.inr 3884, 1)]

theorem sourceEq2534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2534 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 1) (sourceB2534 + difference 1 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 1) (sourceB2534 + difference 1 0) sourceC2534) = raw34985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34985; decide +kernel
    rw [ha]
    exact (canonical34985 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 2) (sourceB2534 + difference 2 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 2) (sourceB2534 + difference 2 0) sourceC2534) = raw34986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34986; decide +kernel
    rw [ha]
    exact (canonical34986 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 3) (sourceB2534 + difference 3 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 3) (sourceB2534 + difference 3 0) sourceC2534) = raw34987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34987; decide +kernel
    rw [ha]
    exact (canonical34987 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 4) (sourceB2534 + difference 4 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 4) (sourceB2534 + difference 4 0) sourceC2534) = raw16502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16502; decide +kernel
    rw [ha]
    exact (canonical16502 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 5) (sourceB2534 + difference 5 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 5) (sourceB2534 + difference 5 0) sourceC2534) = raw34988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34988; decide +kernel
    rw [ha]
    exact (canonical34988 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 0) (sourceB2534 + difference 0 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 0) (sourceB2534 + difference 0 1) sourceC2534) = raw16522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16522; decide +kernel
    rw [ha]
    exact (canonical16522 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 2) (sourceB2534 + difference 2 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 2) (sourceB2534 + difference 2 1) sourceC2534) = raw16524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16524; decide +kernel
    rw [ha]
    exact (canonical16524 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 3) (sourceB2534 + difference 3 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 3) (sourceB2534 + difference 3 1) sourceC2534) = raw16525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16525; decide +kernel
    rw [ha]
    exact (canonical16525 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 4) (sourceB2534 + difference 4 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 4) (sourceB2534 + difference 4 1) sourceC2534) = raw34989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34989; decide +kernel
    rw [ha]
    exact (canonical34989 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 5) (sourceB2534 + difference 5 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 5) (sourceB2534 + difference 5 1) sourceC2534) = raw16526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16526; decide +kernel
    rw [ha]
    exact (canonical16526 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 0) (sourceB2534 + difference 0 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 0) (sourceB2534 + difference 0 2) sourceC2534) = raw34990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34990; decide +kernel
    rw [ha]
    exact (canonical34990 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 1) (sourceB2534 + difference 1 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 1) (sourceB2534 + difference 1 2) sourceC2534) = raw34991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34991; decide +kernel
    rw [ha]
    exact (canonical34991 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 3) (sourceB2534 + difference 3 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3754) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 3) (sourceB2534 + difference 3 2) sourceC2534) = raw34992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34992; decide +kernel
    rw [ha]
    exact (canonical34992 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 4) (sourceB2534 + difference 4 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 4) (sourceB2534 + difference 4 2) sourceC2534) = raw16513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16513; decide +kernel
    rw [ha]
    exact (canonical16513 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 5) (sourceB2534 + difference 5 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 5) (sourceB2534 + difference 5 2) sourceC2534) = raw34993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34993; decide +kernel
    rw [ha]
    exact (canonical34993 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 0) (sourceB2534 + difference 0 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 0) (sourceB2534 + difference 0 3) sourceC2534) = raw34994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34994; decide +kernel
    rw [ha]
    exact (canonical34994 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 1) (sourceB2534 + difference 1 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 1) (sourceB2534 + difference 1 3) sourceC2534) = raw34995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34995; decide +kernel
    rw [ha]
    exact (canonical34995 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 2) (sourceB2534 + difference 2 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3760) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 2) (sourceB2534 + difference 2 3) sourceC2534) = raw34996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34996; decide +kernel
    rw [ha]
    exact (canonical34996 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 4) (sourceB2534 + difference 4 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 4) (sourceB2534 + difference 4 3) sourceC2534) = raw16518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16518; decide +kernel
    rw [ha]
    exact (canonical16518 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 5) (sourceB2534 + difference 5 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 5) (sourceB2534 + difference 5 3) sourceC2534) = raw34997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34997; decide +kernel
    rw [ha]
    exact (canonical34997 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 0) (sourceB2534 + difference 0 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 0) (sourceB2534 + difference 0 4) sourceC2534) = raw34998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34998; decide +kernel
    rw [ha]
    exact (canonical34998 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 1) (sourceB2534 + difference 1 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 1) (sourceB2534 + difference 1 4) sourceC2534) = raw34999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34999; decide +kernel
    rw [ha]
    exact (canonical34999 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 2) (sourceB2534 + difference 2 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 2) (sourceB2534 + difference 2 4) sourceC2534) = raw35000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35000; decide +kernel
    rw [ha]
    exact (canonical35000 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 3) (sourceB2534 + difference 3 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 3) (sourceB2534 + difference 3 4) sourceC2534) = raw35001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35001; decide +kernel
    rw [ha]
    exact (canonical35001 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 5) (sourceB2534 + difference 5 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 5) (sourceB2534 + difference 5 4) sourceC2534) = raw35002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35002; decide +kernel
    rw [ha]
    exact (canonical35002 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 0) (sourceB2534 + difference 0 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 0) (sourceB2534 + difference 0 5) sourceC2534) = raw35003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35003; decide +kernel
    rw [ha]
    exact (canonical35003 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 1) (sourceB2534 + difference 1 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3512) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 1) (sourceB2534 + difference 1 5) sourceC2534) = raw35004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35004; decide +kernel
    rw [ha]
    exact (canonical35004 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 2) (sourceB2534 + difference 2 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 2) (sourceB2534 + difference 2 5) sourceC2534) = raw35005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35005; decide +kernel
    rw [ha]
    exact (canonical35005 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 3) (sourceB2534 + difference 3 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 3) (sourceB2534 + difference 3 5) sourceC2534) = raw35006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35006; decide +kernel
    rw [ha]
    exact (canonical35006 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 4) (sourceB2534 + difference 4 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 4) (sourceB2534 + difference 4 5) sourceC2534) = raw16528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16528; decide +kernel
    rw [ha]
    exact (canonical16528 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2534 sourceB2534 sourceC2534
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2534, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2535 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2535 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2535 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm2535 : Integer.Sparse Master := [(Sum.inr 2348, 1), (Sum.inr 3133, 1), (Sum.inr 3671, 1), (Sum.inr 3693, 1), (Sum.inr 3719, 1), (Sum.inr 3720, 1), (Sum.inr 4092, -1)]

theorem sourceEq2535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2535 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 0) (sourceB2535 + difference 0 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3133) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 0) (sourceB2535 + difference 0 2) sourceC2535) = raw29347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw29347; decide +kernel
    rw [ha]
    exact (canonical29347 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 1) (sourceB2535 + difference 1 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2348) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 1) (sourceB2535 + difference 1 2) sourceC2535) = raw35007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw35007; decide +kernel
    rw [ha]
    exact (canonical35007 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 2) (sourceB2535 + difference 2 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 2) (sourceB2535 + difference 2 2) sourceC2535) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 3) (sourceB2535 + difference 3 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3671) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 3) (sourceB2535 + difference 3 2) sourceC2535) = raw35008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw35008; decide +kernel
    rw [ha]
    exact (canonical35008 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 4) (sourceB2535 + difference 4 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 4) (sourceB2535 + difference 4 2) sourceC2535) = raw16540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw16540; decide +kernel
    rw [ha]
    exact (canonical16540 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 5) (sourceB2535 + difference 5 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 5) (sourceB2535 + difference 5 2) sourceC2535) = raw35009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw35009; decide +kernel
    rw [ha]
    exact (canonical35009 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2535 + sourceB2535) sourceC2535) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2535 + sourceB2535) sourceC2535) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA2535 sourceB2535 sourceC2535 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2535 sourceB2535 sourceC2535
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2535, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2536 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2536 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2536 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm2536 : Integer.Sparse Master := [(Sum.inr 2321, 1), (Sum.inr 2798, 1), (Sum.inr 3674, 1), (Sum.inr 3689, 1), (Sum.inr 3691, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem sourceEq2536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2536 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2536 + difference 0 2) (sourceB2536 + difference 2 0) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA2536 + difference 0 2) (sourceB2536 + difference 2 0) sourceC2536) = raw35010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw35010; decide +kernel
    rw [ha]
    exact (canonical35010 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2536 + difference 1 2) (sourceB2536 + difference 2 1) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA2536 + difference 1 2) (sourceB2536 + difference 2 1) sourceC2536) = raw16550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw16550; decide +kernel
    rw [ha]
    exact (canonical16550 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2536 + difference 2 2) (sourceB2536 + difference 2 2) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2536 + difference 2 2) (sourceB2536 + difference 2 2) sourceC2536) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2536 + difference 3 2) (sourceB2536 + difference 2 3) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3674) := by
    have ha : (tripleCharges (sourceA2536 + difference 3 2) (sourceB2536 + difference 2 3) sourceC2536) = raw35011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw35011; decide +kernel
    rw [ha]
    exact (canonical35011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2536 + difference 4 2) (sourceB2536 + difference 2 4) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2321) := by
    have ha : (tripleCharges (sourceA2536 + difference 4 2) (sourceB2536 + difference 2 4) sourceC2536) = raw35012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw35012; decide +kernel
    rw [ha]
    exact (canonical35012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2536 + difference 5 2) (sourceB2536 + difference 2 5) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2798) := by
    have ha : (tripleCharges (sourceA2536 + difference 5 2) (sourceB2536 + difference 2 5) sourceC2536) = raw35013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw35013; decide +kernel
    rw [ha]
    exact (canonical35013 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2536 + sourceB2536) sourceC2536) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2536 + sourceB2536) sourceC2536) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA2536 sourceB2536 sourceC2536 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2536 sourceB2536 sourceC2536
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2536, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2537 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2537 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2537 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm2537 : Integer.Sparse Master := [(Sum.inr 2356, 1), (Sum.inr 3138, 1), (Sum.inr 3674, 1), (Sum.inr 3693, 1), (Sum.inr 3732, 1), (Sum.inr 3733, 1), (Sum.inr 4092, -1)]

theorem sourceEq2537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2537 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 0) (sourceB2537 + difference 0 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3138) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 0) (sourceB2537 + difference 0 3) sourceC2537) = raw29348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw29348; decide +kernel
    rw [ha]
    exact (canonical29348 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 1) (sourceB2537 + difference 1 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2356) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 1) (sourceB2537 + difference 1 3) sourceC2537) = raw35014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw35014; decide +kernel
    rw [ha]
    exact (canonical35014 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 2) (sourceB2537 + difference 2 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3674) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 2) (sourceB2537 + difference 2 3) sourceC2537) = raw35011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw35011; decide +kernel
    rw [ha]
    exact (canonical35011 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 3) (sourceB2537 + difference 3 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 3) (sourceB2537 + difference 3 3) sourceC2537) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 4) (sourceB2537 + difference 4 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 4) (sourceB2537 + difference 4 3) sourceC2537) = raw16541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw16541; decide +kernel
    rw [ha]
    exact (canonical16541 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 5) (sourceB2537 + difference 5 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 5) (sourceB2537 + difference 5 3) sourceC2537) = raw35015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw35015; decide +kernel
    rw [ha]
    exact (canonical35015 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2537 + sourceB2537) sourceC2537) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2537 + sourceB2537) sourceC2537) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA2537 sourceB2537 sourceC2537 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2537 sourceB2537 sourceC2537
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2537, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2538 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2538 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2538 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceForm2538 : Integer.Sparse Master := [(Sum.inr 5004, 1), (Sum.inr 5006, 1), (Sum.inr 5009, 1), (Sum.inr 5015, 1), (Sum.inr 5122, 1), (Sum.inr 5125, 1), (Sum.inr 5158, 1), (Sum.inr 5230, 1), (Sum.inr 5232, 2), (Sum.inr 5234, 1), (Sum.inr 5236, 1), (Sum.inr 5238, 1), (Sum.inr 5320, 1), (Sum.inr 5327, 1), (Sum.inr 5329, 1), (Sum.inr 5341, 1), (Sum.inr 5342, 1), (Sum.inr 5348, 1), (Sum.inr 5355, 3), (Sum.inr 5356, 2), (Sum.inr 5361, 1), (Sum.inr 5371, 1), (Sum.inr 5376, 1), (Sum.inr 5377, 1), (Sum.inr 5389, 1), (Sum.inr 5390, 1)]

theorem sourceEq2538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2538 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2538 + difference 0 1) (sourceB2538 + difference 1 0) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2538 + difference 0 1) (sourceB2538 + difference 1 0) sourceC2538) = raw35016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35016; decide +kernel
    rw [ha]
    exact (canonical35016 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2538 + difference 0 2) (sourceB2538 + difference 2 0) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2538 + difference 0 2) (sourceB2538 + difference 2 0) sourceC2538) = raw35017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35017; decide +kernel
    rw [ha]
    exact (canonical35017 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2538 + difference 0 3) (sourceB2538 + difference 3 0) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2538 + difference 0 3) (sourceB2538 + difference 3 0) sourceC2538) = raw34821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34821; decide +kernel
    rw [ha]
    exact (canonical34821 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2538 + difference 0 4) (sourceB2538 + difference 4 0) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2538 + difference 0 4) (sourceB2538 + difference 4 0) sourceC2538) = raw35018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35018; decide +kernel
    rw [ha]
    exact (canonical35018 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2538 + difference 0 5) (sourceB2538 + difference 5 0) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2538 + difference 0 5) (sourceB2538 + difference 5 0) sourceC2538) = raw35019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35019; decide +kernel
    rw [ha]
    exact (canonical35019 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2538 + difference 1 0) (sourceB2538 + difference 0 1) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5158) := by
    have ha : (tripleCharges (sourceA2538 + difference 1 0) (sourceB2538 + difference 0 1) sourceC2538) = raw35020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35020; decide +kernel
    rw [ha]
    exact (canonical35020 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2538 + difference 1 2) (sourceB2538 + difference 2 1) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5122) := by
    have ha : (tripleCharges (sourceA2538 + difference 1 2) (sourceB2538 + difference 2 1) sourceC2538) = raw35021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35021; decide +kernel
    rw [ha]
    exact (canonical35021 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2538 + difference 1 3) (sourceB2538 + difference 3 1) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2538 + difference 1 3) (sourceB2538 + difference 3 1) sourceC2538) = raw34826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34826; decide +kernel
    rw [ha]
    exact (canonical34826 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2538 + difference 1 4) (sourceB2538 + difference 4 1) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5006) := by
    have ha : (tripleCharges (sourceA2538 + difference 1 4) (sourceB2538 + difference 4 1) sourceC2538) = raw35022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35022; decide +kernel
    rw [ha]
    exact (canonical35022 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2538 + difference 1 5) (sourceB2538 + difference 5 1) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2538 + difference 1 5) (sourceB2538 + difference 5 1) sourceC2538) = raw35023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35023; decide +kernel
    rw [ha]
    exact (canonical35023 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2538 + difference 2 0) (sourceB2538 + difference 0 2) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5230) := by
    have ha : (tripleCharges (sourceA2538 + difference 2 0) (sourceB2538 + difference 0 2) sourceC2538) = raw35024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35024; decide +kernel
    rw [ha]
    exact (canonical35024 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2538 + difference 2 1) (sourceB2538 + difference 1 2) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA2538 + difference 2 1) (sourceB2538 + difference 1 2) sourceC2538) = raw35025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35025; decide +kernel
    rw [ha]
    exact (canonical35025 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2538 + difference 2 3) (sourceB2538 + difference 3 2) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2538 + difference 2 3) (sourceB2538 + difference 3 2) sourceC2538) = raw34831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34831; decide +kernel
    rw [ha]
    exact (canonical34831 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2538 + difference 2 4) (sourceB2538 + difference 4 2) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5004) := by
    have ha : (tripleCharges (sourceA2538 + difference 2 4) (sourceB2538 + difference 4 2) sourceC2538) = raw35026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35026; decide +kernel
    rw [ha]
    exact (canonical35026 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2538 + difference 2 5) (sourceB2538 + difference 5 2) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5320) := by
    have ha : (tripleCharges (sourceA2538 + difference 2 5) (sourceB2538 + difference 5 2) sourceC2538) = raw35027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35027; decide +kernel
    rw [ha]
    exact (canonical35027 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2538 + difference 3 0) (sourceB2538 + difference 0 3) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5234) := by
    have ha : (tripleCharges (sourceA2538 + difference 3 0) (sourceB2538 + difference 0 3) sourceC2538) = raw35028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35028; decide +kernel
    rw [ha]
    exact (canonical35028 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2538 + difference 3 1) (sourceB2538 + difference 1 3) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA2538 + difference 3 1) (sourceB2538 + difference 1 3) sourceC2538) = raw35029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35029; decide +kernel
    rw [ha]
    exact (canonical35029 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2538 + difference 3 2) (sourceB2538 + difference 2 3) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5342) := by
    have ha : (tripleCharges (sourceA2538 + difference 3 2) (sourceB2538 + difference 2 3) sourceC2538) = raw35030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35030; decide +kernel
    rw [ha]
    exact (canonical35030 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2538 + difference 3 4) (sourceB2538 + difference 4 3) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5009) := by
    have ha : (tripleCharges (sourceA2538 + difference 3 4) (sourceB2538 + difference 4 3) sourceC2538) = raw35031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35031; decide +kernel
    rw [ha]
    exact (canonical35031 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2538 + difference 3 5) (sourceB2538 + difference 5 3) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5329) := by
    have ha : (tripleCharges (sourceA2538 + difference 3 5) (sourceB2538 + difference 5 3) sourceC2538) = raw35032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw35032; decide +kernel
    rw [ha]
    exact (canonical35032 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2538 + difference 4 0) (sourceB2538 + difference 0 4) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2538 + difference 4 0) (sourceB2538 + difference 0 4) sourceC2538) = raw34897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34897; decide +kernel
    rw [ha]
    exact (canonical34897 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2538 + difference 4 1) (sourceB2538 + difference 1 4) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2538 + difference 4 1) (sourceB2538 + difference 1 4) sourceC2538) = raw34898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34898; decide +kernel
    rw [ha]
    exact (canonical34898 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2538 + difference 4 2) (sourceB2538 + difference 2 4) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA2538 + difference 4 2) (sourceB2538 + difference 2 4) sourceC2538) = raw34899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34899; decide +kernel
    rw [ha]
    exact (canonical34899 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2538 + difference 4 3) (sourceB2538 + difference 3 4) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2538 + difference 4 3) (sourceB2538 + difference 3 4) sourceC2538) = raw34841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34841; decide +kernel
    rw [ha]
    exact (canonical34841 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2538 + difference 4 5) (sourceB2538 + difference 5 4) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2538 + difference 4 5) (sourceB2538 + difference 5 4) sourceC2538) = raw34900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34900; decide +kernel
    rw [ha]
    exact (canonical34900 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2538 + difference 5 0) (sourceB2538 + difference 0 5) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2538 + difference 5 0) (sourceB2538 + difference 0 5) sourceC2538) = raw34832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34832; decide +kernel
    rw [ha]
    exact (canonical34832 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2538 + difference 5 1) (sourceB2538 + difference 1 5) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2538 + difference 5 1) (sourceB2538 + difference 1 5) sourceC2538) = raw34833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34833; decide +kernel
    rw [ha]
    exact (canonical34833 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2538 + difference 5 2) (sourceB2538 + difference 2 5) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5376) := by
    have ha : (tripleCharges (sourceA2538 + difference 5 2) (sourceB2538 + difference 2 5) sourceC2538) = raw34834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34834; decide +kernel
    rw [ha]
    exact (canonical34834 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2538 + difference 5 3) (sourceB2538 + difference 3 5) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2538 + difference 5 3) (sourceB2538 + difference 3 5) sourceC2538) = raw34906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34906; decide +kernel
    rw [ha]
    exact (canonical34906 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2538 + difference 5 4) (sourceB2538 + difference 4 5) sourceC2538) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2538 + difference 5 4) (sourceB2538 + difference 4 5) sourceC2538) = raw34835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2538 sourceB2538 sourceC2538 difference raw34835; decide +kernel
    rw [ha]
    exact (canonical34835 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2538 sourceB2538 sourceC2538
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2538, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2539 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2539 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2539 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceForm2539 : Integer.Sparse Master := [(Sum.inr 3041, 1), (Sum.inr 3042, 1), (Sum.inr 3045, 1), (Sum.inr 3047, 1), (Sum.inr 3115, 1), (Sum.inr 3337, 1), (Sum.inr 3343, 1), (Sum.inr 3344, 1), (Sum.inr 3348, 1), (Sum.inr 3367, 1), (Sum.inr 3372, 1), (Sum.inr 3379, 1), (Sum.inr 3397, 1), (Sum.inr 3646, 1), (Sum.inr 3654, 1), (Sum.inr 3660, 1), (Sum.inr 3678, 1), (Sum.inr 3679, 1), (Sum.inr 3685, 1), (Sum.inr 3693, 2), (Sum.inr 3694, 1), (Sum.inr 3699, 1), (Sum.inr 3707, 1), (Sum.inr 3715, 1), (Sum.inr 3716, 1), (Sum.inr 3728, 1), (Sum.inr 3740, 1), (Sum.inr 3741, 1), (Sum.inr 3926, 1)]

theorem sourceEq2539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2539 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2539 + difference 0 1) (sourceB2539 + difference 1 0) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2539 + difference 0 1) (sourceB2539 + difference 1 0) sourceC2539) = raw35033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35033; decide +kernel
    rw [ha]
    exact (canonical35033 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2539 + difference 0 2) (sourceB2539 + difference 2 0) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3678) := by
    have ha : (tripleCharges (sourceA2539 + difference 0 2) (sourceB2539 + difference 2 0) sourceC2539) = raw35034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35034; decide +kernel
    rw [ha]
    exact (canonical35034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2539 + difference 0 3) (sourceB2539 + difference 3 0) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3707) := by
    have ha : (tripleCharges (sourceA2539 + difference 0 3) (sourceB2539 + difference 3 0) sourceC2539) = raw35035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35035; decide +kernel
    rw [ha]
    exact (canonical35035 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2539 + difference 0 4) (sourceB2539 + difference 4 0) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3344) := by
    have ha : (tripleCharges (sourceA2539 + difference 0 4) (sourceB2539 + difference 4 0) sourceC2539) = raw35036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35036; decide +kernel
    rw [ha]
    exact (canonical35036 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2539 + difference 0 5) (sourceB2539 + difference 5 0) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3654) := by
    have ha : (tripleCharges (sourceA2539 + difference 0 5) (sourceB2539 + difference 5 0) sourceC2539) = raw35037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35037; decide +kernel
    rw [ha]
    exact (canonical35037 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2539 + difference 1 0) (sourceB2539 + difference 0 1) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3047) := by
    have ha : (tripleCharges (sourceA2539 + difference 1 0) (sourceB2539 + difference 0 1) sourceC2539) = raw35038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35038; decide +kernel
    rw [ha]
    exact (canonical35038 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2539 + difference 1 2) (sourceB2539 + difference 2 1) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3367) := by
    have ha : (tripleCharges (sourceA2539 + difference 1 2) (sourceB2539 + difference 2 1) sourceC2539) = raw35039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35039; decide +kernel
    rw [ha]
    exact (canonical35039 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2539 + difference 1 3) (sourceB2539 + difference 3 1) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2539 + difference 1 3) (sourceB2539 + difference 3 1) sourceC2539) = raw35040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35040; decide +kernel
    rw [ha]
    exact (canonical35040 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2539 + difference 1 4) (sourceB2539 + difference 4 1) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3343) := by
    have ha : (tripleCharges (sourceA2539 + difference 1 4) (sourceB2539 + difference 4 1) sourceC2539) = raw35041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35041; decide +kernel
    rw [ha]
    exact (canonical35041 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2539 + difference 1 5) (sourceB2539 + difference 5 1) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3372) := by
    have ha : (tripleCharges (sourceA2539 + difference 1 5) (sourceB2539 + difference 5 1) sourceC2539) = raw35042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35042; decide +kernel
    rw [ha]
    exact (canonical35042 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2539 + difference 2 0) (sourceB2539 + difference 0 2) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3041) := by
    have ha : (tripleCharges (sourceA2539 + difference 2 0) (sourceB2539 + difference 0 2) sourceC2539) = raw35043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35043; decide +kernel
    rw [ha]
    exact (canonical35043 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2539 + difference 2 1) (sourceB2539 + difference 1 2) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA2539 + difference 2 1) (sourceB2539 + difference 1 2) sourceC2539) = raw35044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35044; decide +kernel
    rw [ha]
    exact (canonical35044 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2539 + difference 2 3) (sourceB2539 + difference 3 2) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2539 + difference 2 3) (sourceB2539 + difference 3 2) sourceC2539) = raw35045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35045; decide +kernel
    rw [ha]
    exact (canonical35045 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2539 + difference 2 4) (sourceB2539 + difference 4 2) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3337) := by
    have ha : (tripleCharges (sourceA2539 + difference 2 4) (sourceB2539 + difference 4 2) sourceC2539) = raw35046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35046; decide +kernel
    rw [ha]
    exact (canonical35046 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2539 + difference 2 5) (sourceB2539 + difference 5 2) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3646) := by
    have ha : (tripleCharges (sourceA2539 + difference 2 5) (sourceB2539 + difference 5 2) sourceC2539) = raw35047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35047; decide +kernel
    rw [ha]
    exact (canonical35047 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2539 + difference 3 0) (sourceB2539 + difference 0 3) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3042) := by
    have ha : (tripleCharges (sourceA2539 + difference 3 0) (sourceB2539 + difference 0 3) sourceC2539) = raw35048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35048; decide +kernel
    rw [ha]
    exact (canonical35048 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2539 + difference 3 1) (sourceB2539 + difference 1 3) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3699) := by
    have ha : (tripleCharges (sourceA2539 + difference 3 1) (sourceB2539 + difference 1 3) sourceC2539) = raw35049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35049; decide +kernel
    rw [ha]
    exact (canonical35049 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2539 + difference 3 2) (sourceB2539 + difference 2 3) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3679) := by
    have ha : (tripleCharges (sourceA2539 + difference 3 2) (sourceB2539 + difference 2 3) sourceC2539) = raw35050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35050; decide +kernel
    rw [ha]
    exact (canonical35050 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2539 + difference 3 4) (sourceB2539 + difference 4 3) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3348) := by
    have ha : (tripleCharges (sourceA2539 + difference 3 4) (sourceB2539 + difference 4 3) sourceC2539) = raw35051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35051; decide +kernel
    rw [ha]
    exact (canonical35051 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2539 + difference 3 5) (sourceB2539 + difference 5 3) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3660) := by
    have ha : (tripleCharges (sourceA2539 + difference 3 5) (sourceB2539 + difference 5 3) sourceC2539) = raw35052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35052; decide +kernel
    rw [ha]
    exact (canonical35052 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2539 + difference 4 0) (sourceB2539 + difference 0 4) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3115) := by
    have ha : (tripleCharges (sourceA2539 + difference 4 0) (sourceB2539 + difference 0 4) sourceC2539) = raw35053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35053; decide +kernel
    rw [ha]
    exact (canonical35053 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2539 + difference 4 1) (sourceB2539 + difference 1 4) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3926) := by
    have ha : (tripleCharges (sourceA2539 + difference 4 1) (sourceB2539 + difference 1 4) sourceC2539) = raw35054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35054; decide +kernel
    rw [ha]
    exact (canonical35054 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2539 + difference 4 2) (sourceB2539 + difference 2 4) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3716) := by
    have ha : (tripleCharges (sourceA2539 + difference 4 2) (sourceB2539 + difference 2 4) sourceC2539) = raw35055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35055; decide +kernel
    rw [ha]
    exact (canonical35055 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2539 + difference 4 3) (sourceB2539 + difference 3 4) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3741) := by
    have ha : (tripleCharges (sourceA2539 + difference 4 3) (sourceB2539 + difference 3 4) sourceC2539) = raw35056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35056; decide +kernel
    rw [ha]
    exact (canonical35056 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2539 + difference 4 5) (sourceB2539 + difference 5 4) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2539 + difference 4 5) (sourceB2539 + difference 5 4) sourceC2539) = raw35057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35057; decide +kernel
    rw [ha]
    exact (canonical35057 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2539 + difference 5 0) (sourceB2539 + difference 0 5) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA2539 + difference 5 0) (sourceB2539 + difference 0 5) sourceC2539) = raw35058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35058; decide +kernel
    rw [ha]
    exact (canonical35058 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2539 + difference 5 1) (sourceB2539 + difference 1 5) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3728) := by
    have ha : (tripleCharges (sourceA2539 + difference 5 1) (sourceB2539 + difference 1 5) sourceC2539) = raw35059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35059; decide +kernel
    rw [ha]
    exact (canonical35059 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2539 + difference 5 2) (sourceB2539 + difference 2 5) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3715) := by
    have ha : (tripleCharges (sourceA2539 + difference 5 2) (sourceB2539 + difference 2 5) sourceC2539) = raw35060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35060; decide +kernel
    rw [ha]
    exact (canonical35060 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2539 + difference 5 3) (sourceB2539 + difference 3 5) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3740) := by
    have ha : (tripleCharges (sourceA2539 + difference 5 3) (sourceB2539 + difference 3 5) sourceC2539) = raw35061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35061; decide +kernel
    rw [ha]
    exact (canonical35061 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2539 + difference 5 4) (sourceB2539 + difference 4 5) sourceC2539) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA2539 + difference 5 4) (sourceB2539 + difference 4 5) sourceC2539) = raw35062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2539 sourceB2539 sourceC2539 difference raw35062; decide +kernel
    rw [ha]
    exact (canonical35062 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2539 sourceB2539 sourceC2539
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2539, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2540 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2540 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC2540 : Charge := ![0, 2, 0, 2, -2, -2]
def sourceForm2540 : Integer.Sparse Master := [(Sum.inr 2313, 2), (Sum.inr 3638, 1), (Sum.inr 3660, 1), (Sum.inr 3664, 1), (Sum.inr 3666, 1), (Sum.inr 4089, -1)]

theorem sourceEq2540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2540 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2540 + difference 0 3) (sourceB2540 + difference 3 0) sourceC2540) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3664) := by
    have ha : (tripleCharges (sourceA2540 + difference 0 3) (sourceB2540 + difference 3 0) sourceC2540) = raw35063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2540 sourceB2540 sourceC2540 difference raw35063; decide +kernel
    rw [ha]
    exact (canonical35063 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2540 + difference 1 3) (sourceB2540 + difference 3 1) sourceC2540) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3666) := by
    have ha : (tripleCharges (sourceA2540 + difference 1 3) (sourceB2540 + difference 3 1) sourceC2540) = raw29362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2540 sourceB2540 sourceC2540 difference raw29362; decide +kernel
    rw [ha]
    exact (canonical29362 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2540 + difference 2 3) (sourceB2540 + difference 3 2) sourceC2540) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3638) := by
    have ha : (tripleCharges (sourceA2540 + difference 2 3) (sourceB2540 + difference 3 2) sourceC2540) = raw35064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2540 sourceB2540 sourceC2540 difference raw35064; decide +kernel
    rw [ha]
    exact (canonical35064 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2540 + difference 3 3) (sourceB2540 + difference 3 3) sourceC2540) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3660) := by
    have ha : (tripleCharges (sourceA2540 + difference 3 3) (sourceB2540 + difference 3 3) sourceC2540) = raw29360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2540 sourceB2540 sourceC2540 difference raw29360; decide +kernel
    rw [ha]
    exact (canonical29360 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2540 + difference 4 3) (sourceB2540 + difference 3 4) sourceC2540) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2313) := by
    have ha : (tripleCharges (sourceA2540 + difference 4 3) (sourceB2540 + difference 3 4) sourceC2540) = raw35065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2540 sourceB2540 sourceC2540 difference raw35065; decide +kernel
    rw [ha]
    exact (canonical35065 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2540 + difference 5 3) (sourceB2540 + difference 3 5) sourceC2540) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2313) := by
    have ha : (tripleCharges (sourceA2540 + difference 5 3) (sourceB2540 + difference 3 5) sourceC2540) = raw35066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2540 sourceB2540 sourceC2540 difference raw35066; decide +kernel
    rw [ha]
    exact (canonical35066 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2540 + sourceB2540) sourceC2540) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2540 + sourceB2540) sourceC2540) = raw29365 := by
      apply Matrix.ext; unfold doubleCharges sourceA2540 sourceB2540 sourceC2540 raw29365; decide +kernel
    rw [ha]
    exact (canonical29365 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2540 sourceB2540 sourceC2540
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2540, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2541 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2541 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC2541 : Charge := ![0, 2, 1, 1, -2, -2]
def sourceForm2541 : Integer.Sparse Master := [(Sum.inr 2298, 2), (Sum.inr 3641, 1), (Sum.inr 3646, 1), (Sum.inr 3650, 1), (Sum.inr 3653, 1), (Sum.inr 4088, -1)]

theorem sourceEq2541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2541 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2541 + difference 0 2) (sourceB2541 + difference 2 0) sourceC2541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3650) := by
    have ha : (tripleCharges (sourceA2541 + difference 0 2) (sourceB2541 + difference 2 0) sourceC2541) = raw35067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2541 sourceB2541 sourceC2541 difference raw35067; decide +kernel
    rw [ha]
    exact (canonical35067 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2541 + difference 1 2) (sourceB2541 + difference 2 1) sourceC2541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3653) := by
    have ha : (tripleCharges (sourceA2541 + difference 1 2) (sourceB2541 + difference 2 1) sourceC2541) = raw35068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2541 sourceB2541 sourceC2541 difference raw35068; decide +kernel
    rw [ha]
    exact (canonical35068 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2541 + difference 2 2) (sourceB2541 + difference 2 2) sourceC2541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3646) := by
    have ha : (tripleCharges (sourceA2541 + difference 2 2) (sourceB2541 + difference 2 2) sourceC2541) = raw35069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2541 sourceB2541 sourceC2541 difference raw35069; decide +kernel
    rw [ha]
    exact (canonical35069 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2541 + difference 3 2) (sourceB2541 + difference 2 3) sourceC2541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3641) := by
    have ha : (tripleCharges (sourceA2541 + difference 3 2) (sourceB2541 + difference 2 3) sourceC2541) = raw35070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2541 sourceB2541 sourceC2541 difference raw35070; decide +kernel
    rw [ha]
    exact (canonical35070 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2541 + difference 4 2) (sourceB2541 + difference 2 4) sourceC2541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2298) := by
    have ha : (tripleCharges (sourceA2541 + difference 4 2) (sourceB2541 + difference 2 4) sourceC2541) = raw35071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2541 sourceB2541 sourceC2541 difference raw35071; decide +kernel
    rw [ha]
    exact (canonical35071 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2541 + difference 5 2) (sourceB2541 + difference 2 5) sourceC2541) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2298) := by
    have ha : (tripleCharges (sourceA2541 + difference 5 2) (sourceB2541 + difference 2 5) sourceC2541) = raw35072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2541 sourceB2541 sourceC2541 difference raw35072; decide +kernel
    rw [ha]
    exact (canonical35072 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2541 + sourceB2541) sourceC2541) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2541 + sourceB2541) sourceC2541) = raw35073 := by
      apply Matrix.ext; unfold doubleCharges sourceA2541 sourceB2541 sourceC2541 raw35073; decide +kernel
    rw [ha]
    exact (canonical35073 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2541 sourceB2541 sourceC2541
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2541, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2542 : Charge := ![0, 2, 1, 1, -2, -2]
def sourceB2542 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC2542 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceForm2542 : Integer.Sparse Master := [(Sum.inr 2303, 2), (Sum.inr 3656, 1), (Sum.inr 3663, 1), (Sum.inr 3664, 2), (Sum.inr 4089, -1)]

theorem sourceEq2542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2542 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2542 + difference 0 0) (sourceB2542 + difference 0 0) sourceC2542) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3656) := by
    have ha : (tripleCharges (sourceA2542 + difference 0 0) (sourceB2542 + difference 0 0) sourceC2542) = raw35074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2542 sourceB2542 sourceC2542 difference raw35074; decide +kernel
    rw [ha]
    exact (canonical35074 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2542 + difference 0 1) (sourceB2542 + difference 1 0) sourceC2542) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3663) := by
    have ha : (tripleCharges (sourceA2542 + difference 0 1) (sourceB2542 + difference 1 0) sourceC2542) = raw35075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2542 sourceB2542 sourceC2542 difference raw35075; decide +kernel
    rw [ha]
    exact (canonical35075 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2542 + difference 0 2) (sourceB2542 + difference 2 0) sourceC2542) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3664) := by
    have ha : (tripleCharges (sourceA2542 + difference 0 2) (sourceB2542 + difference 2 0) sourceC2542) = raw35076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2542 sourceB2542 sourceC2542 difference raw35076; decide +kernel
    rw [ha]
    exact (canonical35076 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2542 + difference 0 3) (sourceB2542 + difference 3 0) sourceC2542) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3664) := by
    have ha : (tripleCharges (sourceA2542 + difference 0 3) (sourceB2542 + difference 3 0) sourceC2542) = raw35077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2542 sourceB2542 sourceC2542 difference raw35077; decide +kernel
    rw [ha]
    exact (canonical35077 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2542 + difference 0 4) (sourceB2542 + difference 4 0) sourceC2542) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2303) := by
    have ha : (tripleCharges (sourceA2542 + difference 0 4) (sourceB2542 + difference 4 0) sourceC2542) = raw35078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2542 sourceB2542 sourceC2542 difference raw35078; decide +kernel
    rw [ha]
    exact (canonical35078 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2542 + difference 0 5) (sourceB2542 + difference 5 0) sourceC2542) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2303) := by
    have ha : (tripleCharges (sourceA2542 + difference 0 5) (sourceB2542 + difference 5 0) sourceC2542) = raw35079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2542 sourceB2542 sourceC2542 difference raw35079; decide +kernel
    rw [ha]
    exact (canonical35079 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2542 + sourceB2542) sourceC2542) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2542 + sourceB2542) sourceC2542) = raw35080 := by
      apply Matrix.ext; unfold doubleCharges sourceA2542 sourceB2542 sourceC2542 raw35080; decide +kernel
    rw [ha]
    exact (canonical35080 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2542 sourceB2542 sourceC2542
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2542, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2543 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2543 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceC2543 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm2543 : Integer.Sparse Master := [(Sum.inr 4381, 2), (Sum.inr 4382, 1), (Sum.inr 4383, 1), (Sum.inr 4491, 1), (Sum.inr 4651, 2), (Sum.inr 4657, 1), (Sum.inr 4845, 1), (Sum.inr 4920, 2), (Sum.inr 4925, 1), (Sum.inr 4983, 2), (Sum.inr 5046, 2), (Sum.inr 5095, 2), (Sum.inr 5110, 1), (Sum.inr 5207, 1), (Sum.inr 5228, 2), (Sum.inr 5237, 2), (Sum.inr 5291, 1), (Sum.inr 5304, 1), (Sum.inr 5370, 2), (Sum.inr 5443, 1), (Sum.inr 5451, 1)]

theorem sourceEq2543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2543 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2543 + difference 0 1) (sourceB2543 + difference 1 0) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA2543 + difference 0 1) (sourceB2543 + difference 1 0) sourceC2543) = raw35081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35081; decide +kernel
    rw [ha]
    exact (canonical35081 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2543 + difference 0 2) (sourceB2543 + difference 2 0) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2543 + difference 0 2) (sourceB2543 + difference 2 0) sourceC2543) = raw35082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35082; decide +kernel
    rw [ha]
    exact (canonical35082 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2543 + difference 0 3) (sourceB2543 + difference 3 0) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2543 + difference 0 3) (sourceB2543 + difference 3 0) sourceC2543) = raw35083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35083; decide +kernel
    rw [ha]
    exact (canonical35083 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2543 + difference 0 4) (sourceB2543 + difference 4 0) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2543 + difference 0 4) (sourceB2543 + difference 4 0) sourceC2543) = raw16219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw16219; decide +kernel
    rw [ha]
    exact (canonical16219 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2543 + difference 0 5) (sourceB2543 + difference 5 0) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2543 + difference 0 5) (sourceB2543 + difference 5 0) sourceC2543) = raw35084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35084; decide +kernel
    rw [ha]
    exact (canonical35084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2543 + difference 1 0) (sourceB2543 + difference 0 1) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2543 + difference 1 0) (sourceB2543 + difference 0 1) sourceC2543) = raw16239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw16239; decide +kernel
    rw [ha]
    exact (canonical16239 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2543 + difference 1 2) (sourceB2543 + difference 2 1) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2543 + difference 1 2) (sourceB2543 + difference 2 1) sourceC2543) = raw16241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw16241; decide +kernel
    rw [ha]
    exact (canonical16241 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2543 + difference 1 3) (sourceB2543 + difference 3 1) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2543 + difference 1 3) (sourceB2543 + difference 3 1) sourceC2543) = raw16242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw16242; decide +kernel
    rw [ha]
    exact (canonical16242 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2543 + difference 1 4) (sourceB2543 + difference 4 1) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2543 + difference 1 4) (sourceB2543 + difference 4 1) sourceC2543) = raw28233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw28233; decide +kernel
    rw [ha]
    exact (canonical28233 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2543 + difference 1 5) (sourceB2543 + difference 5 1) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2543 + difference 1 5) (sourceB2543 + difference 5 1) sourceC2543) = raw16243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw16243; decide +kernel
    rw [ha]
    exact (canonical16243 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2543 + difference 2 0) (sourceB2543 + difference 0 2) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2543 + difference 2 0) (sourceB2543 + difference 0 2) sourceC2543) = raw29950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw29950; decide +kernel
    rw [ha]
    exact (canonical29950 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2543 + difference 2 1) (sourceB2543 + difference 1 2) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4381) := by
    have ha : (tripleCharges (sourceA2543 + difference 2 1) (sourceB2543 + difference 1 2) sourceC2543) = raw35085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35085; decide +kernel
    rw [ha]
    exact (canonical35085 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2543 + difference 2 3) (sourceB2543 + difference 3 2) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5046) := by
    have ha : (tripleCharges (sourceA2543 + difference 2 3) (sourceB2543 + difference 3 2) sourceC2543) = raw35086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35086; decide +kernel
    rw [ha]
    exact (canonical35086 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2543 + difference 2 4) (sourceB2543 + difference 4 2) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2543 + difference 2 4) (sourceB2543 + difference 4 2) sourceC2543) = raw16230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw16230; decide +kernel
    rw [ha]
    exact (canonical16230 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2543 + difference 2 5) (sourceB2543 + difference 5 2) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2543 + difference 2 5) (sourceB2543 + difference 5 2) sourceC2543) = raw35087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35087; decide +kernel
    rw [ha]
    exact (canonical35087 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2543 + difference 3 0) (sourceB2543 + difference 0 3) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2543 + difference 3 0) (sourceB2543 + difference 0 3) sourceC2543) = raw29954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw29954; decide +kernel
    rw [ha]
    exact (canonical29954 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2543 + difference 3 1) (sourceB2543 + difference 1 3) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4381) := by
    have ha : (tripleCharges (sourceA2543 + difference 3 1) (sourceB2543 + difference 1 3) sourceC2543) = raw35088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35088; decide +kernel
    rw [ha]
    exact (canonical35088 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2543 + difference 3 2) (sourceB2543 + difference 2 3) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5046) := by
    have ha : (tripleCharges (sourceA2543 + difference 3 2) (sourceB2543 + difference 2 3) sourceC2543) = raw35089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35089; decide +kernel
    rw [ha]
    exact (canonical35089 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2543 + difference 3 4) (sourceB2543 + difference 4 3) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2543 + difference 3 4) (sourceB2543 + difference 4 3) sourceC2543) = raw16235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw16235; decide +kernel
    rw [ha]
    exact (canonical16235 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2543 + difference 3 5) (sourceB2543 + difference 5 3) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2543 + difference 3 5) (sourceB2543 + difference 5 3) sourceC2543) = raw35090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35090; decide +kernel
    rw [ha]
    exact (canonical35090 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2543 + difference 4 0) (sourceB2543 + difference 0 4) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4657) := by
    have ha : (tripleCharges (sourceA2543 + difference 4 0) (sourceB2543 + difference 0 4) sourceC2543) = raw29958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw29958; decide +kernel
    rw [ha]
    exact (canonical29958 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2543 + difference 4 1) (sourceB2543 + difference 1 4) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4382) := by
    have ha : (tripleCharges (sourceA2543 + difference 4 1) (sourceB2543 + difference 1 4) sourceC2543) = raw35091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35091; decide +kernel
    rw [ha]
    exact (canonical35091 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2543 + difference 4 2) (sourceB2543 + difference 2 4) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4651) := by
    have ha : (tripleCharges (sourceA2543 + difference 4 2) (sourceB2543 + difference 2 4) sourceC2543) = raw35092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35092; decide +kernel
    rw [ha]
    exact (canonical35092 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2543 + difference 4 3) (sourceB2543 + difference 3 4) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4651) := by
    have ha : (tripleCharges (sourceA2543 + difference 4 3) (sourceB2543 + difference 3 4) sourceC2543) = raw35093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35093; decide +kernel
    rw [ha]
    exact (canonical35093 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2543 + difference 4 5) (sourceB2543 + difference 5 4) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2543 + difference 4 5) (sourceB2543 + difference 5 4) sourceC2543) = raw35094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35094; decide +kernel
    rw [ha]
    exact (canonical35094 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2543 + difference 5 0) (sourceB2543 + difference 0 5) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4925) := by
    have ha : (tripleCharges (sourceA2543 + difference 5 0) (sourceB2543 + difference 0 5) sourceC2543) = raw28247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw28247; decide +kernel
    rw [ha]
    exact (canonical28247 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2543 + difference 5 1) (sourceB2543 + difference 1 5) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4383) := by
    have ha : (tripleCharges (sourceA2543 + difference 5 1) (sourceB2543 + difference 1 5) sourceC2543) = raw35095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35095; decide +kernel
    rw [ha]
    exact (canonical35095 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2543 + difference 5 2) (sourceB2543 + difference 2 5) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4920) := by
    have ha : (tripleCharges (sourceA2543 + difference 5 2) (sourceB2543 + difference 2 5) sourceC2543) = raw35096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35096; decide +kernel
    rw [ha]
    exact (canonical35096 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2543 + difference 5 3) (sourceB2543 + difference 3 5) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4920) := by
    have ha : (tripleCharges (sourceA2543 + difference 5 3) (sourceB2543 + difference 3 5) sourceC2543) = raw35097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw35097; decide +kernel
    rw [ha]
    exact (canonical35097 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2543 + difference 5 4) (sourceB2543 + difference 4 5) sourceC2543) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2543 + difference 5 4) (sourceB2543 + difference 4 5) sourceC2543) = raw16245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2543 sourceB2543 sourceC2543 difference raw16245; decide +kernel
    rw [ha]
    exact (canonical16245 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2543 sourceB2543 sourceC2543
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2543, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2544 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2544 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceC2544 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm2544 : Integer.Sparse Master := [(Sum.inr 1547, 2), (Sum.inr 1548, 1), (Sum.inr 1549, 1), (Sum.inr 1653, 1), (Sum.inr 1779, 2), (Sum.inr 1783, 1), (Sum.inr 2065, 1), (Sum.inr 2311, 2), (Sum.inr 2315, 1), (Sum.inr 2522, 1), (Sum.inr 2794, 2), (Sum.inr 2889, 1), (Sum.inr 3363, 2), (Sum.inr 3391, 2), (Sum.inr 3394, 2), (Sum.inr 3448, 2), (Sum.inr 3582, 1), (Sum.inr 3583, 1), (Sum.inr 3706, 2), (Sum.inr 3862, 1), (Sum.inr 3987, 1)]

theorem sourceEq2544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2544 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2544 + difference 0 1) (sourceB2544 + difference 1 0) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA2544 + difference 0 1) (sourceB2544 + difference 1 0) sourceC2544) = raw35098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35098; decide +kernel
    rw [ha]
    exact (canonical35098 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2544 + difference 0 2) (sourceB2544 + difference 2 0) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3448) := by
    have ha : (tripleCharges (sourceA2544 + difference 0 2) (sourceB2544 + difference 2 0) sourceC2544) = raw35099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35099; decide +kernel
    rw [ha]
    exact (canonical35099 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2544 + difference 0 3) (sourceB2544 + difference 3 0) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3448) := by
    have ha : (tripleCharges (sourceA2544 + difference 0 3) (sourceB2544 + difference 3 0) sourceC2544) = raw35100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35100; decide +kernel
    rw [ha]
    exact (canonical35100 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2544 + difference 0 4) (sourceB2544 + difference 4 0) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA2544 + difference 0 4) (sourceB2544 + difference 4 0) sourceC2544) = raw16249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw16249; decide +kernel
    rw [ha]
    exact (canonical16249 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2544 + difference 0 5) (sourceB2544 + difference 5 0) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA2544 + difference 0 5) (sourceB2544 + difference 5 0) sourceC2544) = raw35101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35101; decide +kernel
    rw [ha]
    exact (canonical35101 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2544 + difference 1 0) (sourceB2544 + difference 0 1) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2544 + difference 1 0) (sourceB2544 + difference 0 1) sourceC2544) = raw16269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw16269; decide +kernel
    rw [ha]
    exact (canonical16269 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2544 + difference 1 2) (sourceB2544 + difference 2 1) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2544 + difference 1 2) (sourceB2544 + difference 2 1) sourceC2544) = raw16271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw16271; decide +kernel
    rw [ha]
    exact (canonical16271 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2544 + difference 1 3) (sourceB2544 + difference 3 1) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2544 + difference 1 3) (sourceB2544 + difference 3 1) sourceC2544) = raw16272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw16272; decide +kernel
    rw [ha]
    exact (canonical16272 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2544 + difference 1 4) (sourceB2544 + difference 4 1) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA2544 + difference 1 4) (sourceB2544 + difference 4 1) sourceC2544) = raw28255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw28255; decide +kernel
    rw [ha]
    exact (canonical28255 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2544 + difference 1 5) (sourceB2544 + difference 5 1) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA2544 + difference 1 5) (sourceB2544 + difference 5 1) sourceC2544) = raw16273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw16273; decide +kernel
    rw [ha]
    exact (canonical16273 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2544 + difference 2 0) (sourceB2544 + difference 0 2) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2794) := by
    have ha : (tripleCharges (sourceA2544 + difference 2 0) (sourceB2544 + difference 0 2) sourceC2544) = raw29967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw29967; decide +kernel
    rw [ha]
    exact (canonical29967 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2544 + difference 2 1) (sourceB2544 + difference 1 2) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1547) := by
    have ha : (tripleCharges (sourceA2544 + difference 2 1) (sourceB2544 + difference 1 2) sourceC2544) = raw35102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35102; decide +kernel
    rw [ha]
    exact (canonical35102 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2544 + difference 2 3) (sourceB2544 + difference 3 2) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3363) := by
    have ha : (tripleCharges (sourceA2544 + difference 2 3) (sourceB2544 + difference 3 2) sourceC2544) = raw35103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35103; decide +kernel
    rw [ha]
    exact (canonical35103 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2544 + difference 2 4) (sourceB2544 + difference 4 2) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA2544 + difference 2 4) (sourceB2544 + difference 4 2) sourceC2544) = raw16260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw16260; decide +kernel
    rw [ha]
    exact (canonical16260 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2544 + difference 2 5) (sourceB2544 + difference 5 2) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA2544 + difference 2 5) (sourceB2544 + difference 5 2) sourceC2544) = raw35104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35104; decide +kernel
    rw [ha]
    exact (canonical35104 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2544 + difference 3 0) (sourceB2544 + difference 0 3) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2794) := by
    have ha : (tripleCharges (sourceA2544 + difference 3 0) (sourceB2544 + difference 0 3) sourceC2544) = raw29971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw29971; decide +kernel
    rw [ha]
    exact (canonical29971 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2544 + difference 3 1) (sourceB2544 + difference 1 3) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1547) := by
    have ha : (tripleCharges (sourceA2544 + difference 3 1) (sourceB2544 + difference 1 3) sourceC2544) = raw35105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35105; decide +kernel
    rw [ha]
    exact (canonical35105 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2544 + difference 3 2) (sourceB2544 + difference 2 3) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3363) := by
    have ha : (tripleCharges (sourceA2544 + difference 3 2) (sourceB2544 + difference 2 3) sourceC2544) = raw35106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35106; decide +kernel
    rw [ha]
    exact (canonical35106 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2544 + difference 3 4) (sourceB2544 + difference 4 3) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA2544 + difference 3 4) (sourceB2544 + difference 4 3) sourceC2544) = raw16265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw16265; decide +kernel
    rw [ha]
    exact (canonical16265 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2544 + difference 3 5) (sourceB2544 + difference 5 3) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA2544 + difference 3 5) (sourceB2544 + difference 5 3) sourceC2544) = raw35107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35107; decide +kernel
    rw [ha]
    exact (canonical35107 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2544 + difference 4 0) (sourceB2544 + difference 0 4) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1783) := by
    have ha : (tripleCharges (sourceA2544 + difference 4 0) (sourceB2544 + difference 0 4) sourceC2544) = raw29975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw29975; decide +kernel
    rw [ha]
    exact (canonical29975 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2544 + difference 4 1) (sourceB2544 + difference 1 4) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1548) := by
    have ha : (tripleCharges (sourceA2544 + difference 4 1) (sourceB2544 + difference 1 4) sourceC2544) = raw35108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35108; decide +kernel
    rw [ha]
    exact (canonical35108 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2544 + difference 4 2) (sourceB2544 + difference 2 4) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1779) := by
    have ha : (tripleCharges (sourceA2544 + difference 4 2) (sourceB2544 + difference 2 4) sourceC2544) = raw35109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35109; decide +kernel
    rw [ha]
    exact (canonical35109 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2544 + difference 4 3) (sourceB2544 + difference 3 4) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1779) := by
    have ha : (tripleCharges (sourceA2544 + difference 4 3) (sourceB2544 + difference 3 4) sourceC2544) = raw35110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35110; decide +kernel
    rw [ha]
    exact (canonical35110 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2544 + difference 4 5) (sourceB2544 + difference 5 4) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA2544 + difference 4 5) (sourceB2544 + difference 5 4) sourceC2544) = raw35111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35111; decide +kernel
    rw [ha]
    exact (canonical35111 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2544 + difference 5 0) (sourceB2544 + difference 0 5) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2315) := by
    have ha : (tripleCharges (sourceA2544 + difference 5 0) (sourceB2544 + difference 0 5) sourceC2544) = raw28269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw28269; decide +kernel
    rw [ha]
    exact (canonical28269 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2544 + difference 5 1) (sourceB2544 + difference 1 5) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1549) := by
    have ha : (tripleCharges (sourceA2544 + difference 5 1) (sourceB2544 + difference 1 5) sourceC2544) = raw35112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35112; decide +kernel
    rw [ha]
    exact (canonical35112 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2544 + difference 5 2) (sourceB2544 + difference 2 5) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2311) := by
    have ha : (tripleCharges (sourceA2544 + difference 5 2) (sourceB2544 + difference 2 5) sourceC2544) = raw35113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35113; decide +kernel
    rw [ha]
    exact (canonical35113 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2544 + difference 5 3) (sourceB2544 + difference 3 5) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2311) := by
    have ha : (tripleCharges (sourceA2544 + difference 5 3) (sourceB2544 + difference 3 5) sourceC2544) = raw35114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw35114; decide +kernel
    rw [ha]
    exact (canonical35114 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2544 + difference 5 4) (sourceB2544 + difference 4 5) sourceC2544) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA2544 + difference 5 4) (sourceB2544 + difference 4 5) sourceC2544) = raw16275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2544 sourceB2544 sourceC2544 difference raw16275; decide +kernel
    rw [ha]
    exact (canonical16275 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2544 sourceB2544 sourceC2544
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2544, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2545 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2545 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2545 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceForm2545 : Integer.Sparse Master := [(Sum.inr 4684, 2), (Sum.inr 4692, 1), (Sum.inr 4693, 1), (Sum.inr 4703, 2), (Sum.inr 4704, 1), (Sum.inr 4705, 1), (Sum.inr 4846, 1), (Sum.inr 4884, 1), (Sum.inr 4945, 2), (Sum.inr 4976, 2), (Sum.inr 5110, 1), (Sum.inr 5206, 1), (Sum.inr 5215, 2), (Sum.inr 5228, 2), (Sum.inr 5229, 2), (Sum.inr 5248, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5287, 2), (Sum.inr 5300, 1), (Sum.inr 5302, 1)]

theorem sourceEq2545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2545 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 1) (sourceB2545 + difference 1 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 1) (sourceB2545 + difference 1 0) sourceC2545) = raw35115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35115; decide +kernel
    rw [ha]
    exact (canonical35115 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 2) (sourceB2545 + difference 2 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 2) (sourceB2545 + difference 2 0) sourceC2545) = raw35116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35116; decide +kernel
    rw [ha]
    exact (canonical35116 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 3) (sourceB2545 + difference 3 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 3) (sourceB2545 + difference 3 0) sourceC2545) = raw35117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35117; decide +kernel
    rw [ha]
    exact (canonical35117 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 4) (sourceB2545 + difference 4 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 4) (sourceB2545 + difference 4 0) sourceC2545) = raw35118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35118; decide +kernel
    rw [ha]
    exact (canonical35118 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 5) (sourceB2545 + difference 5 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 5) (sourceB2545 + difference 5 0) sourceC2545) = raw35119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35119; decide +kernel
    rw [ha]
    exact (canonical35119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 0) (sourceB2545 + difference 0 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 0) (sourceB2545 + difference 0 1) sourceC2545) = raw35120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35120; decide +kernel
    rw [ha]
    exact (canonical35120 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 2) (sourceB2545 + difference 2 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 2) (sourceB2545 + difference 2 1) sourceC2545) = raw35121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35121; decide +kernel
    rw [ha]
    exact (canonical35121 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 3) (sourceB2545 + difference 3 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 3) (sourceB2545 + difference 3 1) sourceC2545) = raw35122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35122; decide +kernel
    rw [ha]
    exact (canonical35122 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 4) (sourceB2545 + difference 4 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 4) (sourceB2545 + difference 4 1) sourceC2545) = raw35123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35123; decide +kernel
    rw [ha]
    exact (canonical35123 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 5) (sourceB2545 + difference 5 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 5) (sourceB2545 + difference 5 1) sourceC2545) = raw35124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35124; decide +kernel
    rw [ha]
    exact (canonical35124 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 0) (sourceB2545 + difference 0 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4703) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 0) (sourceB2545 + difference 0 2) sourceC2545) = raw35125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35125; decide +kernel
    rw [ha]
    exact (canonical35125 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 1) (sourceB2545 + difference 1 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 1) (sourceB2545 + difference 1 2) sourceC2545) = raw35126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35126; decide +kernel
    rw [ha]
    exact (canonical35126 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 3) (sourceB2545 + difference 3 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 3) (sourceB2545 + difference 3 2) sourceC2545) = raw35127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35127; decide +kernel
    rw [ha]
    exact (canonical35127 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 4) (sourceB2545 + difference 4 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 4) (sourceB2545 + difference 4 2) sourceC2545) = raw35128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35128; decide +kernel
    rw [ha]
    exact (canonical35128 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 5) (sourceB2545 + difference 5 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 5) (sourceB2545 + difference 5 2) sourceC2545) = raw35129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35129; decide +kernel
    rw [ha]
    exact (canonical35129 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 0) (sourceB2545 + difference 0 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4703) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 0) (sourceB2545 + difference 0 3) sourceC2545) = raw35130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35130; decide +kernel
    rw [ha]
    exact (canonical35130 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 1) (sourceB2545 + difference 1 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 1) (sourceB2545 + difference 1 3) sourceC2545) = raw35131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35131; decide +kernel
    rw [ha]
    exact (canonical35131 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 2) (sourceB2545 + difference 2 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 2) (sourceB2545 + difference 2 3) sourceC2545) = raw35132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35132; decide +kernel
    rw [ha]
    exact (canonical35132 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 4) (sourceB2545 + difference 4 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 4) (sourceB2545 + difference 4 3) sourceC2545) = raw35133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35133; decide +kernel
    rw [ha]
    exact (canonical35133 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 5) (sourceB2545 + difference 5 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 5) (sourceB2545 + difference 5 3) sourceC2545) = raw35134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35134; decide +kernel
    rw [ha]
    exact (canonical35134 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 0) (sourceB2545 + difference 0 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 0) (sourceB2545 + difference 0 4) sourceC2545) = raw35135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35135; decide +kernel
    rw [ha]
    exact (canonical35135 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 1) (sourceB2545 + difference 1 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 1) (sourceB2545 + difference 1 4) sourceC2545) = raw35136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35136; decide +kernel
    rw [ha]
    exact (canonical35136 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 2) (sourceB2545 + difference 2 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 2) (sourceB2545 + difference 2 4) sourceC2545) = raw35137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35137; decide +kernel
    rw [ha]
    exact (canonical35137 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 3) (sourceB2545 + difference 3 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 3) (sourceB2545 + difference 3 4) sourceC2545) = raw35138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35138; decide +kernel
    rw [ha]
    exact (canonical35138 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 5) (sourceB2545 + difference 5 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 5) (sourceB2545 + difference 5 4) sourceC2545) = raw35139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35139; decide +kernel
    rw [ha]
    exact (canonical35139 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 0) (sourceB2545 + difference 0 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4704) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 0) (sourceB2545 + difference 0 5) sourceC2545) = raw35140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35140; decide +kernel
    rw [ha]
    exact (canonical35140 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 1) (sourceB2545 + difference 1 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 1) (sourceB2545 + difference 1 5) sourceC2545) = raw35141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35141; decide +kernel
    rw [ha]
    exact (canonical35141 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 2) (sourceB2545 + difference 2 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 2) (sourceB2545 + difference 2 5) sourceC2545) = raw35142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35142; decide +kernel
    rw [ha]
    exact (canonical35142 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 3) (sourceB2545 + difference 3 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 3) (sourceB2545 + difference 3 5) sourceC2545) = raw35143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35143; decide +kernel
    rw [ha]
    exact (canonical35143 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 4) (sourceB2545 + difference 4 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 4) (sourceB2545 + difference 4 5) sourceC2545) = raw35144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35144; decide +kernel
    rw [ha]
    exact (canonical35144 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2545 sourceB2545 sourceC2545
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2545, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2546 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2546 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2546 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceForm2546 : Integer.Sparse Master := [(Sum.inr 1829, 2), (Sum.inr 1830, 1), (Sum.inr 1831, 1), (Sum.inr 2138, 1), (Sum.inr 2362, 2), (Sum.inr 2363, 1), (Sum.inr 2643, 1), (Sum.inr 2758, 2), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 2831, 2), (Sum.inr 2832, 1), (Sum.inr 3005, 1), (Sum.inr 3083, 2), (Sum.inr 3092, 2), (Sum.inr 3094, 2), (Sum.inr 3106, 2), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3144, 2), (Sum.inr 3216, 1)]

theorem sourceEq2546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2546 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2546 + difference 0 1) (sourceB2546 + difference 1 0) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3216) := by
    have ha : (tripleCharges (sourceA2546 + difference 0 1) (sourceB2546 + difference 1 0) sourceC2546) = raw35145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35145; decide +kernel
    rw [ha]
    exact (canonical35145 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2546 + difference 0 2) (sourceB2546 + difference 2 0) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3106) := by
    have ha : (tripleCharges (sourceA2546 + difference 0 2) (sourceB2546 + difference 2 0) sourceC2546) = raw35146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35146; decide +kernel
    rw [ha]
    exact (canonical35146 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2546 + difference 0 3) (sourceB2546 + difference 3 0) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3106) := by
    have ha : (tripleCharges (sourceA2546 + difference 0 3) (sourceB2546 + difference 3 0) sourceC2546) = raw35147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35147; decide +kernel
    rw [ha]
    exact (canonical35147 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2546 + difference 0 4) (sourceB2546 + difference 4 0) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA2546 + difference 0 4) (sourceB2546 + difference 4 0) sourceC2546) = raw35148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35148; decide +kernel
    rw [ha]
    exact (canonical35148 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2546 + difference 0 5) (sourceB2546 + difference 5 0) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA2546 + difference 0 5) (sourceB2546 + difference 5 0) sourceC2546) = raw35149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35149; decide +kernel
    rw [ha]
    exact (canonical35149 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2546 + difference 1 0) (sourceB2546 + difference 0 1) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA2546 + difference 1 0) (sourceB2546 + difference 0 1) sourceC2546) = raw35150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35150; decide +kernel
    rw [ha]
    exact (canonical35150 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2546 + difference 1 2) (sourceB2546 + difference 2 1) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA2546 + difference 1 2) (sourceB2546 + difference 2 1) sourceC2546) = raw35151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35151; decide +kernel
    rw [ha]
    exact (canonical35151 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2546 + difference 1 3) (sourceB2546 + difference 3 1) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA2546 + difference 1 3) (sourceB2546 + difference 3 1) sourceC2546) = raw35152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35152; decide +kernel
    rw [ha]
    exact (canonical35152 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2546 + difference 1 4) (sourceB2546 + difference 4 1) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA2546 + difference 1 4) (sourceB2546 + difference 4 1) sourceC2546) = raw35153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35153; decide +kernel
    rw [ha]
    exact (canonical35153 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2546 + difference 1 5) (sourceB2546 + difference 5 1) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA2546 + difference 1 5) (sourceB2546 + difference 5 1) sourceC2546) = raw35154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35154; decide +kernel
    rw [ha]
    exact (canonical35154 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2546 + difference 2 0) (sourceB2546 + difference 0 2) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2546 + difference 2 0) (sourceB2546 + difference 0 2) sourceC2546) = raw35155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35155; decide +kernel
    rw [ha]
    exact (canonical35155 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2546 + difference 2 1) (sourceB2546 + difference 1 2) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3144) := by
    have ha : (tripleCharges (sourceA2546 + difference 2 1) (sourceB2546 + difference 1 2) sourceC2546) = raw35156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35156; decide +kernel
    rw [ha]
    exact (canonical35156 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2546 + difference 2 3) (sourceB2546 + difference 3 2) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3083) := by
    have ha : (tripleCharges (sourceA2546 + difference 2 3) (sourceB2546 + difference 3 2) sourceC2546) = raw35157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35157; decide +kernel
    rw [ha]
    exact (canonical35157 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2546 + difference 2 4) (sourceB2546 + difference 4 2) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA2546 + difference 2 4) (sourceB2546 + difference 4 2) sourceC2546) = raw35158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35158; decide +kernel
    rw [ha]
    exact (canonical35158 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2546 + difference 2 5) (sourceB2546 + difference 5 2) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3094) := by
    have ha : (tripleCharges (sourceA2546 + difference 2 5) (sourceB2546 + difference 5 2) sourceC2546) = raw35159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35159; decide +kernel
    rw [ha]
    exact (canonical35159 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2546 + difference 3 0) (sourceB2546 + difference 0 3) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2546 + difference 3 0) (sourceB2546 + difference 0 3) sourceC2546) = raw35160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35160; decide +kernel
    rw [ha]
    exact (canonical35160 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2546 + difference 3 1) (sourceB2546 + difference 1 3) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3144) := by
    have ha : (tripleCharges (sourceA2546 + difference 3 1) (sourceB2546 + difference 1 3) sourceC2546) = raw35161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35161; decide +kernel
    rw [ha]
    exact (canonical35161 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2546 + difference 3 2) (sourceB2546 + difference 2 3) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3083) := by
    have ha : (tripleCharges (sourceA2546 + difference 3 2) (sourceB2546 + difference 2 3) sourceC2546) = raw35162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35162; decide +kernel
    rw [ha]
    exact (canonical35162 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2546 + difference 3 4) (sourceB2546 + difference 4 3) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA2546 + difference 3 4) (sourceB2546 + difference 4 3) sourceC2546) = raw35163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35163; decide +kernel
    rw [ha]
    exact (canonical35163 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2546 + difference 3 5) (sourceB2546 + difference 5 3) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3094) := by
    have ha : (tripleCharges (sourceA2546 + difference 3 5) (sourceB2546 + difference 5 3) sourceC2546) = raw35164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35164; decide +kernel
    rw [ha]
    exact (canonical35164 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2546 + difference 4 0) (sourceB2546 + difference 0 4) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1831) := by
    have ha : (tripleCharges (sourceA2546 + difference 4 0) (sourceB2546 + difference 0 4) sourceC2546) = raw35165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35165; decide +kernel
    rw [ha]
    exact (canonical35165 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2546 + difference 4 1) (sourceB2546 + difference 1 4) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2832) := by
    have ha : (tripleCharges (sourceA2546 + difference 4 1) (sourceB2546 + difference 1 4) sourceC2546) = raw35166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35166; decide +kernel
    rw [ha]
    exact (canonical35166 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2546 + difference 4 2) (sourceB2546 + difference 2 4) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2831) := by
    have ha : (tripleCharges (sourceA2546 + difference 4 2) (sourceB2546 + difference 2 4) sourceC2546) = raw35167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35167; decide +kernel
    rw [ha]
    exact (canonical35167 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2546 + difference 4 3) (sourceB2546 + difference 3 4) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2831) := by
    have ha : (tripleCharges (sourceA2546 + difference 4 3) (sourceB2546 + difference 3 4) sourceC2546) = raw35168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35168; decide +kernel
    rw [ha]
    exact (canonical35168 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2546 + difference 4 5) (sourceB2546 + difference 5 4) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3005) := by
    have ha : (tripleCharges (sourceA2546 + difference 4 5) (sourceB2546 + difference 5 4) sourceC2546) = raw35169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35169; decide +kernel
    rw [ha]
    exact (canonical35169 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2546 + difference 5 0) (sourceB2546 + difference 0 5) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1830) := by
    have ha : (tripleCharges (sourceA2546 + difference 5 0) (sourceB2546 + difference 0 5) sourceC2546) = raw35170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35170; decide +kernel
    rw [ha]
    exact (canonical35170 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2546 + difference 5 1) (sourceB2546 + difference 1 5) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2363) := by
    have ha : (tripleCharges (sourceA2546 + difference 5 1) (sourceB2546 + difference 1 5) sourceC2546) = raw35171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35171; decide +kernel
    rw [ha]
    exact (canonical35171 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2546 + difference 5 2) (sourceB2546 + difference 2 5) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2362) := by
    have ha : (tripleCharges (sourceA2546 + difference 5 2) (sourceB2546 + difference 2 5) sourceC2546) = raw35172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35172; decide +kernel
    rw [ha]
    exact (canonical35172 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2546 + difference 5 3) (sourceB2546 + difference 3 5) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2362) := by
    have ha : (tripleCharges (sourceA2546 + difference 5 3) (sourceB2546 + difference 3 5) sourceC2546) = raw35173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35173; decide +kernel
    rw [ha]
    exact (canonical35173 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2546 + difference 5 4) (sourceB2546 + difference 4 5) sourceC2546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA2546 + difference 5 4) (sourceB2546 + difference 4 5) sourceC2546) = raw35174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2546 sourceB2546 sourceC2546 difference raw35174; decide +kernel
    rw [ha]
    exact (canonical35174 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2546 sourceB2546 sourceC2546
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2546, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2547 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2547 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2547 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceForm2547 : Integer.Sparse Master := [(Sum.inr 2152, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2229, 1), (Sum.inr 2272, 2), (Sum.inr 2273, 1), (Sum.inr 2280, 1), (Sum.inr 2286, 1), (Sum.inr 2653, 2), (Sum.inr 2658, 2), (Sum.inr 2659, 2), (Sum.inr 2672, 2), (Sum.inr 2673, 2), (Sum.inr 2685, 1), (Sum.inr 2687, 1), (Sum.inr 2705, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 3025, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1)]

theorem sourceEq2547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2547 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 1) (sourceB2547 + difference 1 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 1) (sourceB2547 + difference 1 0) sourceC2547) = raw35175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35175; decide +kernel
    rw [ha]
    exact (canonical35175 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 2) (sourceB2547 + difference 2 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 2) (sourceB2547 + difference 2 0) sourceC2547) = raw35176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35176; decide +kernel
    rw [ha]
    exact (canonical35176 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 3) (sourceB2547 + difference 3 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 3) (sourceB2547 + difference 3 0) sourceC2547) = raw35177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35177; decide +kernel
    rw [ha]
    exact (canonical35177 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 4) (sourceB2547 + difference 4 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 4) (sourceB2547 + difference 4 0) sourceC2547) = raw35178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35178; decide +kernel
    rw [ha]
    exact (canonical35178 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 5) (sourceB2547 + difference 5 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 5) (sourceB2547 + difference 5 0) sourceC2547) = raw35179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35179; decide +kernel
    rw [ha]
    exact (canonical35179 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 0) (sourceB2547 + difference 0 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 0) (sourceB2547 + difference 0 1) sourceC2547) = raw35180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35180; decide +kernel
    rw [ha]
    exact (canonical35180 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 2) (sourceB2547 + difference 2 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 2) (sourceB2547 + difference 2 1) sourceC2547) = raw35181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35181; decide +kernel
    rw [ha]
    exact (canonical35181 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 3) (sourceB2547 + difference 3 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 3) (sourceB2547 + difference 3 1) sourceC2547) = raw35182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35182; decide +kernel
    rw [ha]
    exact (canonical35182 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 4) (sourceB2547 + difference 4 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 4) (sourceB2547 + difference 4 1) sourceC2547) = raw35183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35183; decide +kernel
    rw [ha]
    exact (canonical35183 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 5) (sourceB2547 + difference 5 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 5) (sourceB2547 + difference 5 1) sourceC2547) = raw35184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35184; decide +kernel
    rw [ha]
    exact (canonical35184 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 0) (sourceB2547 + difference 0 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 0) (sourceB2547 + difference 0 2) sourceC2547) = raw35185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35185; decide +kernel
    rw [ha]
    exact (canonical35185 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 1) (sourceB2547 + difference 1 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 1) (sourceB2547 + difference 1 2) sourceC2547) = raw35186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35186; decide +kernel
    rw [ha]
    exact (canonical35186 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 3) (sourceB2547 + difference 3 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 3) (sourceB2547 + difference 3 2) sourceC2547) = raw35187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35187; decide +kernel
    rw [ha]
    exact (canonical35187 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 4) (sourceB2547 + difference 4 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 4) (sourceB2547 + difference 4 2) sourceC2547) = raw35188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35188; decide +kernel
    rw [ha]
    exact (canonical35188 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 5) (sourceB2547 + difference 5 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 5) (sourceB2547 + difference 5 2) sourceC2547) = raw35189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35189; decide +kernel
    rw [ha]
    exact (canonical35189 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 0) (sourceB2547 + difference 0 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 0) (sourceB2547 + difference 0 3) sourceC2547) = raw35190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35190; decide +kernel
    rw [ha]
    exact (canonical35190 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 1) (sourceB2547 + difference 1 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 1) (sourceB2547 + difference 1 3) sourceC2547) = raw35191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35191; decide +kernel
    rw [ha]
    exact (canonical35191 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 2) (sourceB2547 + difference 2 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 2) (sourceB2547 + difference 2 3) sourceC2547) = raw35192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35192; decide +kernel
    rw [ha]
    exact (canonical35192 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 4) (sourceB2547 + difference 4 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 4) (sourceB2547 + difference 4 3) sourceC2547) = raw35193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35193; decide +kernel
    rw [ha]
    exact (canonical35193 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 5) (sourceB2547 + difference 5 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 5) (sourceB2547 + difference 5 3) sourceC2547) = raw35194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35194; decide +kernel
    rw [ha]
    exact (canonical35194 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 0) (sourceB2547 + difference 0 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 0) (sourceB2547 + difference 0 4) sourceC2547) = raw35195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35195; decide +kernel
    rw [ha]
    exact (canonical35195 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 1) (sourceB2547 + difference 1 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 1) (sourceB2547 + difference 1 4) sourceC2547) = raw35196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35196; decide +kernel
    rw [ha]
    exact (canonical35196 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 2) (sourceB2547 + difference 2 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 2) (sourceB2547 + difference 2 4) sourceC2547) = raw35197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35197; decide +kernel
    rw [ha]
    exact (canonical35197 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 3) (sourceB2547 + difference 3 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 3) (sourceB2547 + difference 3 4) sourceC2547) = raw35198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35198; decide +kernel
    rw [ha]
    exact (canonical35198 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 5) (sourceB2547 + difference 5 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 5) (sourceB2547 + difference 5 4) sourceC2547) = raw35199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35199; decide +kernel
    rw [ha]
    exact (canonical35199 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 0) (sourceB2547 + difference 0 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2273) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 0) (sourceB2547 + difference 0 5) sourceC2547) = raw35200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35200; decide +kernel
    rw [ha]
    exact (canonical35200 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 1) (sourceB2547 + difference 1 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 1) (sourceB2547 + difference 1 5) sourceC2547) = raw35201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35201; decide +kernel
    rw [ha]
    exact (canonical35201 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 2) (sourceB2547 + difference 2 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 2) (sourceB2547 + difference 2 5) sourceC2547) = raw35202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35202; decide +kernel
    rw [ha]
    exact (canonical35202 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 3) (sourceB2547 + difference 3 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 3) (sourceB2547 + difference 3 5) sourceC2547) = raw35203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35203; decide +kernel
    rw [ha]
    exact (canonical35203 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 4) (sourceB2547 + difference 4 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 4) (sourceB2547 + difference 4 5) sourceC2547) = raw35204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35204; decide +kernel
    rw [ha]
    exact (canonical35204 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2547 sourceB2547 sourceC2547
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2547, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2548 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2548 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2548 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceForm2548 : Integer.Sparse Master := [(Sum.inr 1810, 1), (Sum.inr 3129, 1), (Sum.inr 3364, 1), (Sum.inr 3391, 1), (Sum.inr 3392, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

theorem sourceEq2548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2548 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2548 + difference 2 0) (sourceB2548 + difference 0 2) sourceC2548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3129) := by
    have ha : (tripleCharges (sourceA2548 + difference 2 0) (sourceB2548 + difference 0 2) sourceC2548) = raw29368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2548 sourceB2548 sourceC2548 difference raw29368; decide +kernel
    rw [ha]
    exact (canonical29368 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2548 + difference 2 1) (sourceB2548 + difference 1 2) sourceC2548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2548 + difference 2 1) (sourceB2548 + difference 1 2) sourceC2548) = raw35205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2548 sourceB2548 sourceC2548 difference raw35205; decide +kernel
    rw [ha]
    exact (canonical35205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2548 + difference 2 2) (sourceB2548 + difference 2 2) sourceC2548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2548 + difference 2 2) (sourceB2548 + difference 2 2) sourceC2548) = raw29366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2548 sourceB2548 sourceC2548 difference raw29366; decide +kernel
    rw [ha]
    exact (canonical29366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2548 + difference 2 3) (sourceB2548 + difference 3 2) sourceC2548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3364) := by
    have ha : (tripleCharges (sourceA2548 + difference 2 3) (sourceB2548 + difference 3 2) sourceC2548) = raw35206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2548 sourceB2548 sourceC2548 difference raw35206; decide +kernel
    rw [ha]
    exact (canonical35206 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2548 + difference 2 4) (sourceB2548 + difference 4 2) sourceC2548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA2548 + difference 2 4) (sourceB2548 + difference 4 2) sourceC2548) = raw35207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2548 sourceB2548 sourceC2548 difference raw35207; decide +kernel
    rw [ha]
    exact (canonical35207 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2548 + difference 2 5) (sourceB2548 + difference 5 2) sourceC2548) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA2548 + difference 2 5) (sourceB2548 + difference 5 2) sourceC2548) = raw35208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2548 sourceB2548 sourceC2548 difference raw35208; decide +kernel
    rw [ha]
    exact (canonical35208 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2548 + sourceB2548) sourceC2548) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2548 + sourceB2548) sourceC2548) = raw29372 := by
      apply Matrix.ext; unfold doubleCharges sourceA2548 sourceB2548 sourceC2548 raw29372; decide +kernel
    rw [ha]
    exact (canonical29372 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2548 sourceB2548 sourceC2548
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2548, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2549 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceB2549 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2549 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceForm2549 : Integer.Sparse Master := [(Sum.inr 4568, 2), (Sum.inr 4573, 1), (Sum.inr 4575, 1), (Sum.inr 4615, 1), (Sum.inr 5006, 2), (Sum.inr 5015, 2), (Sum.inr 5021, 1), (Sum.inr 5024, 1), (Sum.inr 5122, 2), (Sum.inr 5125, 2), (Sum.inr 5158, 2), (Sum.inr 5232, 2), (Sum.inr 5235, 1), (Sum.inr 5236, 2), (Sum.inr 5238, 1), (Sum.inr 5297, 1), (Sum.inr 5303, 1), (Sum.inr 5355, 2), (Sum.inr 5371, 1), (Sum.inr 5389, 1), (Sum.inr 5390, 1)]

theorem sourceEq2549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2549 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2549 + difference 0 1) (sourceB2549 + difference 1 0) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2549 + difference 0 1) (sourceB2549 + difference 1 0) sourceC2549) = raw34821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34821; decide +kernel
    rw [ha]
    exact (canonical34821 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2549 + difference 0 2) (sourceB2549 + difference 2 0) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2549 + difference 0 2) (sourceB2549 + difference 2 0) sourceC2549) = raw35209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35209; decide +kernel
    rw [ha]
    exact (canonical35209 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2549 + difference 0 3) (sourceB2549 + difference 3 0) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2549 + difference 0 3) (sourceB2549 + difference 3 0) sourceC2549) = raw35210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35210; decide +kernel
    rw [ha]
    exact (canonical35210 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2549 + difference 0 4) (sourceB2549 + difference 4 0) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA2549 + difference 0 4) (sourceB2549 + difference 4 0) sourceC2549) = raw35211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35211; decide +kernel
    rw [ha]
    exact (canonical35211 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2549 + difference 0 5) (sourceB2549 + difference 5 0) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5024) := by
    have ha : (tripleCharges (sourceA2549 + difference 0 5) (sourceB2549 + difference 5 0) sourceC2549) = raw35212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35212; decide +kernel
    rw [ha]
    exact (canonical35212 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2549 + difference 1 0) (sourceB2549 + difference 0 1) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4615) := by
    have ha : (tripleCharges (sourceA2549 + difference 1 0) (sourceB2549 + difference 0 1) sourceC2549) = raw35213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35213; decide +kernel
    rw [ha]
    exact (canonical35213 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2549 + difference 1 2) (sourceB2549 + difference 2 1) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4568) := by
    have ha : (tripleCharges (sourceA2549 + difference 1 2) (sourceB2549 + difference 2 1) sourceC2549) = raw35214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35214; decide +kernel
    rw [ha]
    exact (canonical35214 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2549 + difference 1 3) (sourceB2549 + difference 3 1) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4568) := by
    have ha : (tripleCharges (sourceA2549 + difference 1 3) (sourceB2549 + difference 3 1) sourceC2549) = raw35215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35215; decide +kernel
    rw [ha]
    exact (canonical35215 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2549 + difference 1 4) (sourceB2549 + difference 4 1) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4573) := by
    have ha : (tripleCharges (sourceA2549 + difference 1 4) (sourceB2549 + difference 4 1) sourceC2549) = raw35216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35216; decide +kernel
    rw [ha]
    exact (canonical35216 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2549 + difference 1 5) (sourceB2549 + difference 5 1) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4575) := by
    have ha : (tripleCharges (sourceA2549 + difference 1 5) (sourceB2549 + difference 5 1) sourceC2549) = raw35217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35217; decide +kernel
    rw [ha]
    exact (canonical35217 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2549 + difference 2 0) (sourceB2549 + difference 0 2) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5158) := by
    have ha : (tripleCharges (sourceA2549 + difference 2 0) (sourceB2549 + difference 0 2) sourceC2549) = raw35218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35218; decide +kernel
    rw [ha]
    exact (canonical35218 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2549 + difference 2 1) (sourceB2549 + difference 1 2) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2549 + difference 2 1) (sourceB2549 + difference 1 2) sourceC2549) = raw34831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34831; decide +kernel
    rw [ha]
    exact (canonical34831 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2549 + difference 2 3) (sourceB2549 + difference 3 2) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5122) := by
    have ha : (tripleCharges (sourceA2549 + difference 2 3) (sourceB2549 + difference 3 2) sourceC2549) = raw35219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35219; decide +kernel
    rw [ha]
    exact (canonical35219 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2549 + difference 2 4) (sourceB2549 + difference 4 2) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5006) := by
    have ha : (tripleCharges (sourceA2549 + difference 2 4) (sourceB2549 + difference 4 2) sourceC2549) = raw35220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35220; decide +kernel
    rw [ha]
    exact (canonical35220 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2549 + difference 2 5) (sourceB2549 + difference 5 2) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2549 + difference 2 5) (sourceB2549 + difference 5 2) sourceC2549) = raw35221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35221; decide +kernel
    rw [ha]
    exact (canonical35221 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2549 + difference 3 0) (sourceB2549 + difference 0 3) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5158) := by
    have ha : (tripleCharges (sourceA2549 + difference 3 0) (sourceB2549 + difference 0 3) sourceC2549) = raw35020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35020; decide +kernel
    rw [ha]
    exact (canonical35020 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2549 + difference 3 1) (sourceB2549 + difference 1 3) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2549 + difference 3 1) (sourceB2549 + difference 1 3) sourceC2549) = raw34836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34836; decide +kernel
    rw [ha]
    exact (canonical34836 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2549 + difference 3 2) (sourceB2549 + difference 2 3) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5122) := by
    have ha : (tripleCharges (sourceA2549 + difference 3 2) (sourceB2549 + difference 2 3) sourceC2549) = raw35021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35021; decide +kernel
    rw [ha]
    exact (canonical35021 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2549 + difference 3 4) (sourceB2549 + difference 4 3) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5006) := by
    have ha : (tripleCharges (sourceA2549 + difference 3 4) (sourceB2549 + difference 4 3) sourceC2549) = raw35022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35022; decide +kernel
    rw [ha]
    exact (canonical35022 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2549 + difference 3 5) (sourceB2549 + difference 5 3) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2549 + difference 3 5) (sourceB2549 + difference 5 3) sourceC2549) = raw35023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw35023; decide +kernel
    rw [ha]
    exact (canonical35023 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2549 + difference 4 0) (sourceB2549 + difference 0 4) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5303) := by
    have ha : (tripleCharges (sourceA2549 + difference 4 0) (sourceB2549 + difference 0 4) sourceC2549) = raw34889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34889; decide +kernel
    rw [ha]
    exact (canonical34889 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2549 + difference 4 1) (sourceB2549 + difference 1 4) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2549 + difference 4 1) (sourceB2549 + difference 1 4) sourceC2549) = raw34841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34841; decide +kernel
    rw [ha]
    exact (canonical34841 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2549 + difference 4 2) (sourceB2549 + difference 2 4) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2549 + difference 4 2) (sourceB2549 + difference 2 4) sourceC2549) = raw34890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34890; decide +kernel
    rw [ha]
    exact (canonical34890 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2549 + difference 4 3) (sourceB2549 + difference 3 4) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2549 + difference 4 3) (sourceB2549 + difference 3 4) sourceC2549) = raw34891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34891; decide +kernel
    rw [ha]
    exact (canonical34891 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2549 + difference 4 5) (sourceB2549 + difference 5 4) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2549 + difference 4 5) (sourceB2549 + difference 5 4) sourceC2549) = raw34892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34892; decide +kernel
    rw [ha]
    exact (canonical34892 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2549 + difference 5 0) (sourceB2549 + difference 0 5) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5297) := by
    have ha : (tripleCharges (sourceA2549 + difference 5 0) (sourceB2549 + difference 0 5) sourceC2549) = raw34822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34822; decide +kernel
    rw [ha]
    exact (canonical34822 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2549 + difference 5 1) (sourceB2549 + difference 1 5) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2549 + difference 5 1) (sourceB2549 + difference 1 5) sourceC2549) = raw34906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34906; decide +kernel
    rw [ha]
    exact (canonical34906 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2549 + difference 5 2) (sourceB2549 + difference 2 5) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2549 + difference 5 2) (sourceB2549 + difference 2 5) sourceC2549) = raw34823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34823; decide +kernel
    rw [ha]
    exact (canonical34823 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2549 + difference 5 3) (sourceB2549 + difference 3 5) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2549 + difference 5 3) (sourceB2549 + difference 3 5) sourceC2549) = raw34824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34824; decide +kernel
    rw [ha]
    exact (canonical34824 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2549 + difference 5 4) (sourceB2549 + difference 4 5) sourceC2549) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5235) := by
    have ha : (tripleCharges (sourceA2549 + difference 5 4) (sourceB2549 + difference 4 5) sourceC2549) = raw34825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2549 sourceB2549 sourceC2549 difference raw34825; decide +kernel
    rw [ha]
    exact (canonical34825 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2549 sourceB2549 sourceC2549
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2549, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2550 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2550 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2550 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm2550 : Integer.Sparse Master := [(Sum.inr 4950, 8), (Sum.inr 4952, 4), (Sum.inr 5177, 4), (Sum.inr 5457, 2), (Sum.inr 5465, 8), (Sum.inr 5487, 4)]

theorem sourceEq2550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2550 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 1) (sourceB2550 + difference 1 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 1) (sourceB2550 + difference 1 0) sourceC2550) = raw35222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35222; decide +kernel
    rw [ha]
    exact (canonical35222 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 2) (sourceB2550 + difference 2 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 2) (sourceB2550 + difference 2 0) sourceC2550) = raw35223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35223; decide +kernel
    rw [ha]
    exact (canonical35223 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 3) (sourceB2550 + difference 3 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 3) (sourceB2550 + difference 3 0) sourceC2550) = raw35224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35224; decide +kernel
    rw [ha]
    exact (canonical35224 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 4) (sourceB2550 + difference 4 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 4) (sourceB2550 + difference 4 0) sourceC2550) = raw17663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17663; decide +kernel
    rw [ha]
    exact (canonical17663 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2550 + difference 0 5) (sourceB2550 + difference 5 0) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2550 + difference 0 5) (sourceB2550 + difference 5 0) sourceC2550) = raw35225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35225; decide +kernel
    rw [ha]
    exact (canonical35225 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 0) (sourceB2550 + difference 0 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 0) (sourceB2550 + difference 0 1) sourceC2550) = raw17675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17675; decide +kernel
    rw [ha]
    exact (canonical17675 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 2) (sourceB2550 + difference 2 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 2) (sourceB2550 + difference 2 1) sourceC2550) = raw17677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17677; decide +kernel
    rw [ha]
    exact (canonical17677 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 3) (sourceB2550 + difference 3 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 3) (sourceB2550 + difference 3 1) sourceC2550) = raw17678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17678; decide +kernel
    rw [ha]
    exact (canonical17678 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 4) (sourceB2550 + difference 4 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 4) (sourceB2550 + difference 4 1) sourceC2550) = raw2772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw2772; decide +kernel
    rw [ha]
    exact (canonical2772 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2550 + difference 1 5) (sourceB2550 + difference 5 1) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2550 + difference 1 5) (sourceB2550 + difference 5 1) sourceC2550) = raw17679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17679; decide +kernel
    rw [ha]
    exact (canonical17679 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 0) (sourceB2550 + difference 0 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 0) (sourceB2550 + difference 0 2) sourceC2550) = raw29650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw29650; decide +kernel
    rw [ha]
    exact (canonical29650 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 1) (sourceB2550 + difference 1 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 1) (sourceB2550 + difference 1 2) sourceC2550) = raw35226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35226; decide +kernel
    rw [ha]
    exact (canonical35226 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 3) (sourceB2550 + difference 3 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5457) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 3) (sourceB2550 + difference 3 2) sourceC2550) = raw35227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35227; decide +kernel
    rw [ha]
    exact (canonical35227 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 4) (sourceB2550 + difference 4 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 4) (sourceB2550 + difference 4 2) sourceC2550) = raw17668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17668; decide +kernel
    rw [ha]
    exact (canonical17668 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2550 + difference 2 5) (sourceB2550 + difference 5 2) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 2 5) (sourceB2550 + difference 5 2) sourceC2550) = raw35228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35228; decide +kernel
    rw [ha]
    exact (canonical35228 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 0) (sourceB2550 + difference 0 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 0) (sourceB2550 + difference 0 3) sourceC2550) = raw29653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw29653; decide +kernel
    rw [ha]
    exact (canonical29653 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 1) (sourceB2550 + difference 1 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 1) (sourceB2550 + difference 1 3) sourceC2550) = raw35229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35229; decide +kernel
    rw [ha]
    exact (canonical35229 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 2) (sourceB2550 + difference 2 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5457) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 2) (sourceB2550 + difference 2 3) sourceC2550) = raw35230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35230; decide +kernel
    rw [ha]
    exact (canonical35230 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 4) (sourceB2550 + difference 4 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 4) (sourceB2550 + difference 4 3) sourceC2550) = raw17672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17672; decide +kernel
    rw [ha]
    exact (canonical17672 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2550 + difference 3 5) (sourceB2550 + difference 5 3) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2550 + difference 3 5) (sourceB2550 + difference 5 3) sourceC2550) = raw35231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35231; decide +kernel
    rw [ha]
    exact (canonical35231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 0) (sourceB2550 + difference 0 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 0) (sourceB2550 + difference 0 4) sourceC2550) = raw29656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw29656; decide +kernel
    rw [ha]
    exact (canonical29656 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 1) (sourceB2550 + difference 1 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 1) (sourceB2550 + difference 1 4) sourceC2550) = raw35232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35232; decide +kernel
    rw [ha]
    exact (canonical35232 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 2) (sourceB2550 + difference 2 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 2) (sourceB2550 + difference 2 4) sourceC2550) = raw35233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35233; decide +kernel
    rw [ha]
    exact (canonical35233 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 3) (sourceB2550 + difference 3 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 3) (sourceB2550 + difference 3 4) sourceC2550) = raw35234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35234; decide +kernel
    rw [ha]
    exact (canonical35234 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2550 + difference 4 5) (sourceB2550 + difference 5 4) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2550 + difference 4 5) (sourceB2550 + difference 5 4) sourceC2550) = raw35235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35235; decide +kernel
    rw [ha]
    exact (canonical35235 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 0) (sourceB2550 + difference 0 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 0) (sourceB2550 + difference 0 5) sourceC2550) = raw27590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw27590; decide +kernel
    rw [ha]
    exact (canonical27590 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 1) (sourceB2550 + difference 1 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 1) (sourceB2550 + difference 1 5) sourceC2550) = raw35236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35236; decide +kernel
    rw [ha]
    exact (canonical35236 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 2) (sourceB2550 + difference 2 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 2) (sourceB2550 + difference 2 5) sourceC2550) = raw35237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35237; decide +kernel
    rw [ha]
    exact (canonical35237 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 3) (sourceB2550 + difference 3 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 3) (sourceB2550 + difference 3 5) sourceC2550) = raw35238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw35238; decide +kernel
    rw [ha]
    exact (canonical35238 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2550 + difference 5 4) (sourceB2550 + difference 4 5) sourceC2550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2550 + difference 5 4) (sourceB2550 + difference 4 5) sourceC2550) = raw17680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2550 sourceB2550 sourceC2550 difference raw17680; decide +kernel
    rw [ha]
    exact (canonical17680 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2550 sourceB2550 sourceC2550
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2550, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2551 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2551 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2551 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm2551 : Integer.Sparse Master := [(Sum.inr 2342, 8), (Sum.inr 2344, 4), (Sum.inr 2605, 4), (Sum.inr 3917, 2), (Sum.inr 3931, 8), (Sum.inr 4000, 4)]

theorem sourceEq2551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2551 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2551 + difference 0 1) (sourceB2551 + difference 1 0) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA2551 + difference 0 1) (sourceB2551 + difference 1 0) sourceC2551) = raw35239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35239; decide +kernel
    rw [ha]
    exact (canonical35239 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2551 + difference 0 2) (sourceB2551 + difference 2 0) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2551 + difference 0 2) (sourceB2551 + difference 2 0) sourceC2551) = raw35240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35240; decide +kernel
    rw [ha]
    exact (canonical35240 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2551 + difference 0 3) (sourceB2551 + difference 3 0) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2551 + difference 0 3) (sourceB2551 + difference 3 0) sourceC2551) = raw35241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35241; decide +kernel
    rw [ha]
    exact (canonical35241 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2551 + difference 0 4) (sourceB2551 + difference 4 0) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA2551 + difference 0 4) (sourceB2551 + difference 4 0) sourceC2551) = raw35242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35242; decide +kernel
    rw [ha]
    exact (canonical35242 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2551 + difference 0 5) (sourceB2551 + difference 5 0) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA2551 + difference 0 5) (sourceB2551 + difference 5 0) sourceC2551) = raw35243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35243; decide +kernel
    rw [ha]
    exact (canonical35243 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2551 + difference 1 0) (sourceB2551 + difference 0 1) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA2551 + difference 1 0) (sourceB2551 + difference 0 1) sourceC2551) = raw23239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw23239; decide +kernel
    rw [ha]
    exact (canonical23239 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2551 + difference 1 2) (sourceB2551 + difference 2 1) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2551 + difference 1 2) (sourceB2551 + difference 2 1) sourceC2551) = raw29661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw29661; decide +kernel
    rw [ha]
    exact (canonical29661 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2551 + difference 1 3) (sourceB2551 + difference 3 1) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2551 + difference 1 3) (sourceB2551 + difference 3 1) sourceC2551) = raw29662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw29662; decide +kernel
    rw [ha]
    exact (canonical29662 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2551 + difference 1 4) (sourceB2551 + difference 4 1) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA2551 + difference 1 4) (sourceB2551 + difference 4 1) sourceC2551) = raw2802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw2802; decide +kernel
    rw [ha]
    exact (canonical2802 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2551 + difference 1 5) (sourceB2551 + difference 5 1) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA2551 + difference 1 5) (sourceB2551 + difference 5 1) sourceC2551) = raw29663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw29663; decide +kernel
    rw [ha]
    exact (canonical29663 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2551 + difference 2 0) (sourceB2551 + difference 0 2) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2551 + difference 2 0) (sourceB2551 + difference 0 2) sourceC2551) = raw29664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw29664; decide +kernel
    rw [ha]
    exact (canonical29664 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2551 + difference 2 1) (sourceB2551 + difference 1 2) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2551 + difference 2 1) (sourceB2551 + difference 1 2) sourceC2551) = raw35244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35244; decide +kernel
    rw [ha]
    exact (canonical35244 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2551 + difference 2 3) (sourceB2551 + difference 3 2) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3917) := by
    have ha : (tripleCharges (sourceA2551 + difference 2 3) (sourceB2551 + difference 3 2) sourceC2551) = raw35245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35245; decide +kernel
    rw [ha]
    exact (canonical35245 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2551 + difference 2 4) (sourceB2551 + difference 4 2) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2551 + difference 2 4) (sourceB2551 + difference 4 2) sourceC2551) = raw35246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35246; decide +kernel
    rw [ha]
    exact (canonical35246 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2551 + difference 2 5) (sourceB2551 + difference 5 2) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2551 + difference 2 5) (sourceB2551 + difference 5 2) sourceC2551) = raw35247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35247; decide +kernel
    rw [ha]
    exact (canonical35247 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2551 + difference 3 0) (sourceB2551 + difference 0 3) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2551 + difference 3 0) (sourceB2551 + difference 0 3) sourceC2551) = raw29667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw29667; decide +kernel
    rw [ha]
    exact (canonical29667 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2551 + difference 3 1) (sourceB2551 + difference 1 3) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2551 + difference 3 1) (sourceB2551 + difference 1 3) sourceC2551) = raw35248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35248; decide +kernel
    rw [ha]
    exact (canonical35248 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2551 + difference 3 2) (sourceB2551 + difference 2 3) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3917) := by
    have ha : (tripleCharges (sourceA2551 + difference 3 2) (sourceB2551 + difference 2 3) sourceC2551) = raw35249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35249; decide +kernel
    rw [ha]
    exact (canonical35249 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2551 + difference 3 4) (sourceB2551 + difference 4 3) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2551 + difference 3 4) (sourceB2551 + difference 4 3) sourceC2551) = raw35250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35250; decide +kernel
    rw [ha]
    exact (canonical35250 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2551 + difference 3 5) (sourceB2551 + difference 5 3) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2551 + difference 3 5) (sourceB2551 + difference 5 3) sourceC2551) = raw35251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35251; decide +kernel
    rw [ha]
    exact (canonical35251 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2551 + difference 4 0) (sourceB2551 + difference 0 4) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2344) := by
    have ha : (tripleCharges (sourceA2551 + difference 4 0) (sourceB2551 + difference 0 4) sourceC2551) = raw29670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw29670; decide +kernel
    rw [ha]
    exact (canonical29670 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2551 + difference 4 1) (sourceB2551 + difference 1 4) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2344) := by
    have ha : (tripleCharges (sourceA2551 + difference 4 1) (sourceB2551 + difference 1 4) sourceC2551) = raw35252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35252; decide +kernel
    rw [ha]
    exact (canonical35252 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2551 + difference 4 2) (sourceB2551 + difference 2 4) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2551 + difference 4 2) (sourceB2551 + difference 2 4) sourceC2551) = raw35253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35253; decide +kernel
    rw [ha]
    exact (canonical35253 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2551 + difference 4 3) (sourceB2551 + difference 3 4) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2551 + difference 4 3) (sourceB2551 + difference 3 4) sourceC2551) = raw35254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35254; decide +kernel
    rw [ha]
    exact (canonical35254 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2551 + difference 4 5) (sourceB2551 + difference 5 4) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA2551 + difference 4 5) (sourceB2551 + difference 5 4) sourceC2551) = raw35255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35255; decide +kernel
    rw [ha]
    exact (canonical35255 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2551 + difference 5 0) (sourceB2551 + difference 0 5) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2344) := by
    have ha : (tripleCharges (sourceA2551 + difference 5 0) (sourceB2551 + difference 0 5) sourceC2551) = raw27604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw27604; decide +kernel
    rw [ha]
    exact (canonical27604 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2551 + difference 5 1) (sourceB2551 + difference 1 5) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2344) := by
    have ha : (tripleCharges (sourceA2551 + difference 5 1) (sourceB2551 + difference 1 5) sourceC2551) = raw35256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35256; decide +kernel
    rw [ha]
    exact (canonical35256 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2551 + difference 5 2) (sourceB2551 + difference 2 5) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2551 + difference 5 2) (sourceB2551 + difference 2 5) sourceC2551) = raw35257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35257; decide +kernel
    rw [ha]
    exact (canonical35257 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2551 + difference 5 3) (sourceB2551 + difference 3 5) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2551 + difference 5 3) (sourceB2551 + difference 3 5) sourceC2551) = raw35258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw35258; decide +kernel
    rw [ha]
    exact (canonical35258 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2551 + difference 5 4) (sourceB2551 + difference 4 5) sourceC2551) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA2551 + difference 5 4) (sourceB2551 + difference 4 5) sourceC2551) = raw27596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2551 sourceB2551 sourceC2551 difference raw27596; decide +kernel
    rw [ha]
    exact (canonical27596 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2551 sourceB2551 sourceC2551
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2551, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2552 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2552 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2552 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceForm2552 : Integer.Sparse Master := [(Sum.inr 5356, 16), (Sum.inr 5371, 8), (Sum.inr 5390, 4), (Sum.inr 5458, 2)]

theorem sourceEq2552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2552 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2552 + difference 0 1) (sourceB2552 + difference 1 0) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2552 + difference 0 1) (sourceB2552 + difference 1 0) sourceC2552) = raw35259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35259; decide +kernel
    rw [ha]
    exact (canonical35259 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2552 + difference 0 2) (sourceB2552 + difference 2 0) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 0 2) (sourceB2552 + difference 2 0) sourceC2552) = raw35260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35260; decide +kernel
    rw [ha]
    exact (canonical35260 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2552 + difference 0 3) (sourceB2552 + difference 3 0) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 0 3) (sourceB2552 + difference 3 0) sourceC2552) = raw35261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35261; decide +kernel
    rw [ha]
    exact (canonical35261 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2552 + difference 0 4) (sourceB2552 + difference 4 0) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2552 + difference 0 4) (sourceB2552 + difference 4 0) sourceC2552) = raw35262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35262; decide +kernel
    rw [ha]
    exact (canonical35262 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2552 + difference 0 5) (sourceB2552 + difference 5 0) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2552 + difference 0 5) (sourceB2552 + difference 5 0) sourceC2552) = raw35263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35263; decide +kernel
    rw [ha]
    exact (canonical35263 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2552 + difference 1 0) (sourceB2552 + difference 0 1) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2552 + difference 1 0) (sourceB2552 + difference 0 1) sourceC2552) = raw34841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34841; decide +kernel
    rw [ha]
    exact (canonical34841 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2552 + difference 1 2) (sourceB2552 + difference 2 1) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 1 2) (sourceB2552 + difference 2 1) sourceC2552) = raw34886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34886; decide +kernel
    rw [ha]
    exact (canonical34886 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2552 + difference 1 3) (sourceB2552 + difference 3 1) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 1 3) (sourceB2552 + difference 3 1) sourceC2552) = raw34887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34887; decide +kernel
    rw [ha]
    exact (canonical34887 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2552 + difference 1 4) (sourceB2552 + difference 4 1) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2552 + difference 1 4) (sourceB2552 + difference 4 1) sourceC2552) = raw34821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34821; decide +kernel
    rw [ha]
    exact (canonical34821 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2552 + difference 1 5) (sourceB2552 + difference 5 1) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2552 + difference 1 5) (sourceB2552 + difference 5 1) sourceC2552) = raw34888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34888; decide +kernel
    rw [ha]
    exact (canonical34888 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2552 + difference 2 0) (sourceB2552 + difference 0 2) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 2 0) (sourceB2552 + difference 0 2) sourceC2552) = raw34894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34894; decide +kernel
    rw [ha]
    exact (canonical34894 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2552 + difference 2 1) (sourceB2552 + difference 1 2) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 2 1) (sourceB2552 + difference 1 2) sourceC2552) = raw35264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35264; decide +kernel
    rw [ha]
    exact (canonical35264 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2552 + difference 2 3) (sourceB2552 + difference 3 2) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5458) := by
    have ha : (tripleCharges (sourceA2552 + difference 2 3) (sourceB2552 + difference 3 2) sourceC2552) = raw35265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35265; decide +kernel
    rw [ha]
    exact (canonical35265 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2552 + difference 2 4) (sourceB2552 + difference 4 2) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 2 4) (sourceB2552 + difference 4 2) sourceC2552) = raw35266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35266; decide +kernel
    rw [ha]
    exact (canonical35266 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2552 + difference 2 5) (sourceB2552 + difference 5 2) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 2 5) (sourceB2552 + difference 5 2) sourceC2552) = raw35267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35267; decide +kernel
    rw [ha]
    exact (canonical35267 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2552 + difference 3 0) (sourceB2552 + difference 0 3) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 3 0) (sourceB2552 + difference 0 3) sourceC2552) = raw34898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34898; decide +kernel
    rw [ha]
    exact (canonical34898 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2552 + difference 3 1) (sourceB2552 + difference 1 3) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 3 1) (sourceB2552 + difference 1 3) sourceC2552) = raw35268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35268; decide +kernel
    rw [ha]
    exact (canonical35268 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2552 + difference 3 2) (sourceB2552 + difference 2 3) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5458) := by
    have ha : (tripleCharges (sourceA2552 + difference 3 2) (sourceB2552 + difference 2 3) sourceC2552) = raw35269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35269; decide +kernel
    rw [ha]
    exact (canonical35269 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2552 + difference 3 4) (sourceB2552 + difference 4 3) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 3 4) (sourceB2552 + difference 4 3) sourceC2552) = raw35016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35016; decide +kernel
    rw [ha]
    exact (canonical35016 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2552 + difference 3 5) (sourceB2552 + difference 5 3) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 3 5) (sourceB2552 + difference 5 3) sourceC2552) = raw35270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35270; decide +kernel
    rw [ha]
    exact (canonical35270 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2552 + difference 4 0) (sourceB2552 + difference 0 4) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2552 + difference 4 0) (sourceB2552 + difference 0 4) sourceC2552) = raw34902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34902; decide +kernel
    rw [ha]
    exact (canonical34902 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2552 + difference 4 1) (sourceB2552 + difference 1 4) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2552 + difference 4 1) (sourceB2552 + difference 1 4) sourceC2552) = raw35271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35271; decide +kernel
    rw [ha]
    exact (canonical35271 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2552 + difference 4 2) (sourceB2552 + difference 2 4) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 4 2) (sourceB2552 + difference 2 4) sourceC2552) = raw35272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35272; decide +kernel
    rw [ha]
    exact (canonical35272 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2552 + difference 4 3) (sourceB2552 + difference 3 4) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 4 3) (sourceB2552 + difference 3 4) sourceC2552) = raw35273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35273; decide +kernel
    rw [ha]
    exact (canonical35273 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2552 + difference 4 5) (sourceB2552 + difference 5 4) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2552 + difference 4 5) (sourceB2552 + difference 5 4) sourceC2552) = raw35274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35274; decide +kernel
    rw [ha]
    exact (canonical35274 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2552 + difference 5 0) (sourceB2552 + difference 0 5) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2552 + difference 5 0) (sourceB2552 + difference 0 5) sourceC2552) = raw34838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34838; decide +kernel
    rw [ha]
    exact (canonical34838 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2552 + difference 5 1) (sourceB2552 + difference 1 5) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2552 + difference 5 1) (sourceB2552 + difference 1 5) sourceC2552) = raw35275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35275; decide +kernel
    rw [ha]
    exact (canonical35275 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2552 + difference 5 2) (sourceB2552 + difference 2 5) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 5 2) (sourceB2552 + difference 2 5) sourceC2552) = raw35276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35276; decide +kernel
    rw [ha]
    exact (canonical35276 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2552 + difference 5 3) (sourceB2552 + difference 3 5) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2552 + difference 5 3) (sourceB2552 + difference 3 5) sourceC2552) = raw35277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw35277; decide +kernel
    rw [ha]
    exact (canonical35277 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2552 + difference 5 4) (sourceB2552 + difference 4 5) sourceC2552) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2552 + difference 5 4) (sourceB2552 + difference 4 5) sourceC2552) = raw34817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2552 sourceB2552 sourceC2552 difference raw34817; decide +kernel
    rw [ha]
    exact (canonical34817 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2552 sourceB2552 sourceC2552
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2552, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2553 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2553 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2553 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2553 : Integer.Sparse Master := [(Sum.inr 4932, 1), (Sum.inr 4933, 2), (Sum.inr 4934, 2), (Sum.inr 4935, 2), (Sum.inr 4950, 1), (Sum.inr 4951, 2), (Sum.inr 4958, 1), (Sum.inr 4974, 1), (Sum.inr 5081, 1), (Sum.inr 5152, 2), (Sum.inr 5189, 1), (Sum.inr 5337, 1), (Sum.inr 5340, 1), (Sum.inr 5352, 2), (Sum.inr 5369, 2), (Sum.inr 5393, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 2), (Sum.inr 5459, 1), (Sum.inr 5463, 1), (Sum.inr 5473, 2)]

theorem sourceEq2553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2553 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2553 + difference 0 1) (sourceB2553 + difference 1 0) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2553 + difference 0 1) (sourceB2553 + difference 1 0) sourceC2553) = raw35278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35278; decide +kernel
    rw [ha]
    exact (canonical35278 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2553 + difference 0 2) (sourceB2553 + difference 2 0) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2553 + difference 0 2) (sourceB2553 + difference 2 0) sourceC2553) = raw35279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35279; decide +kernel
    rw [ha]
    exact (canonical35279 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2553 + difference 0 3) (sourceB2553 + difference 3 0) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2553 + difference 0 3) (sourceB2553 + difference 3 0) sourceC2553) = raw35280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35280; decide +kernel
    rw [ha]
    exact (canonical35280 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2553 + difference 0 4) (sourceB2553 + difference 4 0) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2553 + difference 0 4) (sourceB2553 + difference 4 0) sourceC2553) = raw17703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw17703; decide +kernel
    rw [ha]
    exact (canonical17703 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2553 + difference 0 5) (sourceB2553 + difference 5 0) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2553 + difference 0 5) (sourceB2553 + difference 5 0) sourceC2553) = raw35281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35281; decide +kernel
    rw [ha]
    exact (canonical35281 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2553 + difference 1 0) (sourceB2553 + difference 0 1) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2553 + difference 1 0) (sourceB2553 + difference 0 1) sourceC2553) = raw17723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw17723; decide +kernel
    rw [ha]
    exact (canonical17723 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2553 + difference 1 2) (sourceB2553 + difference 2 1) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2553 + difference 1 2) (sourceB2553 + difference 2 1) sourceC2553) = raw17725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw17725; decide +kernel
    rw [ha]
    exact (canonical17725 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2553 + difference 1 3) (sourceB2553 + difference 3 1) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2553 + difference 1 3) (sourceB2553 + difference 3 1) sourceC2553) = raw17726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw17726; decide +kernel
    rw [ha]
    exact (canonical17726 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2553 + difference 1 4) (sourceB2553 + difference 4 1) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2553 + difference 1 4) (sourceB2553 + difference 4 1) sourceC2553) = raw29735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw29735; decide +kernel
    rw [ha]
    exact (canonical29735 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2553 + difference 1 5) (sourceB2553 + difference 5 1) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2553 + difference 1 5) (sourceB2553 + difference 5 1) sourceC2553) = raw17727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw17727; decide +kernel
    rw [ha]
    exact (canonical17727 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2553 + difference 2 0) (sourceB2553 + difference 0 2) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2553 + difference 2 0) (sourceB2553 + difference 0 2) sourceC2553) = raw29741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw29741; decide +kernel
    rw [ha]
    exact (canonical29741 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2553 + difference 2 1) (sourceB2553 + difference 1 2) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2553 + difference 2 1) (sourceB2553 + difference 1 2) sourceC2553) = raw35282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35282; decide +kernel
    rw [ha]
    exact (canonical35282 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2553 + difference 2 3) (sourceB2553 + difference 3 2) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2553 + difference 2 3) (sourceB2553 + difference 3 2) sourceC2553) = raw35283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35283; decide +kernel
    rw [ha]
    exact (canonical35283 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2553 + difference 2 4) (sourceB2553 + difference 4 2) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5459) := by
    have ha : (tripleCharges (sourceA2553 + difference 2 4) (sourceB2553 + difference 4 2) sourceC2553) = raw17714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw17714; decide +kernel
    rw [ha]
    exact (canonical17714 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2553 + difference 2 5) (sourceB2553 + difference 5 2) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2553 + difference 2 5) (sourceB2553 + difference 5 2) sourceC2553) = raw35284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35284; decide +kernel
    rw [ha]
    exact (canonical35284 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2553 + difference 3 0) (sourceB2553 + difference 0 3) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2553 + difference 3 0) (sourceB2553 + difference 0 3) sourceC2553) = raw29745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw29745; decide +kernel
    rw [ha]
    exact (canonical29745 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2553 + difference 3 1) (sourceB2553 + difference 1 3) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2553 + difference 3 1) (sourceB2553 + difference 1 3) sourceC2553) = raw35285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35285; decide +kernel
    rw [ha]
    exact (canonical35285 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2553 + difference 3 2) (sourceB2553 + difference 2 3) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5340) := by
    have ha : (tripleCharges (sourceA2553 + difference 3 2) (sourceB2553 + difference 2 3) sourceC2553) = raw35286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35286; decide +kernel
    rw [ha]
    exact (canonical35286 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2553 + difference 3 4) (sourceB2553 + difference 4 3) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5463) := by
    have ha : (tripleCharges (sourceA2553 + difference 3 4) (sourceB2553 + difference 4 3) sourceC2553) = raw17719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw17719; decide +kernel
    rw [ha]
    exact (canonical17719 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2553 + difference 3 5) (sourceB2553 + difference 5 3) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2553 + difference 3 5) (sourceB2553 + difference 5 3) sourceC2553) = raw35287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35287; decide +kernel
    rw [ha]
    exact (canonical35287 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2553 + difference 4 0) (sourceB2553 + difference 0 4) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA2553 + difference 4 0) (sourceB2553 + difference 0 4) sourceC2553) = raw29749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw29749; decide +kernel
    rw [ha]
    exact (canonical29749 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2553 + difference 4 1) (sourceB2553 + difference 1 4) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA2553 + difference 4 1) (sourceB2553 + difference 1 4) sourceC2553) = raw35288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35288; decide +kernel
    rw [ha]
    exact (canonical35288 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2553 + difference 4 2) (sourceB2553 + difference 2 4) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4932) := by
    have ha : (tripleCharges (sourceA2553 + difference 4 2) (sourceB2553 + difference 2 4) sourceC2553) = raw35289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35289; decide +kernel
    rw [ha]
    exact (canonical35289 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2553 + difference 4 3) (sourceB2553 + difference 3 4) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2553 + difference 4 3) (sourceB2553 + difference 3 4) sourceC2553) = raw35290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35290; decide +kernel
    rw [ha]
    exact (canonical35290 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2553 + difference 4 5) (sourceB2553 + difference 5 4) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2553 + difference 4 5) (sourceB2553 + difference 5 4) sourceC2553) = raw35291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35291; decide +kernel
    rw [ha]
    exact (canonical35291 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2553 + difference 5 0) (sourceB2553 + difference 0 5) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2553 + difference 5 0) (sourceB2553 + difference 0 5) sourceC2553) = raw29754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw29754; decide +kernel
    rw [ha]
    exact (canonical29754 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2553 + difference 5 1) (sourceB2553 + difference 1 5) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2553 + difference 5 1) (sourceB2553 + difference 1 5) sourceC2553) = raw35292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35292; decide +kernel
    rw [ha]
    exact (canonical35292 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2553 + difference 5 2) (sourceB2553 + difference 2 5) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4958) := by
    have ha : (tripleCharges (sourceA2553 + difference 5 2) (sourceB2553 + difference 2 5) sourceC2553) = raw35293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35293; decide +kernel
    rw [ha]
    exact (canonical35293 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2553 + difference 5 3) (sourceB2553 + difference 3 5) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2553 + difference 5 3) (sourceB2553 + difference 3 5) sourceC2553) = raw35294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw35294; decide +kernel
    rw [ha]
    exact (canonical35294 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2553 + difference 5 4) (sourceB2553 + difference 4 5) sourceC2553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2553 + difference 5 4) (sourceB2553 + difference 4 5) sourceC2553) = raw17729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2553 sourceB2553 sourceC2553 difference raw17729; decide +kernel
    rw [ha]
    exact (canonical17729 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2553 sourceB2553 sourceC2553
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2553, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2554 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2554 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2554 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2554 : Integer.Sparse Master := [(Sum.inr 2324, 2), (Sum.inr 2325, 2), (Sum.inr 2326, 2), (Sum.inr 2343, 2), (Sum.inr 2351, 1), (Sum.inr 2360, 1), (Sum.inr 2576, 2), (Sum.inr 2621, 1), (Sum.inr 2825, 1), (Sum.inr 2830, 1), (Sum.inr 2991, 1), (Sum.inr 3918, 1), (Sum.inr 3919, 1), (Sum.inr 3923, 1), (Sum.inr 3925, 1), (Sum.inr 3929, 1), (Sum.inr 3932, 1), (Sum.inr 3936, 2), (Sum.inr 3940, 2), (Sum.inr 3995, 2), (Sum.inr 3996, 2)]

theorem sourceEq2554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2554 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2554 + difference 0 1) (sourceB2554 + difference 1 0) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA2554 + difference 0 1) (sourceB2554 + difference 1 0) sourceC2554) = raw35295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35295; decide +kernel
    rw [ha]
    exact (canonical35295 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2554 + difference 0 2) (sourceB2554 + difference 2 0) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3936) := by
    have ha : (tripleCharges (sourceA2554 + difference 0 2) (sourceB2554 + difference 2 0) sourceC2554) = raw35296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35296; decide +kernel
    rw [ha]
    exact (canonical35296 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2554 + difference 0 3) (sourceB2554 + difference 3 0) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3940) := by
    have ha : (tripleCharges (sourceA2554 + difference 0 3) (sourceB2554 + difference 3 0) sourceC2554) = raw35297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35297; decide +kernel
    rw [ha]
    exact (canonical35297 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2554 + difference 0 4) (sourceB2554 + difference 4 0) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA2554 + difference 0 4) (sourceB2554 + difference 4 0) sourceC2554) = raw35298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35298; decide +kernel
    rw [ha]
    exact (canonical35298 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2554 + difference 0 5) (sourceB2554 + difference 5 0) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA2554 + difference 0 5) (sourceB2554 + difference 5 0) sourceC2554) = raw35299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35299; decide +kernel
    rw [ha]
    exact (canonical35299 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2554 + difference 1 0) (sourceB2554 + difference 0 1) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA2554 + difference 1 0) (sourceB2554 + difference 0 1) sourceC2554) = raw35300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35300; decide +kernel
    rw [ha]
    exact (canonical35300 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2554 + difference 1 2) (sourceB2554 + difference 2 1) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3936) := by
    have ha : (tripleCharges (sourceA2554 + difference 1 2) (sourceB2554 + difference 2 1) sourceC2554) = raw29758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw29758; decide +kernel
    rw [ha]
    exact (canonical29758 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2554 + difference 1 3) (sourceB2554 + difference 3 1) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3940) := by
    have ha : (tripleCharges (sourceA2554 + difference 1 3) (sourceB2554 + difference 3 1) sourceC2554) = raw29759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw29759; decide +kernel
    rw [ha]
    exact (canonical29759 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2554 + difference 1 4) (sourceB2554 + difference 4 1) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA2554 + difference 1 4) (sourceB2554 + difference 4 1) sourceC2554) = raw29760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw29760; decide +kernel
    rw [ha]
    exact (canonical29760 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2554 + difference 1 5) (sourceB2554 + difference 5 1) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA2554 + difference 1 5) (sourceB2554 + difference 5 1) sourceC2554) = raw29761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw29761; decide +kernel
    rw [ha]
    exact (canonical29761 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2554 + difference 2 0) (sourceB2554 + difference 0 2) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2324) := by
    have ha : (tripleCharges (sourceA2554 + difference 2 0) (sourceB2554 + difference 0 2) sourceC2554) = raw29768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw29768; decide +kernel
    rw [ha]
    exact (canonical29768 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2554 + difference 2 1) (sourceB2554 + difference 1 2) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2324) := by
    have ha : (tripleCharges (sourceA2554 + difference 2 1) (sourceB2554 + difference 1 2) sourceC2554) = raw35301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35301; decide +kernel
    rw [ha]
    exact (canonical35301 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2554 + difference 2 3) (sourceB2554 + difference 3 2) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3919) := by
    have ha : (tripleCharges (sourceA2554 + difference 2 3) (sourceB2554 + difference 3 2) sourceC2554) = raw35302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35302; decide +kernel
    rw [ha]
    exact (canonical35302 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2554 + difference 2 4) (sourceB2554 + difference 4 2) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3923) := by
    have ha : (tripleCharges (sourceA2554 + difference 2 4) (sourceB2554 + difference 4 2) sourceC2554) = raw35303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35303; decide +kernel
    rw [ha]
    exact (canonical35303 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2554 + difference 2 5) (sourceB2554 + difference 5 2) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3925) := by
    have ha : (tripleCharges (sourceA2554 + difference 2 5) (sourceB2554 + difference 5 2) sourceC2554) = raw35304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35304; decide +kernel
    rw [ha]
    exact (canonical35304 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2554 + difference 3 0) (sourceB2554 + difference 0 3) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2343) := by
    have ha : (tripleCharges (sourceA2554 + difference 3 0) (sourceB2554 + difference 0 3) sourceC2554) = raw29773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw29773; decide +kernel
    rw [ha]
    exact (canonical29773 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2554 + difference 3 1) (sourceB2554 + difference 1 3) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2343) := by
    have ha : (tripleCharges (sourceA2554 + difference 3 1) (sourceB2554 + difference 1 3) sourceC2554) = raw35305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35305; decide +kernel
    rw [ha]
    exact (canonical35305 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2554 + difference 3 2) (sourceB2554 + difference 2 3) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3918) := by
    have ha : (tripleCharges (sourceA2554 + difference 3 2) (sourceB2554 + difference 2 3) sourceC2554) = raw35306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35306; decide +kernel
    rw [ha]
    exact (canonical35306 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2554 + difference 3 4) (sourceB2554 + difference 4 3) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3929) := by
    have ha : (tripleCharges (sourceA2554 + difference 3 4) (sourceB2554 + difference 4 3) sourceC2554) = raw35307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35307; decide +kernel
    rw [ha]
    exact (canonical35307 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2554 + difference 3 5) (sourceB2554 + difference 5 3) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3932) := by
    have ha : (tripleCharges (sourceA2554 + difference 3 5) (sourceB2554 + difference 5 3) sourceC2554) = raw35308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35308; decide +kernel
    rw [ha]
    exact (canonical35308 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2554 + difference 4 0) (sourceB2554 + difference 0 4) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA2554 + difference 4 0) (sourceB2554 + difference 0 4) sourceC2554) = raw29778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw29778; decide +kernel
    rw [ha]
    exact (canonical29778 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2554 + difference 4 1) (sourceB2554 + difference 1 4) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA2554 + difference 4 1) (sourceB2554 + difference 1 4) sourceC2554) = raw35309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35309; decide +kernel
    rw [ha]
    exact (canonical35309 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2554 + difference 4 2) (sourceB2554 + difference 2 4) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2825) := by
    have ha : (tripleCharges (sourceA2554 + difference 4 2) (sourceB2554 + difference 2 4) sourceC2554) = raw35310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35310; decide +kernel
    rw [ha]
    exact (canonical35310 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2554 + difference 4 3) (sourceB2554 + difference 3 4) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2830) := by
    have ha : (tripleCharges (sourceA2554 + difference 4 3) (sourceB2554 + difference 3 4) sourceC2554) = raw35311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35311; decide +kernel
    rw [ha]
    exact (canonical35311 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2554 + difference 4 5) (sourceB2554 + difference 5 4) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2991) := by
    have ha : (tripleCharges (sourceA2554 + difference 4 5) (sourceB2554 + difference 5 4) sourceC2554) = raw35312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35312; decide +kernel
    rw [ha]
    exact (canonical35312 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2554 + difference 5 0) (sourceB2554 + difference 0 5) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2325) := by
    have ha : (tripleCharges (sourceA2554 + difference 5 0) (sourceB2554 + difference 0 5) sourceC2554) = raw29783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw29783; decide +kernel
    rw [ha]
    exact (canonical29783 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2554 + difference 5 1) (sourceB2554 + difference 1 5) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2325) := by
    have ha : (tripleCharges (sourceA2554 + difference 5 1) (sourceB2554 + difference 1 5) sourceC2554) = raw35313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35313; decide +kernel
    rw [ha]
    exact (canonical35313 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2554 + difference 5 2) (sourceB2554 + difference 2 5) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2351) := by
    have ha : (tripleCharges (sourceA2554 + difference 5 2) (sourceB2554 + difference 2 5) sourceC2554) = raw35314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35314; decide +kernel
    rw [ha]
    exact (canonical35314 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2554 + difference 5 3) (sourceB2554 + difference 3 5) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2360) := by
    have ha : (tripleCharges (sourceA2554 + difference 5 3) (sourceB2554 + difference 3 5) sourceC2554) = raw35315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35315; decide +kernel
    rw [ha]
    exact (canonical35315 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2554 + difference 5 4) (sourceB2554 + difference 4 5) sourceC2554) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA2554 + difference 5 4) (sourceB2554 + difference 4 5) sourceC2554) = raw35316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2554 sourceB2554 sourceC2554 difference raw35316; decide +kernel
    rw [ha]
    exact (canonical35316 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2554 sourceB2554 sourceC2554
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2554, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2555 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2555 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2555 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2555 : Integer.Sparse Master := [(Sum.inr 3409, 1), (Sum.inr 3414, 2), (Sum.inr 3415, 2), (Sum.inr 3418, 2), (Sum.inr 3419, 2), (Sum.inr 3421, 1), (Sum.inr 3482, 1), (Sum.inr 3511, 1), (Sum.inr 3542, 1), (Sum.inr 3592, 1), (Sum.inr 3612, 2), (Sum.inr 3756, 1), (Sum.inr 3763, 1), (Sum.inr 3764, 2), (Sum.inr 3774, 2), (Sum.inr 3797, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 2), (Sum.inr 3951, 1), (Sum.inr 3960, 1), (Sum.inr 3961, 2)]

theorem sourceEq2555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2555 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 1) (sourceB2555 + difference 1 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 1) (sourceB2555 + difference 1 0) sourceC2555) = raw35317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35317; decide +kernel
    rw [ha]
    exact (canonical35317 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 2) (sourceB2555 + difference 2 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 2) (sourceB2555 + difference 2 0) sourceC2555) = raw35318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35318; decide +kernel
    rw [ha]
    exact (canonical35318 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 3) (sourceB2555 + difference 3 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 3) (sourceB2555 + difference 3 0) sourceC2555) = raw35319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35319; decide +kernel
    rw [ha]
    exact (canonical35319 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 4) (sourceB2555 + difference 4 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 4) (sourceB2555 + difference 4 0) sourceC2555) = raw17733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17733; decide +kernel
    rw [ha]
    exact (canonical17733 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2555 + difference 0 5) (sourceB2555 + difference 5 0) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2555 + difference 0 5) (sourceB2555 + difference 5 0) sourceC2555) = raw35320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35320; decide +kernel
    rw [ha]
    exact (canonical35320 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 0) (sourceB2555 + difference 0 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 0) (sourceB2555 + difference 0 1) sourceC2555) = raw17753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17753; decide +kernel
    rw [ha]
    exact (canonical17753 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 2) (sourceB2555 + difference 2 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 2) (sourceB2555 + difference 2 1) sourceC2555) = raw17755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17755; decide +kernel
    rw [ha]
    exact (canonical17755 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 3) (sourceB2555 + difference 3 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 3) (sourceB2555 + difference 3 1) sourceC2555) = raw17756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17756; decide +kernel
    rw [ha]
    exact (canonical17756 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 4) (sourceB2555 + difference 4 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 4) (sourceB2555 + difference 4 1) sourceC2555) = raw29787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29787; decide +kernel
    rw [ha]
    exact (canonical29787 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2555 + difference 1 5) (sourceB2555 + difference 5 1) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2555 + difference 1 5) (sourceB2555 + difference 5 1) sourceC2555) = raw17757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17757; decide +kernel
    rw [ha]
    exact (canonical17757 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 0) (sourceB2555 + difference 0 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 0) (sourceB2555 + difference 0 2) sourceC2555) = raw29793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29793; decide +kernel
    rw [ha]
    exact (canonical29793 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 1) (sourceB2555 + difference 1 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 1) (sourceB2555 + difference 1 2) sourceC2555) = raw35321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35321; decide +kernel
    rw [ha]
    exact (canonical35321 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 3) (sourceB2555 + difference 3 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3756) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 3) (sourceB2555 + difference 3 2) sourceC2555) = raw35322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35322; decide +kernel
    rw [ha]
    exact (canonical35322 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 4) (sourceB2555 + difference 4 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3951) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 4) (sourceB2555 + difference 4 2) sourceC2555) = raw17744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17744; decide +kernel
    rw [ha]
    exact (canonical17744 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2555 + difference 2 5) (sourceB2555 + difference 5 2) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3797) := by
    have ha : (tripleCharges (sourceA2555 + difference 2 5) (sourceB2555 + difference 5 2) sourceC2555) = raw35323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35323; decide +kernel
    rw [ha]
    exact (canonical35323 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 0) (sourceB2555 + difference 0 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 0) (sourceB2555 + difference 0 3) sourceC2555) = raw29797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29797; decide +kernel
    rw [ha]
    exact (canonical29797 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 1) (sourceB2555 + difference 1 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 1) (sourceB2555 + difference 1 3) sourceC2555) = raw35324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35324; decide +kernel
    rw [ha]
    exact (canonical35324 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 2) (sourceB2555 + difference 2 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3763) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 2) (sourceB2555 + difference 2 3) sourceC2555) = raw35325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35325; decide +kernel
    rw [ha]
    exact (canonical35325 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 4) (sourceB2555 + difference 4 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3960) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 4) (sourceB2555 + difference 4 3) sourceC2555) = raw17749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17749; decide +kernel
    rw [ha]
    exact (canonical17749 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2555 + difference 3 5) (sourceB2555 + difference 5 3) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA2555 + difference 3 5) (sourceB2555 + difference 5 3) sourceC2555) = raw35326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35326; decide +kernel
    rw [ha]
    exact (canonical35326 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 0) (sourceB2555 + difference 0 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 0) (sourceB2555 + difference 0 4) sourceC2555) = raw29801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29801; decide +kernel
    rw [ha]
    exact (canonical29801 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 1) (sourceB2555 + difference 1 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 1) (sourceB2555 + difference 1 4) sourceC2555) = raw35327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35327; decide +kernel
    rw [ha]
    exact (canonical35327 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 2) (sourceB2555 + difference 2 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3409) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 2) (sourceB2555 + difference 2 4) sourceC2555) = raw35328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35328; decide +kernel
    rw [ha]
    exact (canonical35328 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 3) (sourceB2555 + difference 3 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3421) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 3) (sourceB2555 + difference 3 4) sourceC2555) = raw35329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35329; decide +kernel
    rw [ha]
    exact (canonical35329 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2555 + difference 4 5) (sourceB2555 + difference 5 4) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2555 + difference 4 5) (sourceB2555 + difference 5 4) sourceC2555) = raw35330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35330; decide +kernel
    rw [ha]
    exact (canonical35330 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 0) (sourceB2555 + difference 0 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 0) (sourceB2555 + difference 0 5) sourceC2555) = raw29806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw29806; decide +kernel
    rw [ha]
    exact (canonical29806 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 1) (sourceB2555 + difference 1 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 1) (sourceB2555 + difference 1 5) sourceC2555) = raw35331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35331; decide +kernel
    rw [ha]
    exact (canonical35331 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 2) (sourceB2555 + difference 2 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 2) (sourceB2555 + difference 2 5) sourceC2555) = raw35332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35332; decide +kernel
    rw [ha]
    exact (canonical35332 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 3) (sourceB2555 + difference 3 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 3) (sourceB2555 + difference 3 5) sourceC2555) = raw35333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw35333; decide +kernel
    rw [ha]
    exact (canonical35333 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2555 + difference 5 4) (sourceB2555 + difference 4 5) sourceC2555) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2555 + difference 5 4) (sourceB2555 + difference 4 5) sourceC2555) = raw17759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2555 sourceB2555 sourceC2555 difference raw17759; decide +kernel
    rw [ha]
    exact (canonical17759 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2555 sourceB2555 sourceC2555
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2555, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2556 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2556 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2556 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2556 : Integer.Sparse Master := [(Sum.inr 2822, 2), (Sum.inr 3672, 1), (Sum.inr 3694, 1), (Sum.inr 3779, 1), (Sum.inr 3920, 1), (Sum.inr 4091, -1)]

theorem sourceEq2556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2556 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 0) (sourceB2556 + difference 0 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 0) (sourceB2556 + difference 0 2) sourceC2556) = raw29810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw29810; decide +kernel
    rw [ha]
    exact (canonical29810 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 1) (sourceB2556 + difference 1 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 1) (sourceB2556 + difference 1 2) sourceC2556) = raw35334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw35334; decide +kernel
    rw [ha]
    exact (canonical35334 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 2) (sourceB2556 + difference 2 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 2) (sourceB2556 + difference 2 2) sourceC2556) = raw29809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw29809; decide +kernel
    rw [ha]
    exact (canonical29809 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 3) (sourceB2556 + difference 3 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3672) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 3) (sourceB2556 + difference 3 2) sourceC2556) = raw35335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw35335; decide +kernel
    rw [ha]
    exact (canonical35335 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 4) (sourceB2556 + difference 4 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3920) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 4) (sourceB2556 + difference 4 2) sourceC2556) = raw35336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw35336; decide +kernel
    rw [ha]
    exact (canonical35336 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2556 + difference 2 5) (sourceB2556 + difference 5 2) sourceC2556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2556 + difference 2 5) (sourceB2556 + difference 5 2) sourceC2556) = raw35337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2556 sourceB2556 sourceC2556 difference raw35337; decide +kernel
    rw [ha]
    exact (canonical35337 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2556 + sourceB2556) sourceC2556) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2556 + sourceB2556) sourceC2556) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2556 sourceB2556 sourceC2556 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2556 sourceB2556 sourceC2556
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2556, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2557 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2557 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2557 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2557 : Integer.Sparse Master := [(Sum.inr 2322, 1), (Sum.inr 2799, 1), (Sum.inr 3675, 1), (Sum.inr 3690, 2), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

theorem sourceEq2557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2557 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2557 + difference 0 2) (sourceB2557 + difference 2 0) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2557 + difference 0 2) (sourceB2557 + difference 2 0) sourceC2557) = raw35338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35338; decide +kernel
    rw [ha]
    exact (canonical35338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2557 + difference 1 2) (sourceB2557 + difference 2 1) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2557 + difference 1 2) (sourceB2557 + difference 2 1) sourceC2557) = raw35339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35339; decide +kernel
    rw [ha]
    exact (canonical35339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2557 + difference 2 2) (sourceB2557 + difference 2 2) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2557 + difference 2 2) (sourceB2557 + difference 2 2) sourceC2557) = raw29809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw29809; decide +kernel
    rw [ha]
    exact (canonical29809 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2557 + difference 3 2) (sourceB2557 + difference 2 3) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3675) := by
    have ha : (tripleCharges (sourceA2557 + difference 3 2) (sourceB2557 + difference 2 3) sourceC2557) = raw35340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35340; decide +kernel
    rw [ha]
    exact (canonical35340 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2557 + difference 4 2) (sourceB2557 + difference 2 4) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2322) := by
    have ha : (tripleCharges (sourceA2557 + difference 4 2) (sourceB2557 + difference 2 4) sourceC2557) = raw35341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35341; decide +kernel
    rw [ha]
    exact (canonical35341 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2557 + difference 5 2) (sourceB2557 + difference 2 5) sourceC2557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2799) := by
    have ha : (tripleCharges (sourceA2557 + difference 5 2) (sourceB2557 + difference 2 5) sourceC2557) = raw35342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2557 sourceB2557 sourceC2557 difference raw35342; decide +kernel
    rw [ha]
    exact (canonical35342 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2557 + sourceB2557) sourceC2557) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2557 + sourceB2557) sourceC2557) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2557 sourceB2557 sourceC2557 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2557 sourceB2557 sourceC2557
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2557, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2558 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2558 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2558 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2558 : Integer.Sparse Master := [(Sum.inr 2827, 2), (Sum.inr 3675, 1), (Sum.inr 3694, 1), (Sum.inr 3790, 1), (Sum.inr 3929, 1), (Sum.inr 4091, -1)]

theorem sourceEq2558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2558 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 0) (sourceB2558 + difference 0 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2827) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 0) (sourceB2558 + difference 0 3) sourceC2558) = raw29811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw29811; decide +kernel
    rw [ha]
    exact (canonical29811 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 1) (sourceB2558 + difference 1 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2827) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 1) (sourceB2558 + difference 1 3) sourceC2558) = raw35343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw35343; decide +kernel
    rw [ha]
    exact (canonical35343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 2) (sourceB2558 + difference 2 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3675) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 2) (sourceB2558 + difference 2 3) sourceC2558) = raw35340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw35340; decide +kernel
    rw [ha]
    exact (canonical35340 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 3) (sourceB2558 + difference 3 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 3) (sourceB2558 + difference 3 3) sourceC2558) = raw29809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw29809; decide +kernel
    rw [ha]
    exact (canonical29809 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 4) (sourceB2558 + difference 4 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3929) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 4) (sourceB2558 + difference 4 3) sourceC2558) = raw35344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw35344; decide +kernel
    rw [ha]
    exact (canonical35344 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2558 + difference 3 5) (sourceB2558 + difference 5 3) sourceC2558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2558 + difference 3 5) (sourceB2558 + difference 5 3) sourceC2558) = raw35345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2558 sourceB2558 sourceC2558 difference raw35345; decide +kernel
    rw [ha]
    exact (canonical35345 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2558 + sourceB2558) sourceC2558) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2558 + sourceB2558) sourceC2558) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2558 sourceB2558 sourceC2558 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2558 sourceB2558 sourceC2558
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2558, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2559 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2559 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC2559 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm2559 : Integer.Sparse Master := [(Sum.inr 4635, 1), (Sum.inr 4637, 2), (Sum.inr 4654, 1), (Sum.inr 4811, 1), (Sum.inr 4906, 1), (Sum.inr 4907, 2), (Sum.inr 4923, 1), (Sum.inr 4928, 2), (Sum.inr 4946, 2), (Sum.inr 5081, 1), (Sum.inr 5141, 2), (Sum.inr 5334, 1), (Sum.inr 5337, 1), (Sum.inr 5352, 2), (Sum.inr 5368, 2), (Sum.inr 5393, 1), (Sum.inr 5418, 1), (Sum.inr 5434, 2), (Sum.inr 5460, 1), (Sum.inr 5465, 1), (Sum.inr 5483, 2)]

theorem sourceEq2559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2559 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2559 + difference 0 1) (sourceB2559 + difference 1 0) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2559 + difference 0 1) (sourceB2559 + difference 1 0) sourceC2559) = raw35346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35346; decide +kernel
    rw [ha]
    exact (canonical35346 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2559 + difference 0 2) (sourceB2559 + difference 2 0) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2559 + difference 0 2) (sourceB2559 + difference 2 0) sourceC2559) = raw35347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35347; decide +kernel
    rw [ha]
    exact (canonical35347 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2559 + difference 0 3) (sourceB2559 + difference 3 0) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2559 + difference 0 3) (sourceB2559 + difference 3 0) sourceC2559) = raw35348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35348; decide +kernel
    rw [ha]
    exact (canonical35348 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2559 + difference 0 4) (sourceB2559 + difference 4 0) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2559 + difference 0 4) (sourceB2559 + difference 4 0) sourceC2559) = raw17086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw17086; decide +kernel
    rw [ha]
    exact (canonical17086 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2559 + difference 0 5) (sourceB2559 + difference 5 0) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2559 + difference 0 5) (sourceB2559 + difference 5 0) sourceC2559) = raw35349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35349; decide +kernel
    rw [ha]
    exact (canonical35349 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2559 + difference 1 0) (sourceB2559 + difference 0 1) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2559 + difference 1 0) (sourceB2559 + difference 0 1) sourceC2559) = raw9861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw9861; decide +kernel
    rw [ha]
    exact (canonical9861 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2559 + difference 1 2) (sourceB2559 + difference 2 1) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2559 + difference 1 2) (sourceB2559 + difference 2 1) sourceC2559) = raw17097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw17097; decide +kernel
    rw [ha]
    exact (canonical17097 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2559 + difference 1 3) (sourceB2559 + difference 3 1) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2559 + difference 1 3) (sourceB2559 + difference 3 1) sourceC2559) = raw17098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw17098; decide +kernel
    rw [ha]
    exact (canonical17098 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2559 + difference 1 4) (sourceB2559 + difference 4 1) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2559 + difference 1 4) (sourceB2559 + difference 4 1) sourceC2559) = raw3145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw3145; decide +kernel
    rw [ha]
    exact (canonical3145 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2559 + difference 1 5) (sourceB2559 + difference 5 1) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2559 + difference 1 5) (sourceB2559 + difference 5 1) sourceC2559) = raw3140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw3140; decide +kernel
    rw [ha]
    exact (canonical3140 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2559 + difference 2 0) (sourceB2559 + difference 0 2) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2559 + difference 2 0) (sourceB2559 + difference 0 2) sourceC2559) = raw30140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw30140; decide +kernel
    rw [ha]
    exact (canonical30140 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2559 + difference 2 1) (sourceB2559 + difference 1 2) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2559 + difference 2 1) (sourceB2559 + difference 1 2) sourceC2559) = raw35350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35350; decide +kernel
    rw [ha]
    exact (canonical35350 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2559 + difference 2 3) (sourceB2559 + difference 3 2) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5334) := by
    have ha : (tripleCharges (sourceA2559 + difference 2 3) (sourceB2559 + difference 3 2) sourceC2559) = raw35351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35351; decide +kernel
    rw [ha]
    exact (canonical35351 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2559 + difference 2 4) (sourceB2559 + difference 4 2) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2559 + difference 2 4) (sourceB2559 + difference 4 2) sourceC2559) = raw17090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw17090; decide +kernel
    rw [ha]
    exact (canonical17090 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2559 + difference 2 5) (sourceB2559 + difference 5 2) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2559 + difference 2 5) (sourceB2559 + difference 5 2) sourceC2559) = raw35352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35352; decide +kernel
    rw [ha]
    exact (canonical35352 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2559 + difference 3 0) (sourceB2559 + difference 0 3) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2559 + difference 3 0) (sourceB2559 + difference 0 3) sourceC2559) = raw30144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw30144; decide +kernel
    rw [ha]
    exact (canonical30144 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2559 + difference 3 1) (sourceB2559 + difference 1 3) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2559 + difference 3 1) (sourceB2559 + difference 1 3) sourceC2559) = raw35353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35353; decide +kernel
    rw [ha]
    exact (canonical35353 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2559 + difference 3 2) (sourceB2559 + difference 2 3) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2559 + difference 3 2) (sourceB2559 + difference 2 3) sourceC2559) = raw35354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35354; decide +kernel
    rw [ha]
    exact (canonical35354 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2559 + difference 3 4) (sourceB2559 + difference 4 3) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2559 + difference 3 4) (sourceB2559 + difference 4 3) sourceC2559) = raw17093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw17093; decide +kernel
    rw [ha]
    exact (canonical17093 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2559 + difference 3 5) (sourceB2559 + difference 5 3) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2559 + difference 3 5) (sourceB2559 + difference 5 3) sourceC2559) = raw35355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35355; decide +kernel
    rw [ha]
    exact (canonical35355 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2559 + difference 4 0) (sourceB2559 + difference 0 4) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2559 + difference 4 0) (sourceB2559 + difference 0 4) sourceC2559) = raw30148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw30148; decide +kernel
    rw [ha]
    exact (canonical30148 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2559 + difference 4 1) (sourceB2559 + difference 1 4) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2559 + difference 4 1) (sourceB2559 + difference 1 4) sourceC2559) = raw35356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35356; decide +kernel
    rw [ha]
    exact (canonical35356 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2559 + difference 4 2) (sourceB2559 + difference 2 4) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4635) := by
    have ha : (tripleCharges (sourceA2559 + difference 4 2) (sourceB2559 + difference 2 4) sourceC2559) = raw35357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35357; decide +kernel
    rw [ha]
    exact (canonical35357 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2559 + difference 4 3) (sourceB2559 + difference 3 4) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4654) := by
    have ha : (tripleCharges (sourceA2559 + difference 4 3) (sourceB2559 + difference 3 4) sourceC2559) = raw35358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35358; decide +kernel
    rw [ha]
    exact (canonical35358 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2559 + difference 4 5) (sourceB2559 + difference 5 4) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2559 + difference 4 5) (sourceB2559 + difference 5 4) sourceC2559) = raw35359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35359; decide +kernel
    rw [ha]
    exact (canonical35359 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2559 + difference 5 0) (sourceB2559 + difference 0 5) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2559 + difference 5 0) (sourceB2559 + difference 0 5) sourceC2559) = raw28773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw28773; decide +kernel
    rw [ha]
    exact (canonical28773 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2559 + difference 5 1) (sourceB2559 + difference 1 5) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2559 + difference 5 1) (sourceB2559 + difference 1 5) sourceC2559) = raw35360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35360; decide +kernel
    rw [ha]
    exact (canonical35360 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2559 + difference 5 2) (sourceB2559 + difference 2 5) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4906) := by
    have ha : (tripleCharges (sourceA2559 + difference 5 2) (sourceB2559 + difference 2 5) sourceC2559) = raw35361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35361; decide +kernel
    rw [ha]
    exact (canonical35361 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2559 + difference 5 3) (sourceB2559 + difference 3 5) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4923) := by
    have ha : (tripleCharges (sourceA2559 + difference 5 3) (sourceB2559 + difference 3 5) sourceC2559) = raw35362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw35362; decide +kernel
    rw [ha]
    exact (canonical35362 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2559 + difference 5 4) (sourceB2559 + difference 4 5) sourceC2559) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2559 + difference 5 4) (sourceB2559 + difference 4 5) sourceC2559) = raw17099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2559 sourceB2559 sourceC2559 difference raw17099; decide +kernel
    rw [ha]
    exact (canonical17099 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2559 sourceB2559 sourceC2559
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2559, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
