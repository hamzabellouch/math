import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical223
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical227

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2048 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB2048 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC2048 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2048 : Integer.Sparse Master := [(Sum.inr 4395, 1), (Sum.inr 4398, 1), (Sum.inr 4403, 1), (Sum.inr 4418, 1), (Sum.inr 4450, 1), (Sum.inr 4728, 1), (Sum.inr 4738, 1), (Sum.inr 4741, 1), (Sum.inr 4744, 1), (Sum.inr 4778, 1), (Sum.inr 4779, 1), (Sum.inr 4781, 1), (Sum.inr 4791, 1), (Sum.inr 4792, 1), (Sum.inr 4797, 1), (Sum.inr 4800, 1), (Sum.inr 4804, 1), (Sum.inr 4807, 1), (Sum.inr 4814, 1), (Sum.inr 4817, 1), (Sum.inr 4837, 1), (Sum.inr 4841, 1), (Sum.inr 4850, 1), (Sum.inr 4853, 1), (Sum.inr 4868, 1), (Sum.inr 5075, 1), (Sum.inr 5078, 1), (Sum.inr 5127, 1), (Sum.inr 5147, 1), (Sum.inr 5171, 1)]

theorem sourceEq2048 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2048 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2048 + difference 0 1) (sourceB2048 + difference 1 0) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2048 + difference 0 1) (sourceB2048 + difference 1 0) sourceC2048) = raw28925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28925; decide +kernel
    rw [ha]
    exact (canonical28925 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2048 + difference 0 2) (sourceB2048 + difference 2 0) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA2048 + difference 0 2) (sourceB2048 + difference 2 0) sourceC2048) = raw28926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28926; decide +kernel
    rw [ha]
    exact (canonical28926 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2048 + difference 0 3) (sourceB2048 + difference 3 0) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA2048 + difference 0 3) (sourceB2048 + difference 3 0) sourceC2048) = raw28927 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28927; decide +kernel
    rw [ha]
    exact (canonical28927 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2048 + difference 0 4) (sourceB2048 + difference 4 0) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA2048 + difference 0 4) (sourceB2048 + difference 4 0) sourceC2048) = raw28661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28661; decide +kernel
    rw [ha]
    exact (canonical28661 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2048 + difference 0 5) (sourceB2048 + difference 5 0) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2048 + difference 0 5) (sourceB2048 + difference 5 0) sourceC2048) = raw28801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28801; decide +kernel
    rw [ha]
    exact (canonical28801 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2048 + difference 1 0) (sourceB2048 + difference 0 1) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2048 + difference 1 0) (sourceB2048 + difference 0 1) sourceC2048) = raw28928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28928; decide +kernel
    rw [ha]
    exact (canonical28928 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2048 + difference 1 2) (sourceB2048 + difference 2 1) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4791) := by
    have ha : (tripleCharges (sourceA2048 + difference 1 2) (sourceB2048 + difference 2 1) sourceC2048) = raw28929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28929; decide +kernel
    rw [ha]
    exact (canonical28929 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2048 + difference 1 3) (sourceB2048 + difference 3 1) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4814) := by
    have ha : (tripleCharges (sourceA2048 + difference 1 3) (sourceB2048 + difference 3 1) sourceC2048) = raw28930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28930; decide +kernel
    rw [ha]
    exact (canonical28930 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2048 + difference 1 4) (sourceB2048 + difference 4 1) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4850) := by
    have ha : (tripleCharges (sourceA2048 + difference 1 4) (sourceB2048 + difference 4 1) sourceC2048) = raw28666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28666; decide +kernel
    rw [ha]
    exact (canonical28666 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2048 + difference 1 5) (sourceB2048 + difference 5 1) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2048 + difference 1 5) (sourceB2048 + difference 5 1) sourceC2048) = raw28805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28805; decide +kernel
    rw [ha]
    exact (canonical28805 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2048 + difference 2 0) (sourceB2048 + difference 0 2) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4778) := by
    have ha : (tripleCharges (sourceA2048 + difference 2 0) (sourceB2048 + difference 0 2) sourceC2048) = raw28931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28931; decide +kernel
    rw [ha]
    exact (canonical28931 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2048 + difference 2 1) (sourceB2048 + difference 1 2) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2048 + difference 2 1) (sourceB2048 + difference 1 2) sourceC2048) = raw28932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28932; decide +kernel
    rw [ha]
    exact (canonical28932 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2048 + difference 2 3) (sourceB2048 + difference 3 2) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4781) := by
    have ha : (tripleCharges (sourceA2048 + difference 2 3) (sourceB2048 + difference 3 2) sourceC2048) = raw28933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28933; decide +kernel
    rw [ha]
    exact (canonical28933 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2048 + difference 2 4) (sourceB2048 + difference 4 2) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4797) := by
    have ha : (tripleCharges (sourceA2048 + difference 2 4) (sourceB2048 + difference 4 2) sourceC2048) = raw28671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28671; decide +kernel
    rw [ha]
    exact (canonical28671 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2048 + difference 2 5) (sourceB2048 + difference 5 2) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA2048 + difference 2 5) (sourceB2048 + difference 5 2) sourceC2048) = raw28809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28809; decide +kernel
    rw [ha]
    exact (canonical28809 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2048 + difference 3 0) (sourceB2048 + difference 0 3) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2048 + difference 3 0) (sourceB2048 + difference 0 3) sourceC2048) = raw28678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28678; decide +kernel
    rw [ha]
    exact (canonical28678 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2048 + difference 3 1) (sourceB2048 + difference 1 3) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2048 + difference 3 1) (sourceB2048 + difference 1 3) sourceC2048) = raw28679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28679; decide +kernel
    rw [ha]
    exact (canonical28679 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2048 + difference 3 2) (sourceB2048 + difference 2 3) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2048 + difference 3 2) (sourceB2048 + difference 2 3) sourceC2048) = raw28680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28680; decide +kernel
    rw [ha]
    exact (canonical28680 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2048 + difference 3 4) (sourceB2048 + difference 4 3) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2048 + difference 3 4) (sourceB2048 + difference 4 3) sourceC2048) = raw28934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28934; decide +kernel
    rw [ha]
    exact (canonical28934 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2048 + difference 3 5) (sourceB2048 + difference 5 3) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2048 + difference 3 5) (sourceB2048 + difference 5 3) sourceC2048) = raw27667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw27667; decide +kernel
    rw [ha]
    exact (canonical27667 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2048 + difference 4 0) (sourceB2048 + difference 0 4) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4738) := by
    have ha : (tripleCharges (sourceA2048 + difference 4 0) (sourceB2048 + difference 0 4) sourceC2048) = raw28814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28814; decide +kernel
    rw [ha]
    exact (canonical28814 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2048 + difference 4 1) (sourceB2048 + difference 1 4) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2048 + difference 4 1) (sourceB2048 + difference 1 4) sourceC2048) = raw28815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28815; decide +kernel
    rw [ha]
    exact (canonical28815 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2048 + difference 4 2) (sourceB2048 + difference 2 4) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2048 + difference 4 2) (sourceB2048 + difference 2 4) sourceC2048) = raw28816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28816; decide +kernel
    rw [ha]
    exact (canonical28816 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2048 + difference 4 3) (sourceB2048 + difference 3 4) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2048 + difference 4 3) (sourceB2048 + difference 3 4) sourceC2048) = raw28817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28817; decide +kernel
    rw [ha]
    exact (canonical28817 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2048 + difference 4 5) (sourceB2048 + difference 5 4) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2048 + difference 4 5) (sourceB2048 + difference 5 4) sourceC2048) = raw27666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw27666; decide +kernel
    rw [ha]
    exact (canonical27666 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2048 + difference 5 0) (sourceB2048 + difference 0 5) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA2048 + difference 5 0) (sourceB2048 + difference 0 5) sourceC2048) = raw28935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28935; decide +kernel
    rw [ha]
    exact (canonical28935 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2048 + difference 5 1) (sourceB2048 + difference 1 5) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA2048 + difference 5 1) (sourceB2048 + difference 1 5) sourceC2048) = raw28936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28936; decide +kernel
    rw [ha]
    exact (canonical28936 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2048 + difference 5 2) (sourceB2048 + difference 2 5) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4395) := by
    have ha : (tripleCharges (sourceA2048 + difference 5 2) (sourceB2048 + difference 2 5) sourceC2048) = raw28937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28937; decide +kernel
    rw [ha]
    exact (canonical28937 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2048 + difference 5 3) (sourceB2048 + difference 3 5) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA2048 + difference 5 3) (sourceB2048 + difference 3 5) sourceC2048) = raw28938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28938; decide +kernel
    rw [ha]
    exact (canonical28938 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2048 + difference 5 4) (sourceB2048 + difference 4 5) sourceC2048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA2048 + difference 5 4) (sourceB2048 + difference 4 5) sourceC2048) = raw28685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2048 sourceB2048 sourceC2048 difference raw28685; decide +kernel
    rw [ha]
    exact (canonical28685 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2048 sourceB2048 sourceC2048
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2048, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2049 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB2049 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC2049 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2049 : Integer.Sparse Master := [(Sum.inr 1398, 1), (Sum.inr 1399, 1), (Sum.inr 1400, 1), (Sum.inr 1415, 1), (Sum.inr 1427, 1), (Sum.inr 2471, 1), (Sum.inr 2485, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2574, 1), (Sum.inr 2858, 1), (Sum.inr 2865, 1), (Sum.inr 2866, 1), (Sum.inr 2872, 1), (Sum.inr 2914, 1), (Sum.inr 2915, 1), (Sum.inr 2919, 1), (Sum.inr 2932, 1), (Sum.inr 2939, 1), (Sum.inr 2941, 1), (Sum.inr 2948, 1), (Sum.inr 2965, 1), (Sum.inr 2966, 1), (Sum.inr 2982, 1), (Sum.inr 2993, 1), (Sum.inr 3004, 1), (Sum.inr 3177, 1), (Sum.inr 3200, 1), (Sum.inr 3208, 1), (Sum.inr 3215, 1)]

theorem sourceEq2049 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2049 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2049 + difference 0 1) (sourceB2049 + difference 1 0) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA2049 + difference 0 1) (sourceB2049 + difference 1 0) sourceC2049) = raw28939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28939; decide +kernel
    rw [ha]
    exact (canonical28939 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2049 + difference 0 2) (sourceB2049 + difference 2 0) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA2049 + difference 0 2) (sourceB2049 + difference 2 0) sourceC2049) = raw28940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28940; decide +kernel
    rw [ha]
    exact (canonical28940 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2049 + difference 0 3) (sourceB2049 + difference 3 0) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA2049 + difference 0 3) (sourceB2049 + difference 3 0) sourceC2049) = raw28941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28941; decide +kernel
    rw [ha]
    exact (canonical28941 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2049 + difference 0 4) (sourceB2049 + difference 4 0) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA2049 + difference 0 4) (sourceB2049 + difference 4 0) sourceC2049) = raw28689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28689; decide +kernel
    rw [ha]
    exact (canonical28689 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2049 + difference 0 5) (sourceB2049 + difference 5 0) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA2049 + difference 0 5) (sourceB2049 + difference 5 0) sourceC2049) = raw28942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28942; decide +kernel
    rw [ha]
    exact (canonical28942 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2049 + difference 1 0) (sourceB2049 + difference 0 1) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3177) := by
    have ha : (tripleCharges (sourceA2049 + difference 1 0) (sourceB2049 + difference 0 1) sourceC2049) = raw28943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28943; decide +kernel
    rw [ha]
    exact (canonical28943 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2049 + difference 1 2) (sourceB2049 + difference 2 1) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2858) := by
    have ha : (tripleCharges (sourceA2049 + difference 1 2) (sourceB2049 + difference 2 1) sourceC2049) = raw28944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28944; decide +kernel
    rw [ha]
    exact (canonical28944 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2049 + difference 1 3) (sourceB2049 + difference 3 1) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2872) := by
    have ha : (tripleCharges (sourceA2049 + difference 1 3) (sourceB2049 + difference 3 1) sourceC2049) = raw28945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28945; decide +kernel
    rw [ha]
    exact (canonical28945 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2049 + difference 1 4) (sourceB2049 + difference 4 1) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2866) := by
    have ha : (tripleCharges (sourceA2049 + difference 1 4) (sourceB2049 + difference 4 1) sourceC2049) = raw28694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28694; decide +kernel
    rw [ha]
    exact (canonical28694 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2049 + difference 1 5) (sourceB2049 + difference 5 1) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA2049 + difference 1 5) (sourceB2049 + difference 5 1) sourceC2049) = raw28946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28946; decide +kernel
    rw [ha]
    exact (canonical28946 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2049 + difference 2 0) (sourceB2049 + difference 0 2) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3200) := by
    have ha : (tripleCharges (sourceA2049 + difference 2 0) (sourceB2049 + difference 0 2) sourceC2049) = raw28947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28947; decide +kernel
    rw [ha]
    exact (canonical28947 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2049 + difference 2 1) (sourceB2049 + difference 1 2) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2982) := by
    have ha : (tripleCharges (sourceA2049 + difference 2 1) (sourceB2049 + difference 1 2) sourceC2049) = raw28948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28948; decide +kernel
    rw [ha]
    exact (canonical28948 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2049 + difference 2 3) (sourceB2049 + difference 3 2) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2919) := by
    have ha : (tripleCharges (sourceA2049 + difference 2 3) (sourceB2049 + difference 3 2) sourceC2049) = raw28949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28949; decide +kernel
    rw [ha]
    exact (canonical28949 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2049 + difference 2 4) (sourceB2049 + difference 4 2) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2915) := by
    have ha : (tripleCharges (sourceA2049 + difference 2 4) (sourceB2049 + difference 4 2) sourceC2049) = raw28699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28699; decide +kernel
    rw [ha]
    exact (canonical28699 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2049 + difference 2 5) (sourceB2049 + difference 5 2) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2914) := by
    have ha : (tripleCharges (sourceA2049 + difference 2 5) (sourceB2049 + difference 5 2) sourceC2049) = raw28950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28950; decide +kernel
    rw [ha]
    exact (canonical28950 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2049 + difference 3 0) (sourceB2049 + difference 0 3) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3215) := by
    have ha : (tripleCharges (sourceA2049 + difference 3 0) (sourceB2049 + difference 0 3) sourceC2049) = raw28706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28706; decide +kernel
    rw [ha]
    exact (canonical28706 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2049 + difference 3 1) (sourceB2049 + difference 1 3) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3004) := by
    have ha : (tripleCharges (sourceA2049 + difference 3 1) (sourceB2049 + difference 1 3) sourceC2049) = raw28707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28707; decide +kernel
    rw [ha]
    exact (canonical28707 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2049 + difference 3 2) (sourceB2049 + difference 2 3) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2049 + difference 3 2) (sourceB2049 + difference 2 3) sourceC2049) = raw28708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28708; decide +kernel
    rw [ha]
    exact (canonical28708 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2049 + difference 3 4) (sourceB2049 + difference 4 3) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA2049 + difference 3 4) (sourceB2049 + difference 4 3) sourceC2049) = raw28951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28951; decide +kernel
    rw [ha]
    exact (canonical28951 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2049 + difference 3 5) (sourceB2049 + difference 5 3) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA2049 + difference 3 5) (sourceB2049 + difference 5 3) sourceC2049) = raw27998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw27998; decide +kernel
    rw [ha]
    exact (canonical27998 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2049 + difference 4 0) (sourceB2049 + difference 0 4) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3208) := by
    have ha : (tripleCharges (sourceA2049 + difference 4 0) (sourceB2049 + difference 0 4) sourceC2049) = raw28952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28952; decide +kernel
    rw [ha]
    exact (canonical28952 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2049 + difference 4 1) (sourceB2049 + difference 1 4) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2993) := by
    have ha : (tripleCharges (sourceA2049 + difference 4 1) (sourceB2049 + difference 1 4) sourceC2049) = raw28953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28953; decide +kernel
    rw [ha]
    exact (canonical28953 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2049 + difference 4 2) (sourceB2049 + difference 2 4) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2932) := by
    have ha : (tripleCharges (sourceA2049 + difference 4 2) (sourceB2049 + difference 2 4) sourceC2049) = raw28954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28954; decide +kernel
    rw [ha]
    exact (canonical28954 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2049 + difference 4 3) (sourceB2049 + difference 3 4) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2948) := by
    have ha : (tripleCharges (sourceA2049 + difference 4 3) (sourceB2049 + difference 3 4) sourceC2049) = raw28955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28955; decide +kernel
    rw [ha]
    exact (canonical28955 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2049 + difference 4 5) (sourceB2049 + difference 5 4) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA2049 + difference 4 5) (sourceB2049 + difference 5 4) sourceC2049) = raw28956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28956; decide +kernel
    rw [ha]
    exact (canonical28956 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2049 + difference 5 0) (sourceB2049 + difference 0 5) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1399) := by
    have ha : (tripleCharges (sourceA2049 + difference 5 0) (sourceB2049 + difference 0 5) sourceC2049) = raw28957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28957; decide +kernel
    rw [ha]
    exact (canonical28957 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2049 + difference 5 1) (sourceB2049 + difference 1 5) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1427) := by
    have ha : (tripleCharges (sourceA2049 + difference 5 1) (sourceB2049 + difference 1 5) sourceC2049) = raw28958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28958; decide +kernel
    rw [ha]
    exact (canonical28958 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2049 + difference 5 2) (sourceB2049 + difference 2 5) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1398) := by
    have ha : (tripleCharges (sourceA2049 + difference 5 2) (sourceB2049 + difference 2 5) sourceC2049) = raw28959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28959; decide +kernel
    rw [ha]
    exact (canonical28959 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2049 + difference 5 3) (sourceB2049 + difference 3 5) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA2049 + difference 5 3) (sourceB2049 + difference 3 5) sourceC2049) = raw28960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28960; decide +kernel
    rw [ha]
    exact (canonical28960 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2049 + difference 5 4) (sourceB2049 + difference 4 5) sourceC2049) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA2049 + difference 5 4) (sourceB2049 + difference 4 5) sourceC2049) = raw28713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2049 sourceB2049 sourceC2049 difference raw28713; decide +kernel
    rw [ha]
    exact (canonical28713 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2049 sourceB2049 sourceC2049
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2049, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2050 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2050 : Charge := ![1, 1, 0, -2, 1, -1]
def sourceC2050 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceForm2050 : Integer.Sparse Master := [(Sum.inr 2389, 1), (Sum.inr 2391, 1), (Sum.inr 2394, 1), (Sum.inr 2400, 1), (Sum.inr 2677, 1), (Sum.inr 3770, 1), (Sum.inr 4089, -1)]

theorem sourceEq2050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2050 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2050 + difference 0 0) (sourceB2050 + difference 0 0) sourceC2050) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA2050 + difference 0 0) (sourceB2050 + difference 0 0) sourceC2050) = raw21003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2050 sourceB2050 sourceC2050 difference raw21003; decide +kernel
    rw [ha]
    exact (canonical21003 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2050 + difference 0 1) (sourceB2050 + difference 1 0) sourceC2050) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2394) := by
    have ha : (tripleCharges (sourceA2050 + difference 0 1) (sourceB2050 + difference 1 0) sourceC2050) = raw28961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2050 sourceB2050 sourceC2050 difference raw28961; decide +kernel
    rw [ha]
    exact (canonical28961 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2050 + difference 0 2) (sourceB2050 + difference 2 0) sourceC2050) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2389) := by
    have ha : (tripleCharges (sourceA2050 + difference 0 2) (sourceB2050 + difference 2 0) sourceC2050) = raw28962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2050 sourceB2050 sourceC2050 difference raw28962; decide +kernel
    rw [ha]
    exact (canonical28962 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2050 + difference 0 3) (sourceB2050 + difference 3 0) sourceC2050) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2400) := by
    have ha : (tripleCharges (sourceA2050 + difference 0 3) (sourceB2050 + difference 3 0) sourceC2050) = raw28963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2050 sourceB2050 sourceC2050 difference raw28963; decide +kernel
    rw [ha]
    exact (canonical28963 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2050 + difference 0 4) (sourceB2050 + difference 4 0) sourceC2050) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA2050 + difference 0 4) (sourceB2050 + difference 4 0) sourceC2050) = raw28964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2050 sourceB2050 sourceC2050 difference raw28964; decide +kernel
    rw [ha]
    exact (canonical28964 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2050 + difference 0 5) (sourceB2050 + difference 5 0) sourceC2050) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2050 + difference 0 5) (sourceB2050 + difference 5 0) sourceC2050) = raw28965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2050 sourceB2050 sourceC2050 difference raw28965; decide +kernel
    rw [ha]
    exact (canonical28965 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2050 + sourceB2050) sourceC2050) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2050 + sourceB2050) sourceC2050) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA2050 sourceB2050 sourceC2050 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2050 sourceB2050 sourceC2050
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2050, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2051 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2051 : Charge := ![1, 1, 0, -2, 1, -1]
def sourceC2051 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceForm2051 : Integer.Sparse Master := [(Sum.inr 2391, 1), (Sum.inr 2535, 1), (Sum.inr 2539, 1), (Sum.inr 2585, 1), (Sum.inr 2686, 1), (Sum.inr 3770, 1), (Sum.inr 4089, -1)]

theorem sourceEq2051 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2051 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2051 + difference 0 5) (sourceB2051 + difference 5 0) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2051 + difference 0 5) (sourceB2051 + difference 5 0) sourceC2051) = raw28965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw28965; decide +kernel
    rw [ha]
    exact (canonical28965 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2051 + difference 1 5) (sourceB2051 + difference 5 1) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2051 + difference 1 5) (sourceB2051 + difference 5 1) sourceC2051) = raw21007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw21007; decide +kernel
    rw [ha]
    exact (canonical21007 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2051 + difference 2 5) (sourceB2051 + difference 5 2) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2535) := by
    have ha : (tripleCharges (sourceA2051 + difference 2 5) (sourceB2051 + difference 5 2) sourceC2051) = raw28966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw28966; decide +kernel
    rw [ha]
    exact (canonical28966 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2051 + difference 3 5) (sourceB2051 + difference 5 3) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2585) := by
    have ha : (tripleCharges (sourceA2051 + difference 3 5) (sourceB2051 + difference 5 3) sourceC2051) = raw28967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw28967; decide +kernel
    rw [ha]
    exact (canonical28967 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2051 + difference 4 5) (sourceB2051 + difference 5 4) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2539) := by
    have ha : (tripleCharges (sourceA2051 + difference 4 5) (sourceB2051 + difference 5 4) sourceC2051) = raw22850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw22850; decide +kernel
    rw [ha]
    exact (canonical22850 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2051 + difference 5 5) (sourceB2051 + difference 5 5) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA2051 + difference 5 5) (sourceB2051 + difference 5 5) sourceC2051) = raw21003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw21003; decide +kernel
    rw [ha]
    exact (canonical21003 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2051 + sourceB2051) sourceC2051) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2051 + sourceB2051) sourceC2051) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA2051 sourceB2051 sourceC2051 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2051 sourceB2051 sourceC2051
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2051, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2052 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2052 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2052 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceForm2052 : Integer.Sparse Master := [(Sum.inr 1921, 1), (Sum.inr 1924, 1), (Sum.inr 1928, 1), (Sum.inr 1945, 1), (Sum.inr 2215, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

theorem sourceEq2052 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2052 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 0) (sourceB2052 + difference 0 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 0) (sourceB2052 + difference 0 0) sourceC2052) = raw21014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw21014; decide +kernel
    rw [ha]
    exact (canonical21014 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 1) (sourceB2052 + difference 1 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 1) (sourceB2052 + difference 1 0) sourceC2052) = raw28968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28968; decide +kernel
    rw [ha]
    exact (canonical28968 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 2) (sourceB2052 + difference 2 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1921) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 2) (sourceB2052 + difference 2 0) sourceC2052) = raw28969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28969; decide +kernel
    rw [ha]
    exact (canonical28969 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 3) (sourceB2052 + difference 3 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 3) (sourceB2052 + difference 3 0) sourceC2052) = raw28970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28970; decide +kernel
    rw [ha]
    exact (canonical28970 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 4) (sourceB2052 + difference 4 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 4) (sourceB2052 + difference 4 0) sourceC2052) = raw28971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28971; decide +kernel
    rw [ha]
    exact (canonical28971 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 5) (sourceB2052 + difference 5 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 5) (sourceB2052 + difference 5 0) sourceC2052) = raw28972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28972; decide +kernel
    rw [ha]
    exact (canonical28972 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2052 + sourceB2052) sourceC2052) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2052 + sourceB2052) sourceC2052) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA2052 sourceB2052 sourceC2052 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2052 sourceB2052 sourceC2052
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2052, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2053 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2053 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2053 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceForm2053 : Integer.Sparse Master := [(Sum.inr 881, 1), (Sum.inr 1773, 1), (Sum.inr 1863, 1), (Sum.inr 1924, 1), (Sum.inr 1945, 1), (Sum.inr 1950, 1), (Sum.inr 4082, -1)]

theorem sourceEq2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2053 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2053 + difference 0 3) (sourceB2053 + difference 3 0) sourceC2053) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA2053 + difference 0 3) (sourceB2053 + difference 3 0) sourceC2053) = raw28970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2053 sourceB2053 sourceC2053 difference raw28970; decide +kernel
    rw [ha]
    exact (canonical28970 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2053 + difference 1 3) (sourceB2053 + difference 3 1) sourceC2053) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1950) := by
    have ha : (tripleCharges (sourceA2053 + difference 1 3) (sourceB2053 + difference 3 1) sourceC2053) = raw21016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2053 sourceB2053 sourceC2053 difference raw21016; decide +kernel
    rw [ha]
    exact (canonical21016 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2053 + difference 2 3) (sourceB2053 + difference 3 2) sourceC2053) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1863) := by
    have ha : (tripleCharges (sourceA2053 + difference 2 3) (sourceB2053 + difference 3 2) sourceC2053) = raw28973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2053 sourceB2053 sourceC2053 difference raw28973; decide +kernel
    rw [ha]
    exact (canonical28973 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2053 + difference 3 3) (sourceB2053 + difference 3 3) sourceC2053) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA2053 + difference 3 3) (sourceB2053 + difference 3 3) sourceC2053) = raw21014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2053 sourceB2053 sourceC2053 difference raw21014; decide +kernel
    rw [ha]
    exact (canonical21014 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2053 + difference 4 3) (sourceB2053 + difference 3 4) sourceC2053) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1773) := by
    have ha : (tripleCharges (sourceA2053 + difference 4 3) (sourceB2053 + difference 3 4) sourceC2053) = raw28974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2053 sourceB2053 sourceC2053 difference raw28974; decide +kernel
    rw [ha]
    exact (canonical28974 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2053 + difference 5 3) (sourceB2053 + difference 3 5) sourceC2053) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA2053 + difference 5 3) (sourceB2053 + difference 3 5) sourceC2053) = raw28975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2053 sourceB2053 sourceC2053 difference raw28975; decide +kernel
    rw [ha]
    exact (canonical28975 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2053 + sourceB2053) sourceC2053) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2053 + sourceB2053) sourceC2053) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA2053 sourceB2053 sourceC2053 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2053 sourceB2053 sourceC2053
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2053, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2054 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2054 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2054 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceForm2054 : Integer.Sparse Master := [(Sum.inr 1924, 1), (Sum.inr 2534, 1), (Sum.inr 2538, 1), (Sum.inr 2584, 1), (Sum.inr 2685, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

theorem sourceEq2054 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2054 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2054 + difference 0 5) (sourceB2054 + difference 5 0) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2054 + difference 0 5) (sourceB2054 + difference 5 0) sourceC2054) = raw28972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw28972; decide +kernel
    rw [ha]
    exact (canonical28972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2054 + difference 1 5) (sourceB2054 + difference 5 1) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2054 + difference 1 5) (sourceB2054 + difference 5 1) sourceC2054) = raw21018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw21018; decide +kernel
    rw [ha]
    exact (canonical21018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2054 + difference 2 5) (sourceB2054 + difference 5 2) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2534) := by
    have ha : (tripleCharges (sourceA2054 + difference 2 5) (sourceB2054 + difference 5 2) sourceC2054) = raw28976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw28976; decide +kernel
    rw [ha]
    exact (canonical28976 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2054 + difference 3 5) (sourceB2054 + difference 5 3) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA2054 + difference 3 5) (sourceB2054 + difference 5 3) sourceC2054) = raw28977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw28977; decide +kernel
    rw [ha]
    exact (canonical28977 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2054 + difference 4 5) (sourceB2054 + difference 5 4) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA2054 + difference 4 5) (sourceB2054 + difference 5 4) sourceC2054) = raw28978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw28978; decide +kernel
    rw [ha]
    exact (canonical28978 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2054 + difference 5 5) (sourceB2054 + difference 5 5) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA2054 + difference 5 5) (sourceB2054 + difference 5 5) sourceC2054) = raw21014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw21014; decide +kernel
    rw [ha]
    exact (canonical21014 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2054 + sourceB2054) sourceC2054) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2054 + sourceB2054) sourceC2054) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA2054 sourceB2054 sourceC2054 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2054 sourceB2054 sourceC2054
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2054, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2055 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceB2055 : Charge := ![2, 0, 0, 2, -1, -3]
def sourceC2055 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2055 : Integer.Sparse Master := [(Sum.inr 872, 1), (Sum.inr 1765, 1), (Sum.inr 1784, 1), (Sum.inr 1799, 1), (Sum.inr 1911, 1), (Sum.inr 1917, 1), (Sum.inr 4081, -1)]

theorem sourceEq2055 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2055 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2055 + difference 0 0) (sourceB2055 + difference 0 0) sourceC2055) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA2055 + difference 0 0) (sourceB2055 + difference 0 0) sourceC2055) = raw28979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2055 sourceB2055 sourceC2055 difference raw28979; decide +kernel
    rw [ha]
    exact (canonical28979 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2055 + difference 1 0) (sourceB2055 + difference 0 1) sourceC2055) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1799) := by
    have ha : (tripleCharges (sourceA2055 + difference 1 0) (sourceB2055 + difference 0 1) sourceC2055) = raw28980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2055 sourceB2055 sourceC2055 difference raw28980; decide +kernel
    rw [ha]
    exact (canonical28980 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2055 + difference 2 0) (sourceB2055 + difference 0 2) sourceC2055) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1784) := by
    have ha : (tripleCharges (sourceA2055 + difference 2 0) (sourceB2055 + difference 0 2) sourceC2055) = raw28981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2055 sourceB2055 sourceC2055 difference raw28981; decide +kernel
    rw [ha]
    exact (canonical28981 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2055 + difference 3 0) (sourceB2055 + difference 0 3) sourceC2055) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA2055 + difference 3 0) (sourceB2055 + difference 0 3) sourceC2055) = raw28982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2055 sourceB2055 sourceC2055 difference raw28982; decide +kernel
    rw [ha]
    exact (canonical28982 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2055 + difference 4 0) (sourceB2055 + difference 0 4) sourceC2055) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1765) := by
    have ha : (tripleCharges (sourceA2055 + difference 4 0) (sourceB2055 + difference 0 4) sourceC2055) = raw28983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2055 sourceB2055 sourceC2055 difference raw28983; decide +kernel
    rw [ha]
    exact (canonical28983 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2055 + difference 5 0) (sourceB2055 + difference 0 5) sourceC2055) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 872) := by
    have ha : (tripleCharges (sourceA2055 + difference 5 0) (sourceB2055 + difference 0 5) sourceC2055) = raw28984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2055 sourceB2055 sourceC2055 difference raw28984; decide +kernel
    rw [ha]
    exact (canonical28984 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2055 + sourceB2055) sourceC2055) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA2055 + sourceB2055) sourceC2055) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2055 sourceB2055 sourceC2055 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2055 sourceB2055 sourceC2055
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2055, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2056 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2056 : Charge := ![1, 1, -1, -1, 1, -1]
def sourceC2056 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceForm2056 : Integer.Sparse Master := [(Sum.inr 2377, 1), (Sum.inr 2379, 1), (Sum.inr 2382, 2), (Sum.inr 2661, 1), (Sum.inr 3757, 1), (Sum.inr 4088, -1)]

theorem sourceEq2056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2056 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 0) (sourceB2056 + difference 0 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2377) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 0) (sourceB2056 + difference 0 0) sourceC2056) = raw21041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw21041; decide +kernel
    rw [ha]
    exact (canonical21041 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 1) (sourceB2056 + difference 1 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2379) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 1) (sourceB2056 + difference 1 0) sourceC2056) = raw28985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28985; decide +kernel
    rw [ha]
    exact (canonical28985 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 2) (sourceB2056 + difference 2 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 2) (sourceB2056 + difference 2 0) sourceC2056) = raw28986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28986; decide +kernel
    rw [ha]
    exact (canonical28986 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 3) (sourceB2056 + difference 3 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 3) (sourceB2056 + difference 3 0) sourceC2056) = raw28987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28987; decide +kernel
    rw [ha]
    exact (canonical28987 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 4) (sourceB2056 + difference 4 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 4) (sourceB2056 + difference 4 0) sourceC2056) = raw28988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28988; decide +kernel
    rw [ha]
    exact (canonical28988 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 5) (sourceB2056 + difference 5 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 5) (sourceB2056 + difference 5 0) sourceC2056) = raw28989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28989; decide +kernel
    rw [ha]
    exact (canonical28989 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2056 + sourceB2056) sourceC2056) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2056 + sourceB2056) sourceC2056) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA2056 sourceB2056 sourceC2056 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2056 sourceB2056 sourceC2056
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2056, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2057 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2057 : Charge := ![1, 1, -1, -1, 1, -1]
def sourceC2057 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceForm2057 : Integer.Sparse Master := [(Sum.inr 2377, 1), (Sum.inr 2541, 1), (Sum.inr 2551, 2), (Sum.inr 2705, 1), (Sum.inr 3757, 1), (Sum.inr 4088, -1)]

theorem sourceEq2057 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2057 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2057 + difference 0 5) (sourceB2057 + difference 5 0) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2057 + difference 0 5) (sourceB2057 + difference 5 0) sourceC2057) = raw28989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw28989; decide +kernel
    rw [ha]
    exact (canonical28989 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2057 + difference 1 5) (sourceB2057 + difference 5 1) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2057 + difference 1 5) (sourceB2057 + difference 5 1) sourceC2057) = raw21045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw21045; decide +kernel
    rw [ha]
    exact (canonical21045 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2057 + difference 2 5) (sourceB2057 + difference 5 2) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2551) := by
    have ha : (tripleCharges (sourceA2057 + difference 2 5) (sourceB2057 + difference 5 2) sourceC2057) = raw28990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw28990; decide +kernel
    rw [ha]
    exact (canonical28990 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2057 + difference 3 5) (sourceB2057 + difference 5 3) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2551) := by
    have ha : (tripleCharges (sourceA2057 + difference 3 5) (sourceB2057 + difference 5 3) sourceC2057) = raw28991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw28991; decide +kernel
    rw [ha]
    exact (canonical28991 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2057 + difference 4 5) (sourceB2057 + difference 5 4) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2541) := by
    have ha : (tripleCharges (sourceA2057 + difference 4 5) (sourceB2057 + difference 5 4) sourceC2057) = raw22871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw22871; decide +kernel
    rw [ha]
    exact (canonical22871 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2057 + difference 5 5) (sourceB2057 + difference 5 5) sourceC2057) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2377) := by
    have ha : (tripleCharges (sourceA2057 + difference 5 5) (sourceB2057 + difference 5 5) sourceC2057) = raw21041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2057 sourceB2057 sourceC2057 difference raw21041; decide +kernel
    rw [ha]
    exact (canonical21041 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2057 + sourceB2057) sourceC2057) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2057 + sourceB2057) sourceC2057) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA2057 sourceB2057 sourceC2057 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2057 sourceB2057 sourceC2057
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2057, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2058 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2058 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2058 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceForm2058 : Integer.Sparse Master := [(Sum.inr 865, 1), (Sum.inr 1760, 1), (Sum.inr 1875, 1), (Sum.inr 1897, 1), (Sum.inr 1908, 1), (Sum.inr 1914, 1), (Sum.inr 4080, -1)]

theorem sourceEq2058 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2058 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2058 + difference 0 2) (sourceB2058 + difference 2 0) sourceC2058) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1908) := by
    have ha : (tripleCharges (sourceA2058 + difference 0 2) (sourceB2058 + difference 2 0) sourceC2058) = raw28992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2058 sourceB2058 sourceC2058 difference raw28992; decide +kernel
    rw [ha]
    exact (canonical28992 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2058 + difference 1 2) (sourceB2058 + difference 2 1) sourceC2058) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA2058 + difference 1 2) (sourceB2058 + difference 2 1) sourceC2058) = raw21053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2058 sourceB2058 sourceC2058 difference raw21053; decide +kernel
    rw [ha]
    exact (canonical21053 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2058 + difference 2 2) (sourceB2058 + difference 2 2) sourceC2058) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA2058 + difference 2 2) (sourceB2058 + difference 2 2) sourceC2058) = raw21052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2058 sourceB2058 sourceC2058 difference raw21052; decide +kernel
    rw [ha]
    exact (canonical21052 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2058 + difference 3 2) (sourceB2058 + difference 2 3) sourceC2058) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1875) := by
    have ha : (tripleCharges (sourceA2058 + difference 3 2) (sourceB2058 + difference 2 3) sourceC2058) = raw28993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2058 sourceB2058 sourceC2058 difference raw28993; decide +kernel
    rw [ha]
    exact (canonical28993 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2058 + difference 4 2) (sourceB2058 + difference 2 4) sourceC2058) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1760) := by
    have ha : (tripleCharges (sourceA2058 + difference 4 2) (sourceB2058 + difference 2 4) sourceC2058) = raw28994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2058 sourceB2058 sourceC2058 difference raw28994; decide +kernel
    rw [ha]
    exact (canonical28994 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2058 + difference 5 2) (sourceB2058 + difference 2 5) sourceC2058) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 865) := by
    have ha : (tripleCharges (sourceA2058 + difference 5 2) (sourceB2058 + difference 2 5) sourceC2058) = raw28995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2058 sourceB2058 sourceC2058 difference raw28995; decide +kernel
    rw [ha]
    exact (canonical28995 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2058 + sourceB2058) sourceC2058) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2058 + sourceB2058) sourceC2058) = raw21057 := by
      apply Matrix.ext; unfold doubleCharges sourceA2058 sourceB2058 sourceC2058 raw21057; decide +kernel
    rw [ha]
    exact (canonical21057 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2058 sourceB2058 sourceC2058
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2058, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2059 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2059 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2059 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceForm2059 : Integer.Sparse Master := [(Sum.inr 1897, 1), (Sum.inr 2540, 1), (Sum.inr 2550, 2), (Sum.inr 2704, 1), (Sum.inr 3459, 1), (Sum.inr 4080, -1)]

theorem sourceEq2059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2059 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2059 + difference 0 5) (sourceB2059 + difference 5 0) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA2059 + difference 0 5) (sourceB2059 + difference 5 0) sourceC2059) = raw28996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw28996; decide +kernel
    rw [ha]
    exact (canonical28996 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2059 + difference 1 5) (sourceB2059 + difference 5 1) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2059 + difference 1 5) (sourceB2059 + difference 5 1) sourceC2059) = raw21056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw21056; decide +kernel
    rw [ha]
    exact (canonical21056 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2059 + difference 2 5) (sourceB2059 + difference 5 2) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2550) := by
    have ha : (tripleCharges (sourceA2059 + difference 2 5) (sourceB2059 + difference 5 2) sourceC2059) = raw28997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw28997; decide +kernel
    rw [ha]
    exact (canonical28997 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2059 + difference 3 5) (sourceB2059 + difference 5 3) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2550) := by
    have ha : (tripleCharges (sourceA2059 + difference 3 5) (sourceB2059 + difference 5 3) sourceC2059) = raw28998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw28998; decide +kernel
    rw [ha]
    exact (canonical28998 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2059 + difference 4 5) (sourceB2059 + difference 5 4) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2540) := by
    have ha : (tripleCharges (sourceA2059 + difference 4 5) (sourceB2059 + difference 5 4) sourceC2059) = raw28999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw28999; decide +kernel
    rw [ha]
    exact (canonical28999 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2059 + difference 5 5) (sourceB2059 + difference 5 5) sourceC2059) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA2059 + difference 5 5) (sourceB2059 + difference 5 5) sourceC2059) = raw21052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2059 sourceB2059 sourceC2059 difference raw21052; decide +kernel
    rw [ha]
    exact (canonical21052 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2059 + sourceB2059) sourceC2059) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2059 + sourceB2059) sourceC2059) = raw21057 := by
      apply Matrix.ext; unfold doubleCharges sourceA2059 sourceB2059 sourceC2059 raw21057; decide +kernel
    rw [ha]
    exact (canonical21057 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2059 sourceB2059 sourceC2059
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2059, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2060 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceB2060 : Charge := ![2, 0, 1, 1, -1, -3]
def sourceC2060 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2060 : Integer.Sparse Master := [(Sum.inr 864, 1), (Sum.inr 1759, 1), (Sum.inr 1874, 1), (Sum.inr 1907, 1), (Sum.inr 1911, 2), (Sum.inr 4081, -1)]

theorem sourceEq2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2060 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2060 + difference 0 0) (sourceB2060 + difference 0 0) sourceC2060) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1907) := by
    have ha : (tripleCharges (sourceA2060 + difference 0 0) (sourceB2060 + difference 0 0) sourceC2060) = raw29000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2060 sourceB2060 sourceC2060 difference raw29000; decide +kernel
    rw [ha]
    exact (canonical29000 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2060 + difference 1 0) (sourceB2060 + difference 0 1) sourceC2060) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1874) := by
    have ha : (tripleCharges (sourceA2060 + difference 1 0) (sourceB2060 + difference 0 1) sourceC2060) = raw29001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2060 sourceB2060 sourceC2060 difference raw29001; decide +kernel
    rw [ha]
    exact (canonical29001 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2060 + difference 2 0) (sourceB2060 + difference 0 2) sourceC2060) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA2060 + difference 2 0) (sourceB2060 + difference 0 2) sourceC2060) = raw28982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2060 sourceB2060 sourceC2060 difference raw28982; decide +kernel
    rw [ha]
    exact (canonical28982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2060 + difference 3 0) (sourceB2060 + difference 0 3) sourceC2060) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA2060 + difference 3 0) (sourceB2060 + difference 0 3) sourceC2060) = raw29002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2060 sourceB2060 sourceC2060 difference raw29002; decide +kernel
    rw [ha]
    exact (canonical29002 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2060 + difference 4 0) (sourceB2060 + difference 0 4) sourceC2060) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1759) := by
    have ha : (tripleCharges (sourceA2060 + difference 4 0) (sourceB2060 + difference 0 4) sourceC2060) = raw29003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2060 sourceB2060 sourceC2060 difference raw29003; decide +kernel
    rw [ha]
    exact (canonical29003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2060 + difference 5 0) (sourceB2060 + difference 0 5) sourceC2060) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 864) := by
    have ha : (tripleCharges (sourceA2060 + difference 5 0) (sourceB2060 + difference 0 5) sourceC2060) = raw29004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2060 sourceB2060 sourceC2060 difference raw29004; decide +kernel
    rw [ha]
    exact (canonical29004 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2060 + sourceB2060) sourceC2060) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA2060 + sourceB2060) sourceC2060) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2060 sourceB2060 sourceC2060 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2060 sourceB2060 sourceC2060
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2060, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2061 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2061 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC2061 : Charge := ![2, 1, -1, 0, 1, -3]
def sourceForm2061 : Integer.Sparse Master := [(Sum.inr 2075, 1), (Sum.inr 2079, 1), (Sum.inr 2082, 1), (Sum.inr 2101, 1), (Sum.inr 2205, 1), (Sum.inr 3564, 1), (Sum.inr 4080, -1)]

theorem sourceEq2061 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2061 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 0) (sourceB2061 + difference 0 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 0) (sourceB2061 + difference 0 0) sourceC2061) = raw29005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29005; decide +kernel
    rw [ha]
    exact (canonical29005 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 1) (sourceB2061 + difference 1 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 1) (sourceB2061 + difference 1 0) sourceC2061) = raw29006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29006; decide +kernel
    rw [ha]
    exact (canonical29006 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 2) (sourceB2061 + difference 2 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 2) (sourceB2061 + difference 2 0) sourceC2061) = raw29007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29007; decide +kernel
    rw [ha]
    exact (canonical29007 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 3) (sourceB2061 + difference 3 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 3) (sourceB2061 + difference 3 0) sourceC2061) = raw29008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29008; decide +kernel
    rw [ha]
    exact (canonical29008 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 4) (sourceB2061 + difference 4 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 4) (sourceB2061 + difference 4 0) sourceC2061) = raw29009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29009; decide +kernel
    rw [ha]
    exact (canonical29009 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2061 + difference 0 5) (sourceB2061 + difference 5 0) sourceC2061) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2061 + difference 0 5) (sourceB2061 + difference 5 0) sourceC2061) = raw29010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2061 sourceB2061 sourceC2061 difference raw29010; decide +kernel
    rw [ha]
    exact (canonical29010 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2061 + sourceB2061) sourceC2061) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2061 + sourceB2061) sourceC2061) = raw29011 := by
      apply Matrix.ext; unfold doubleCharges sourceA2061 sourceB2061 sourceC2061 raw29011; decide +kernel
    rw [ha]
    exact (canonical29011 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2061 sourceB2061 sourceC2061
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2061, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2062 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2062 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC2062 : Charge := ![2, 1, -1, 0, 1, -3]
def sourceForm2062 : Integer.Sparse Master := [(Sum.inr 1123, 1), (Sum.inr 1875, 1), (Sum.inr 1880, 1), (Sum.inr 1914, 1), (Sum.inr 2079, 1), (Sum.inr 2504, 1), (Sum.inr 4080, -1)]

theorem sourceEq2062 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2062 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 0) (sourceB2062 + difference 0 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 0) (sourceB2062 + difference 0 2) sourceC2062) = raw29012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29012; decide +kernel
    rw [ha]
    exact (canonical29012 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 1) (sourceB2062 + difference 1 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 1) (sourceB2062 + difference 1 2) sourceC2062) = raw29013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29013; decide +kernel
    rw [ha]
    exact (canonical29013 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 2) (sourceB2062 + difference 2 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 2) (sourceB2062 + difference 2 2) sourceC2062) = raw29005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29005; decide +kernel
    rw [ha]
    exact (canonical29005 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 3) (sourceB2062 + difference 3 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1875) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 3) (sourceB2062 + difference 3 2) sourceC2062) = raw29014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29014; decide +kernel
    rw [ha]
    exact (canonical29014 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 4) (sourceB2062 + difference 4 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 4) (sourceB2062 + difference 4 2) sourceC2062) = raw29015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29015; decide +kernel
    rw [ha]
    exact (canonical29015 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2062 + difference 2 5) (sourceB2062 + difference 5 2) sourceC2062) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA2062 + difference 2 5) (sourceB2062 + difference 5 2) sourceC2062) = raw29016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2062 sourceB2062 sourceC2062 difference raw29016; decide +kernel
    rw [ha]
    exact (canonical29016 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2062 + sourceB2062) sourceC2062) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2062 + sourceB2062) sourceC2062) = raw29011 := by
      apply Matrix.ext; unfold doubleCharges sourceA2062 sourceB2062 sourceC2062 raw29011; decide +kernel
    rw [ha]
    exact (canonical29011 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2062 sourceB2062 sourceC2062
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2062, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2063 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2063 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC2063 : Charge := ![2, 1, -1, 0, 1, -3]
def sourceForm2063 : Integer.Sparse Master := [(Sum.inr 2079, 1), (Sum.inr 2476, 1), (Sum.inr 2487, 1), (Sum.inr 2504, 1), (Sum.inr 2719, 1), (Sum.inr 3564, 1), (Sum.inr 4080, -1)]

theorem sourceEq2063 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2063 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2063 + difference 0 5) (sourceB2063 + difference 5 0) sourceC2063) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2063 + difference 0 5) (sourceB2063 + difference 5 0) sourceC2063) = raw29010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2063 sourceB2063 sourceC2063 difference raw29010; decide +kernel
    rw [ha]
    exact (canonical29010 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2063 + difference 1 5) (sourceB2063 + difference 5 1) sourceC2063) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA2063 + difference 1 5) (sourceB2063 + difference 5 1) sourceC2063) = raw29017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2063 sourceB2063 sourceC2063 difference raw29017; decide +kernel
    rw [ha]
    exact (canonical29017 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2063 + difference 2 5) (sourceB2063 + difference 5 2) sourceC2063) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA2063 + difference 2 5) (sourceB2063 + difference 5 2) sourceC2063) = raw29016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2063 sourceB2063 sourceC2063 difference raw29016; decide +kernel
    rw [ha]
    exact (canonical29016 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2063 + difference 3 5) (sourceB2063 + difference 5 3) sourceC2063) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2476) := by
    have ha : (tripleCharges (sourceA2063 + difference 3 5) (sourceB2063 + difference 5 3) sourceC2063) = raw29018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2063 sourceB2063 sourceC2063 difference raw29018; decide +kernel
    rw [ha]
    exact (canonical29018 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2063 + difference 4 5) (sourceB2063 + difference 5 4) sourceC2063) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2487) := by
    have ha : (tripleCharges (sourceA2063 + difference 4 5) (sourceB2063 + difference 5 4) sourceC2063) = raw29019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2063 sourceB2063 sourceC2063 difference raw29019; decide +kernel
    rw [ha]
    exact (canonical29019 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2063 + difference 5 5) (sourceB2063 + difference 5 5) sourceC2063) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA2063 + difference 5 5) (sourceB2063 + difference 5 5) sourceC2063) = raw29005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2063 sourceB2063 sourceC2063 difference raw29005; decide +kernel
    rw [ha]
    exact (canonical29005 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2063 + sourceB2063) sourceC2063) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2063 + sourceB2063) sourceC2063) = raw29011 := by
      apply Matrix.ext; unfold doubleCharges sourceA2063 sourceB2063 sourceC2063 raw29011; decide +kernel
    rw [ha]
    exact (canonical29011 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2063 sourceB2063 sourceC2063
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2063, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2064 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceB2064 : Charge := ![2, 1, -1, 0, 1, -3]
def sourceC2064 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2064 : Integer.Sparse Master := [(Sum.inr 916, 1), (Sum.inr 1799, 1), (Sum.inr 1874, 1), (Sum.inr 1911, 1), (Sum.inr 2018, 1), (Sum.inr 2047, 1), (Sum.inr 4081, -1)]

theorem sourceEq2064 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2064 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2064 + difference 0 0) (sourceB2064 + difference 0 0) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA2064 + difference 0 0) (sourceB2064 + difference 0 0) sourceC2064) = raw29020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29020; decide +kernel
    rw [ha]
    exact (canonical29020 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2064 + difference 1 0) (sourceB2064 + difference 0 1) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA2064 + difference 1 0) (sourceB2064 + difference 0 1) sourceC2064) = raw29021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29021; decide +kernel
    rw [ha]
    exact (canonical29021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2064 + difference 2 0) (sourceB2064 + difference 0 2) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1799) := by
    have ha : (tripleCharges (sourceA2064 + difference 2 0) (sourceB2064 + difference 0 2) sourceC2064) = raw29022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29022; decide +kernel
    rw [ha]
    exact (canonical29022 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2064 + difference 3 0) (sourceB2064 + difference 0 3) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1874) := by
    have ha : (tripleCharges (sourceA2064 + difference 3 0) (sourceB2064 + difference 0 3) sourceC2064) = raw29023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29023; decide +kernel
    rw [ha]
    exact (canonical29023 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2064 + difference 4 0) (sourceB2064 + difference 0 4) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA2064 + difference 4 0) (sourceB2064 + difference 0 4) sourceC2064) = raw29024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29024; decide +kernel
    rw [ha]
    exact (canonical29024 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2064 + difference 5 0) (sourceB2064 + difference 0 5) sourceC2064) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA2064 + difference 5 0) (sourceB2064 + difference 0 5) sourceC2064) = raw29025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2064 sourceB2064 sourceC2064 difference raw29025; decide +kernel
    rw [ha]
    exact (canonical29025 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2064 + sourceB2064) sourceC2064) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA2064 + sourceB2064) sourceC2064) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2064 sourceB2064 sourceC2064 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2064 sourceB2064 sourceC2064
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2064, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2065 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2065 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceC2065 : Charge := ![2, 1, -1, 1, -1, -2]
def sourceForm2065 : Integer.Sparse Master := [(Sum.inr 2449, 1), (Sum.inr 2452, 1), (Sum.inr 2461, 1), (Sum.inr 2477, 1), (Sum.inr 2694, 1), (Sum.inr 3793, 1), (Sum.inr 4090, -1)]

theorem sourceEq2065 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2065 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 0) (sourceB2065 + difference 0 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 0) (sourceB2065 + difference 0 0) sourceC2065) = raw29026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29026; decide +kernel
    rw [ha]
    exact (canonical29026 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 1) (sourceB2065 + difference 1 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 1) (sourceB2065 + difference 1 0) sourceC2065) = raw29027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29027; decide +kernel
    rw [ha]
    exact (canonical29027 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 2) (sourceB2065 + difference 2 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 2) (sourceB2065 + difference 2 0) sourceC2065) = raw29028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29028; decide +kernel
    rw [ha]
    exact (canonical29028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 3) (sourceB2065 + difference 3 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2461) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 3) (sourceB2065 + difference 3 0) sourceC2065) = raw29029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29029; decide +kernel
    rw [ha]
    exact (canonical29029 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 4) (sourceB2065 + difference 4 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 4) (sourceB2065 + difference 4 0) sourceC2065) = raw29030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29030; decide +kernel
    rw [ha]
    exact (canonical29030 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2065 + difference 0 5) (sourceB2065 + difference 5 0) sourceC2065) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3793) := by
    have ha : (tripleCharges (sourceA2065 + difference 0 5) (sourceB2065 + difference 5 0) sourceC2065) = raw29031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2065 sourceB2065 sourceC2065 difference raw29031; decide +kernel
    rw [ha]
    exact (canonical29031 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2065 + sourceB2065) sourceC2065) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2065 + sourceB2065) sourceC2065) = raw29032 := by
      apply Matrix.ext; unfold doubleCharges sourceA2065 sourceB2065 sourceC2065 raw29032; decide +kernel
    rw [ha]
    exact (canonical29032 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2065 sourceB2065 sourceC2065
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2065, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2066 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2066 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceC2066 : Charge := ![2, 1, -1, 1, -1, -2]
def sourceForm2066 : Integer.Sparse Master := [(Sum.inr 1107, 1), (Sum.inr 2317, 1), (Sum.inr 2415, 1), (Sum.inr 2449, 2), (Sum.inr 2461, 1), (Sum.inr 4090, -1)]

theorem sourceEq2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2066 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2066 + difference 2 0) (sourceB2066 + difference 0 2) sourceC2066) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1107) := by
    have ha : (tripleCharges (sourceA2066 + difference 2 0) (sourceB2066 + difference 0 2) sourceC2066) = raw29033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2066 sourceB2066 sourceC2066 difference raw29033; decide +kernel
    rw [ha]
    exact (canonical29033 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2066 + difference 2 1) (sourceB2066 + difference 1 2) sourceC2066) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2317) := by
    have ha : (tripleCharges (sourceA2066 + difference 2 1) (sourceB2066 + difference 1 2) sourceC2066) = raw29034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2066 sourceB2066 sourceC2066 difference raw29034; decide +kernel
    rw [ha]
    exact (canonical29034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2066 + difference 2 2) (sourceB2066 + difference 2 2) sourceC2066) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA2066 + difference 2 2) (sourceB2066 + difference 2 2) sourceC2066) = raw29026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2066 sourceB2066 sourceC2066 difference raw29026; decide +kernel
    rw [ha]
    exact (canonical29026 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2066 + difference 2 3) (sourceB2066 + difference 3 2) sourceC2066) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2415) := by
    have ha : (tripleCharges (sourceA2066 + difference 2 3) (sourceB2066 + difference 3 2) sourceC2066) = raw29035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2066 sourceB2066 sourceC2066 difference raw29035; decide +kernel
    rw [ha]
    exact (canonical29035 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2066 + difference 2 4) (sourceB2066 + difference 4 2) sourceC2066) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA2066 + difference 2 4) (sourceB2066 + difference 4 2) sourceC2066) = raw29036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2066 sourceB2066 sourceC2066 difference raw29036; decide +kernel
    rw [ha]
    exact (canonical29036 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2066 + difference 2 5) (sourceB2066 + difference 5 2) sourceC2066) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2461) := by
    have ha : (tripleCharges (sourceA2066 + difference 2 5) (sourceB2066 + difference 5 2) sourceC2066) = raw29037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2066 sourceB2066 sourceC2066 difference raw29037; decide +kernel
    rw [ha]
    exact (canonical29037 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2066 + sourceB2066) sourceC2066) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2066 + sourceB2066) sourceC2066) = raw29032 := by
      apply Matrix.ext; unfold doubleCharges sourceA2066 sourceB2066 sourceC2066 raw29032; decide +kernel
    rw [ha]
    exact (canonical29032 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2066 sourceB2066 sourceC2066
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2066, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2067 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceB2067 : Charge := ![2, 1, -1, 1, -1, -2]
def sourceC2067 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2067 : Integer.Sparse Master := [(Sum.inr 1862, 1), (Sum.inr 1864, 1), (Sum.inr 1868, 1), (Sum.inr 1944, 1), (Sum.inr 1996, 1), (Sum.inr 3432, 1), (Sum.inr 4081, -1)]

theorem sourceEq2067 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2067 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2067 + difference 0 0) (sourceB2067 + difference 0 0) sourceC2067) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3432) := by
    have ha : (tripleCharges (sourceA2067 + difference 0 0) (sourceB2067 + difference 0 0) sourceC2067) = raw29038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2067 sourceB2067 sourceC2067 difference raw29038; decide +kernel
    rw [ha]
    exact (canonical29038 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2067 + difference 1 0) (sourceB2067 + difference 0 1) sourceC2067) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1996) := by
    have ha : (tripleCharges (sourceA2067 + difference 1 0) (sourceB2067 + difference 0 1) sourceC2067) = raw29039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2067 sourceB2067 sourceC2067 difference raw29039; decide +kernel
    rw [ha]
    exact (canonical29039 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2067 + difference 2 0) (sourceB2067 + difference 0 2) sourceC2067) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1868) := by
    have ha : (tripleCharges (sourceA2067 + difference 2 0) (sourceB2067 + difference 0 2) sourceC2067) = raw29040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2067 sourceB2067 sourceC2067 difference raw29040; decide +kernel
    rw [ha]
    exact (canonical29040 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2067 + difference 3 0) (sourceB2067 + difference 0 3) sourceC2067) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1944) := by
    have ha : (tripleCharges (sourceA2067 + difference 3 0) (sourceB2067 + difference 0 3) sourceC2067) = raw29041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2067 sourceB2067 sourceC2067 difference raw29041; decide +kernel
    rw [ha]
    exact (canonical29041 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2067 + difference 4 0) (sourceB2067 + difference 0 4) sourceC2067) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1864) := by
    have ha : (tripleCharges (sourceA2067 + difference 4 0) (sourceB2067 + difference 0 4) sourceC2067) = raw29042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2067 sourceB2067 sourceC2067 difference raw29042; decide +kernel
    rw [ha]
    exact (canonical29042 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2067 + difference 5 0) (sourceB2067 + difference 0 5) sourceC2067) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1862) := by
    have ha : (tripleCharges (sourceA2067 + difference 5 0) (sourceB2067 + difference 0 5) sourceC2067) = raw29043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2067 sourceB2067 sourceC2067 difference raw29043; decide +kernel
    rw [ha]
    exact (canonical29043 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2067 + sourceB2067) sourceC2067) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA2067 + sourceB2067) sourceC2067) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2067 sourceB2067 sourceC2067 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2067 sourceB2067 sourceC2067
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2067, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2068 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2068 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2068 : Charge := ![2, 1, -1, 1, 0, -3]
def sourceForm2068 : Integer.Sparse Master := [(Sum.inr 1105, 1), (Sum.inr 1860, 1), (Sum.inr 1866, 1), (Sum.inr 1914, 1), (Sum.inr 1987, 1), (Sum.inr 2458, 1), (Sum.inr 4080, -1)]

theorem sourceEq2068 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2068 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2068 + difference 2 0) (sourceB2068 + difference 0 2) sourceC2068) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1105) := by
    have ha : (tripleCharges (sourceA2068 + difference 2 0) (sourceB2068 + difference 0 2) sourceC2068) = raw29044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2068 sourceB2068 sourceC2068 difference raw29044; decide +kernel
    rw [ha]
    exact (canonical29044 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2068 + difference 2 1) (sourceB2068 + difference 1 2) sourceC2068) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1860) := by
    have ha : (tripleCharges (sourceA2068 + difference 2 1) (sourceB2068 + difference 1 2) sourceC2068) = raw29045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2068 sourceB2068 sourceC2068 difference raw29045; decide +kernel
    rw [ha]
    exact (canonical29045 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2068 + difference 2 2) (sourceB2068 + difference 2 2) sourceC2068) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA2068 + difference 2 2) (sourceB2068 + difference 2 2) sourceC2068) = raw29046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2068 sourceB2068 sourceC2068 difference raw29046; decide +kernel
    rw [ha]
    exact (canonical29046 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2068 + difference 2 3) (sourceB2068 + difference 3 2) sourceC2068) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1866) := by
    have ha : (tripleCharges (sourceA2068 + difference 2 3) (sourceB2068 + difference 3 2) sourceC2068) = raw29047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2068 sourceB2068 sourceC2068 difference raw29047; decide +kernel
    rw [ha]
    exact (canonical29047 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2068 + difference 2 4) (sourceB2068 + difference 4 2) sourceC2068) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA2068 + difference 2 4) (sourceB2068 + difference 4 2) sourceC2068) = raw29048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2068 sourceB2068 sourceC2068 difference raw29048; decide +kernel
    rw [ha]
    exact (canonical29048 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2068 + difference 2 5) (sourceB2068 + difference 5 2) sourceC2068) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2458) := by
    have ha : (tripleCharges (sourceA2068 + difference 2 5) (sourceB2068 + difference 5 2) sourceC2068) = raw29049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2068 sourceB2068 sourceC2068 difference raw29049; decide +kernel
    rw [ha]
    exact (canonical29049 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2068 + sourceB2068) sourceC2068) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2068 + sourceB2068) sourceC2068) = raw29050 := by
      apply Matrix.ext; unfold doubleCharges sourceA2068 sourceB2068 sourceC2068 raw29050; decide +kernel
    rw [ha]
    exact (canonical29050 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2068 sourceB2068 sourceC2068
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2068, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2069 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2069 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2069 : Charge := ![2, 1, -1, 1, 0, -3]
def sourceForm2069 : Integer.Sparse Master := [(Sum.inr 900, 1), (Sum.inr 1786, 1), (Sum.inr 1866, 1), (Sum.inr 1987, 2), (Sum.inr 1999, 1), (Sum.inr 4080, -1)]

theorem sourceEq2069 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2069 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2069 + difference 0 3) (sourceB2069 + difference 3 0) sourceC2069) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1999) := by
    have ha : (tripleCharges (sourceA2069 + difference 0 3) (sourceB2069 + difference 3 0) sourceC2069) = raw29051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2069 sourceB2069 sourceC2069 difference raw29051; decide +kernel
    rw [ha]
    exact (canonical29051 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2069 + difference 1 3) (sourceB2069 + difference 3 1) sourceC2069) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA2069 + difference 1 3) (sourceB2069 + difference 3 1) sourceC2069) = raw29052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2069 sourceB2069 sourceC2069 difference raw29052; decide +kernel
    rw [ha]
    exact (canonical29052 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2069 + difference 2 3) (sourceB2069 + difference 3 2) sourceC2069) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1866) := by
    have ha : (tripleCharges (sourceA2069 + difference 2 3) (sourceB2069 + difference 3 2) sourceC2069) = raw29047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2069 sourceB2069 sourceC2069 difference raw29047; decide +kernel
    rw [ha]
    exact (canonical29047 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2069 + difference 3 3) (sourceB2069 + difference 3 3) sourceC2069) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA2069 + difference 3 3) (sourceB2069 + difference 3 3) sourceC2069) = raw29046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2069 sourceB2069 sourceC2069 difference raw29046; decide +kernel
    rw [ha]
    exact (canonical29046 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2069 + difference 4 3) (sourceB2069 + difference 3 4) sourceC2069) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1786) := by
    have ha : (tripleCharges (sourceA2069 + difference 4 3) (sourceB2069 + difference 3 4) sourceC2069) = raw29053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2069 sourceB2069 sourceC2069 difference raw29053; decide +kernel
    rw [ha]
    exact (canonical29053 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2069 + difference 5 3) (sourceB2069 + difference 3 5) sourceC2069) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 900) := by
    have ha : (tripleCharges (sourceA2069 + difference 5 3) (sourceB2069 + difference 3 5) sourceC2069) = raw29054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2069 sourceB2069 sourceC2069 difference raw29054; decide +kernel
    rw [ha]
    exact (canonical29054 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2069 + sourceB2069) sourceC2069) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2069 + sourceB2069) sourceC2069) = raw29050 := by
      apply Matrix.ext; unfold doubleCharges sourceA2069 sourceB2069 sourceC2069 raw29050; decide +kernel
    rw [ha]
    exact (canonical29050 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2069 sourceB2069 sourceC2069
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2069, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2070 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2070 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2070 : Charge := ![2, 1, -1, 1, 0, -3]
def sourceForm2070 : Integer.Sparse Master := [(Sum.inr 1987, 1), (Sum.inr 2451, 1), (Sum.inr 2458, 1), (Sum.inr 2476, 1), (Sum.inr 2693, 1), (Sum.inr 3514, 1), (Sum.inr 4080, -1)]

theorem sourceEq2070 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2070 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2070 + difference 0 5) (sourceB2070 + difference 5 0) sourceC2070) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2070 + difference 0 5) (sourceB2070 + difference 5 0) sourceC2070) = raw29055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2070 sourceB2070 sourceC2070 difference raw29055; decide +kernel
    rw [ha]
    exact (canonical29055 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2070 + difference 1 5) (sourceB2070 + difference 5 1) sourceC2070) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA2070 + difference 1 5) (sourceB2070 + difference 5 1) sourceC2070) = raw29056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2070 sourceB2070 sourceC2070 difference raw29056; decide +kernel
    rw [ha]
    exact (canonical29056 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2070 + difference 2 5) (sourceB2070 + difference 5 2) sourceC2070) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2458) := by
    have ha : (tripleCharges (sourceA2070 + difference 2 5) (sourceB2070 + difference 5 2) sourceC2070) = raw29049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2070 sourceB2070 sourceC2070 difference raw29049; decide +kernel
    rw [ha]
    exact (canonical29049 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2070 + difference 3 5) (sourceB2070 + difference 5 3) sourceC2070) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2476) := by
    have ha : (tripleCharges (sourceA2070 + difference 3 5) (sourceB2070 + difference 5 3) sourceC2070) = raw29057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2070 sourceB2070 sourceC2070 difference raw29057; decide +kernel
    rw [ha]
    exact (canonical29057 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2070 + difference 4 5) (sourceB2070 + difference 5 4) sourceC2070) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2451) := by
    have ha : (tripleCharges (sourceA2070 + difference 4 5) (sourceB2070 + difference 5 4) sourceC2070) = raw29058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2070 sourceB2070 sourceC2070 difference raw29058; decide +kernel
    rw [ha]
    exact (canonical29058 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2070 + difference 5 5) (sourceB2070 + difference 5 5) sourceC2070) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA2070 + difference 5 5) (sourceB2070 + difference 5 5) sourceC2070) = raw29046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2070 sourceB2070 sourceC2070 difference raw29046; decide +kernel
    rw [ha]
    exact (canonical29046 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2070 + sourceB2070) sourceC2070) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2070 + sourceB2070) sourceC2070) = raw29050 := by
      apply Matrix.ext; unfold doubleCharges sourceA2070 sourceB2070 sourceC2070 raw29050; decide +kernel
    rw [ha]
    exact (canonical29050 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2070 sourceB2070 sourceC2070
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2070, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2071 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB2071 : Charge := ![2, 1, -1, 1, 0, -3]
def sourceC2071 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2071 : Integer.Sparse Master := [(Sum.inr 898, 1), (Sum.inr 1784, 1), (Sum.inr 1862, 1), (Sum.inr 1911, 1), (Sum.inr 1986, 1), (Sum.inr 1996, 1), (Sum.inr 4081, -1)]

theorem sourceEq2071 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2071 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2071 + difference 0 0) (sourceB2071 + difference 0 0) sourceC2071) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1996) := by
    have ha : (tripleCharges (sourceA2071 + difference 0 0) (sourceB2071 + difference 0 0) sourceC2071) = raw29059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2071 sourceB2071 sourceC2071 difference raw29059; decide +kernel
    rw [ha]
    exact (canonical29059 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2071 + difference 1 0) (sourceB2071 + difference 0 1) sourceC2071) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1986) := by
    have ha : (tripleCharges (sourceA2071 + difference 1 0) (sourceB2071 + difference 0 1) sourceC2071) = raw29060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2071 sourceB2071 sourceC2071 difference raw29060; decide +kernel
    rw [ha]
    exact (canonical29060 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2071 + difference 2 0) (sourceB2071 + difference 0 2) sourceC2071) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1784) := by
    have ha : (tripleCharges (sourceA2071 + difference 2 0) (sourceB2071 + difference 0 2) sourceC2071) = raw29061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2071 sourceB2071 sourceC2071 difference raw29061; decide +kernel
    rw [ha]
    exact (canonical29061 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2071 + difference 3 0) (sourceB2071 + difference 0 3) sourceC2071) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA2071 + difference 3 0) (sourceB2071 + difference 0 3) sourceC2071) = raw29024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2071 sourceB2071 sourceC2071 difference raw29024; decide +kernel
    rw [ha]
    exact (canonical29024 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2071 + difference 4 0) (sourceB2071 + difference 0 4) sourceC2071) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1862) := by
    have ha : (tripleCharges (sourceA2071 + difference 4 0) (sourceB2071 + difference 0 4) sourceC2071) = raw29043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2071 sourceB2071 sourceC2071 difference raw29043; decide +kernel
    rw [ha]
    exact (canonical29043 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2071 + difference 5 0) (sourceB2071 + difference 0 5) sourceC2071) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 898) := by
    have ha : (tripleCharges (sourceA2071 + difference 5 0) (sourceB2071 + difference 0 5) sourceC2071) = raw29062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2071 sourceB2071 sourceC2071 difference raw29062; decide +kernel
    rw [ha]
    exact (canonical29062 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2071 + sourceB2071) sourceC2071) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA2071 + sourceB2071) sourceC2071) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2071 sourceB2071 sourceC2071 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2071 sourceB2071 sourceC2071
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2071, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2072 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2072 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC2072 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceForm2072 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4346, 2), (Sum.inr 4356, 1), (Sum.inr 4360, 1), (Sum.inr 4505, 1), (Sum.inr 4543, 2), (Sum.inr 4557, 1), (Sum.inr 4605, 1), (Sum.inr 4681, 2), (Sum.inr 4692, 1), (Sum.inr 4760, 2), (Sum.inr 4769, 2), (Sum.inr 4804, 2), (Sum.inr 4834, 2), (Sum.inr 4841, 2), (Sum.inr 4846, 1), (Sum.inr 4897, 1), (Sum.inr 5099, 2), (Sum.inr 5110, 1), (Sum.inr 5272, 1), (Sum.inr 5274, 1)]

theorem sourceEq2072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2072 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 1) (sourceB2072 + difference 1 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 1) (sourceB2072 + difference 1 0) sourceC2072) = raw29063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29063; decide +kernel
    rw [ha]
    exact (canonical29063 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 2) (sourceB2072 + difference 2 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 2) (sourceB2072 + difference 2 0) sourceC2072) = raw29064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29064; decide +kernel
    rw [ha]
    exact (canonical29064 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 3) (sourceB2072 + difference 3 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 3) (sourceB2072 + difference 3 0) sourceC2072) = raw29065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29065; decide +kernel
    rw [ha]
    exact (canonical29065 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 4) (sourceB2072 + difference 4 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 4) (sourceB2072 + difference 4 0) sourceC2072) = raw29066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29066; decide +kernel
    rw [ha]
    exact (canonical29066 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 5) (sourceB2072 + difference 5 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 5) (sourceB2072 + difference 5 0) sourceC2072) = raw29067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29067; decide +kernel
    rw [ha]
    exact (canonical29067 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 0) (sourceB2072 + difference 0 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 0) (sourceB2072 + difference 0 1) sourceC2072) = raw29068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29068; decide +kernel
    rw [ha]
    exact (canonical29068 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 2) (sourceB2072 + difference 2 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 2) (sourceB2072 + difference 2 1) sourceC2072) = raw29069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29069; decide +kernel
    rw [ha]
    exact (canonical29069 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 3) (sourceB2072 + difference 3 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 3) (sourceB2072 + difference 3 1) sourceC2072) = raw29070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29070; decide +kernel
    rw [ha]
    exact (canonical29070 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 4) (sourceB2072 + difference 4 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 4) (sourceB2072 + difference 4 1) sourceC2072) = raw29071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29071; decide +kernel
    rw [ha]
    exact (canonical29071 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 5) (sourceB2072 + difference 5 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 5) (sourceB2072 + difference 5 1) sourceC2072) = raw29072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29072; decide +kernel
    rw [ha]
    exact (canonical29072 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 0) (sourceB2072 + difference 0 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 0) (sourceB2072 + difference 0 2) sourceC2072) = raw29073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29073; decide +kernel
    rw [ha]
    exact (canonical29073 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 1) (sourceB2072 + difference 1 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 1) (sourceB2072 + difference 1 2) sourceC2072) = raw29074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29074; decide +kernel
    rw [ha]
    exact (canonical29074 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 3) (sourceB2072 + difference 3 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 3) (sourceB2072 + difference 3 2) sourceC2072) = raw29075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29075; decide +kernel
    rw [ha]
    exact (canonical29075 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 4) (sourceB2072 + difference 4 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 4) (sourceB2072 + difference 4 2) sourceC2072) = raw29076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29076; decide +kernel
    rw [ha]
    exact (canonical29076 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 5) (sourceB2072 + difference 5 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 5) (sourceB2072 + difference 5 2) sourceC2072) = raw29077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29077; decide +kernel
    rw [ha]
    exact (canonical29077 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 0) (sourceB2072 + difference 0 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 0) (sourceB2072 + difference 0 3) sourceC2072) = raw29078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29078; decide +kernel
    rw [ha]
    exact (canonical29078 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 1) (sourceB2072 + difference 1 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 1) (sourceB2072 + difference 1 3) sourceC2072) = raw29079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29079; decide +kernel
    rw [ha]
    exact (canonical29079 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 2) (sourceB2072 + difference 2 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 2) (sourceB2072 + difference 2 3) sourceC2072) = raw29080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29080; decide +kernel
    rw [ha]
    exact (canonical29080 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 4) (sourceB2072 + difference 4 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 4) (sourceB2072 + difference 4 3) sourceC2072) = raw29081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29081; decide +kernel
    rw [ha]
    exact (canonical29081 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 5) (sourceB2072 + difference 5 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 5) (sourceB2072 + difference 5 3) sourceC2072) = raw29082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29082; decide +kernel
    rw [ha]
    exact (canonical29082 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 0) (sourceB2072 + difference 0 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 0) (sourceB2072 + difference 0 4) sourceC2072) = raw29083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29083; decide +kernel
    rw [ha]
    exact (canonical29083 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 1) (sourceB2072 + difference 1 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 1) (sourceB2072 + difference 1 4) sourceC2072) = raw29084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29084; decide +kernel
    rw [ha]
    exact (canonical29084 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 2) (sourceB2072 + difference 2 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 2) (sourceB2072 + difference 2 4) sourceC2072) = raw29085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29085; decide +kernel
    rw [ha]
    exact (canonical29085 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 3) (sourceB2072 + difference 3 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 3) (sourceB2072 + difference 3 4) sourceC2072) = raw29086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29086; decide +kernel
    rw [ha]
    exact (canonical29086 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 5) (sourceB2072 + difference 5 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 5) (sourceB2072 + difference 5 4) sourceC2072) = raw29087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29087; decide +kernel
    rw [ha]
    exact (canonical29087 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 0) (sourceB2072 + difference 0 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 0) (sourceB2072 + difference 0 5) sourceC2072) = raw29088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29088; decide +kernel
    rw [ha]
    exact (canonical29088 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 1) (sourceB2072 + difference 1 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 1) (sourceB2072 + difference 1 5) sourceC2072) = raw29089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29089; decide +kernel
    rw [ha]
    exact (canonical29089 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 2) (sourceB2072 + difference 2 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 2) (sourceB2072 + difference 2 5) sourceC2072) = raw29090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29090; decide +kernel
    rw [ha]
    exact (canonical29090 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 3) (sourceB2072 + difference 3 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 3) (sourceB2072 + difference 3 5) sourceC2072) = raw29091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29091; decide +kernel
    rw [ha]
    exact (canonical29091 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 4) (sourceB2072 + difference 4 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 4) (sourceB2072 + difference 4 5) sourceC2072) = raw29092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29092; decide +kernel
    rw [ha]
    exact (canonical29092 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2072 sourceB2072 sourceC2072
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2072, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2073 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2073 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC2073 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceForm2073 : Integer.Sparse Master := [(Sum.inr 1674, 2), (Sum.inr 1692, 1), (Sum.inr 1693, 1), (Sum.inr 1754, 1), (Sum.inr 2151, 2), (Sum.inr 2167, 1), (Sum.inr 2168, 1), (Sum.inr 2173, 2), (Sum.inr 2184, 2), (Sum.inr 2185, 2), (Sum.inr 2203, 2), (Sum.inr 2205, 2), (Sum.inr 2226, 1), (Sum.inr 2228, 2), (Sum.inr 2229, 1), (Sum.inr 2292, 1), (Sum.inr 2685, 1), (Sum.inr 2704, 2), (Sum.inr 2740, 1), (Sum.inr 2742, 1), (Sum.inr 4084, 1)]

theorem sourceEq2073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2073 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 1) (sourceB2073 + difference 1 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 1) (sourceB2073 + difference 1 0) sourceC2073) = raw29093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29093; decide +kernel
    rw [ha]
    exact (canonical29093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 2) (sourceB2073 + difference 2 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 2) (sourceB2073 + difference 2 0) sourceC2073) = raw29094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29094; decide +kernel
    rw [ha]
    exact (canonical29094 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 3) (sourceB2073 + difference 3 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 3) (sourceB2073 + difference 3 0) sourceC2073) = raw29095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29095; decide +kernel
    rw [ha]
    exact (canonical29095 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 4) (sourceB2073 + difference 4 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 4) (sourceB2073 + difference 4 0) sourceC2073) = raw29096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29096; decide +kernel
    rw [ha]
    exact (canonical29096 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2073 + difference 0 5) (sourceB2073 + difference 5 0) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2073 + difference 0 5) (sourceB2073 + difference 5 0) sourceC2073) = raw29097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29097; decide +kernel
    rw [ha]
    exact (canonical29097 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 0) (sourceB2073 + difference 0 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 0) (sourceB2073 + difference 0 1) sourceC2073) = raw29098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29098; decide +kernel
    rw [ha]
    exact (canonical29098 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 2) (sourceB2073 + difference 2 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 2) (sourceB2073 + difference 2 1) sourceC2073) = raw29099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29099; decide +kernel
    rw [ha]
    exact (canonical29099 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 3) (sourceB2073 + difference 3 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 3) (sourceB2073 + difference 3 1) sourceC2073) = raw29100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29100; decide +kernel
    rw [ha]
    exact (canonical29100 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 4) (sourceB2073 + difference 4 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 4) (sourceB2073 + difference 4 1) sourceC2073) = raw29101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29101; decide +kernel
    rw [ha]
    exact (canonical29101 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2073 + difference 1 5) (sourceB2073 + difference 5 1) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2073 + difference 1 5) (sourceB2073 + difference 5 1) sourceC2073) = raw29102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29102; decide +kernel
    rw [ha]
    exact (canonical29102 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 0) (sourceB2073 + difference 0 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 0) (sourceB2073 + difference 0 2) sourceC2073) = raw29103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29103; decide +kernel
    rw [ha]
    exact (canonical29103 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 1) (sourceB2073 + difference 1 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 1) (sourceB2073 + difference 1 2) sourceC2073) = raw29104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29104; decide +kernel
    rw [ha]
    exact (canonical29104 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 3) (sourceB2073 + difference 3 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2173) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 3) (sourceB2073 + difference 3 2) sourceC2073) = raw29105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29105; decide +kernel
    rw [ha]
    exact (canonical29105 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 4) (sourceB2073 + difference 4 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 4) (sourceB2073 + difference 4 2) sourceC2073) = raw29106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29106; decide +kernel
    rw [ha]
    exact (canonical29106 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2073 + difference 2 5) (sourceB2073 + difference 5 2) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2073 + difference 2 5) (sourceB2073 + difference 5 2) sourceC2073) = raw29107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29107; decide +kernel
    rw [ha]
    exact (canonical29107 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 0) (sourceB2073 + difference 0 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 0) (sourceB2073 + difference 0 3) sourceC2073) = raw29108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29108; decide +kernel
    rw [ha]
    exact (canonical29108 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 1) (sourceB2073 + difference 1 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 1) (sourceB2073 + difference 1 3) sourceC2073) = raw29109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29109; decide +kernel
    rw [ha]
    exact (canonical29109 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 2) (sourceB2073 + difference 2 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2173) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 2) (sourceB2073 + difference 2 3) sourceC2073) = raw29110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29110; decide +kernel
    rw [ha]
    exact (canonical29110 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 4) (sourceB2073 + difference 4 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 4) (sourceB2073 + difference 4 3) sourceC2073) = raw29111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29111; decide +kernel
    rw [ha]
    exact (canonical29111 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2073 + difference 3 5) (sourceB2073 + difference 5 3) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2073 + difference 3 5) (sourceB2073 + difference 5 3) sourceC2073) = raw29112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29112; decide +kernel
    rw [ha]
    exact (canonical29112 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 0) (sourceB2073 + difference 0 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 0) (sourceB2073 + difference 0 4) sourceC2073) = raw29113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29113; decide +kernel
    rw [ha]
    exact (canonical29113 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 1) (sourceB2073 + difference 1 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 1) (sourceB2073 + difference 1 4) sourceC2073) = raw29114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29114; decide +kernel
    rw [ha]
    exact (canonical29114 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 2) (sourceB2073 + difference 2 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 2) (sourceB2073 + difference 2 4) sourceC2073) = raw29115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29115; decide +kernel
    rw [ha]
    exact (canonical29115 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 3) (sourceB2073 + difference 3 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 3) (sourceB2073 + difference 3 4) sourceC2073) = raw29116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29116; decide +kernel
    rw [ha]
    exact (canonical29116 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2073 + difference 4 5) (sourceB2073 + difference 5 4) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2073 + difference 4 5) (sourceB2073 + difference 5 4) sourceC2073) = raw29117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29117; decide +kernel
    rw [ha]
    exact (canonical29117 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 0) (sourceB2073 + difference 0 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 0) (sourceB2073 + difference 0 5) sourceC2073) = raw29118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29118; decide +kernel
    rw [ha]
    exact (canonical29118 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 1) (sourceB2073 + difference 1 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 1) (sourceB2073 + difference 1 5) sourceC2073) = raw29119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29119; decide +kernel
    rw [ha]
    exact (canonical29119 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 2) (sourceB2073 + difference 2 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 2) (sourceB2073 + difference 2 5) sourceC2073) = raw29120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29120; decide +kernel
    rw [ha]
    exact (canonical29120 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 3) (sourceB2073 + difference 3 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 3) (sourceB2073 + difference 3 5) sourceC2073) = raw29121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29121; decide +kernel
    rw [ha]
    exact (canonical29121 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2073 + difference 5 4) (sourceB2073 + difference 4 5) sourceC2073) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA2073 + difference 5 4) (sourceB2073 + difference 4 5) sourceC2073) = raw29122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2073 sourceB2073 sourceC2073 difference raw29122; decide +kernel
    rw [ha]
    exact (canonical29122 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2073 sourceB2073 sourceC2073
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2073, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2074 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2074 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC2074 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceForm2074 : Integer.Sparse Master := [(Sum.inr 2382, 1), (Sum.inr 2385, 1), (Sum.inr 2388, 1), (Sum.inr 2403, 1), (Sum.inr 2672, 1), (Sum.inr 3766, 1), (Sum.inr 4088, -1)]

theorem sourceEq2074 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2074 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 0) (sourceB2074 + difference 0 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 0) (sourceB2074 + difference 0 0) sourceC2074) = raw29123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29123; decide +kernel
    rw [ha]
    exact (canonical29123 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 1) (sourceB2074 + difference 1 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 1) (sourceB2074 + difference 1 0) sourceC2074) = raw29124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29124; decide +kernel
    rw [ha]
    exact (canonical29124 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 2) (sourceB2074 + difference 2 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 2) (sourceB2074 + difference 2 0) sourceC2074) = raw29125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29125; decide +kernel
    rw [ha]
    exact (canonical29125 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 3) (sourceB2074 + difference 3 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2403) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 3) (sourceB2074 + difference 3 0) sourceC2074) = raw29126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29126; decide +kernel
    rw [ha]
    exact (canonical29126 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 4) (sourceB2074 + difference 4 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 4) (sourceB2074 + difference 4 0) sourceC2074) = raw29127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29127; decide +kernel
    rw [ha]
    exact (canonical29127 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2074 + difference 0 5) (sourceB2074 + difference 5 0) sourceC2074) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2074 + difference 0 5) (sourceB2074 + difference 5 0) sourceC2074) = raw29128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2074 sourceB2074 sourceC2074 difference raw29128; decide +kernel
    rw [ha]
    exact (canonical29128 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2074 + sourceB2074) sourceC2074) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2074 + sourceB2074) sourceC2074) = raw29129 := by
      apply Matrix.ext; unfold doubleCharges sourceA2074 sourceB2074 sourceC2074 raw29129; decide +kernel
    rw [ha]
    exact (canonical29129 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2074 sourceB2074 sourceC2074
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2074, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2075 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2075 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC2075 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceForm2075 : Integer.Sparse Master := [(Sum.inr 1101, 1), (Sum.inr 2309, 1), (Sum.inr 2371, 1), (Sum.inr 2385, 2), (Sum.inr 2403, 1), (Sum.inr 4088, -1)]

theorem sourceEq2075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2075 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2075 + difference 0 3) (sourceB2075 + difference 3 0) sourceC2075) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2403) := by
    have ha : (tripleCharges (sourceA2075 + difference 0 3) (sourceB2075 + difference 3 0) sourceC2075) = raw29126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2075 sourceB2075 sourceC2075 difference raw29126; decide +kernel
    rw [ha]
    exact (canonical29126 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2075 + difference 1 3) (sourceB2075 + difference 3 1) sourceC2075) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA2075 + difference 1 3) (sourceB2075 + difference 3 1) sourceC2075) = raw29130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2075 sourceB2075 sourceC2075 difference raw29130; decide +kernel
    rw [ha]
    exact (canonical29130 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2075 + difference 2 3) (sourceB2075 + difference 3 2) sourceC2075) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2371) := by
    have ha : (tripleCharges (sourceA2075 + difference 2 3) (sourceB2075 + difference 3 2) sourceC2075) = raw29131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2075 sourceB2075 sourceC2075 difference raw29131; decide +kernel
    rw [ha]
    exact (canonical29131 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2075 + difference 3 3) (sourceB2075 + difference 3 3) sourceC2075) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA2075 + difference 3 3) (sourceB2075 + difference 3 3) sourceC2075) = raw29123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2075 sourceB2075 sourceC2075 difference raw29123; decide +kernel
    rw [ha]
    exact (canonical29123 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2075 + difference 4 3) (sourceB2075 + difference 3 4) sourceC2075) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2309) := by
    have ha : (tripleCharges (sourceA2075 + difference 4 3) (sourceB2075 + difference 3 4) sourceC2075) = raw29132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2075 sourceB2075 sourceC2075 difference raw29132; decide +kernel
    rw [ha]
    exact (canonical29132 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2075 + difference 5 3) (sourceB2075 + difference 3 5) sourceC2075) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1101) := by
    have ha : (tripleCharges (sourceA2075 + difference 5 3) (sourceB2075 + difference 3 5) sourceC2075) = raw29133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2075 sourceB2075 sourceC2075 difference raw29133; decide +kernel
    rw [ha]
    exact (canonical29133 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2075 + sourceB2075) sourceC2075) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2075 + sourceB2075) sourceC2075) = raw29129 := by
      apply Matrix.ext; unfold doubleCharges sourceA2075 sourceB2075 sourceC2075 raw29129; decide +kernel
    rw [ha]
    exact (canonical29129 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2075 sourceB2075 sourceC2075
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2075, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2076 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2076 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC2076 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceForm2076 : Integer.Sparse Master := [(Sum.inr 1110, 1), (Sum.inr 2295, 1), (Sum.inr 2300, 1), (Sum.inr 2309, 1), (Sum.inr 2385, 1), (Sum.inr 2468, 1), (Sum.inr 4088, -1)]

theorem sourceEq2076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2076 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2076 + difference 4 0) (sourceB2076 + difference 0 4) sourceC2076) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA2076 + difference 4 0) (sourceB2076 + difference 0 4) sourceC2076) = raw29134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2076 sourceB2076 sourceC2076 difference raw29134; decide +kernel
    rw [ha]
    exact (canonical29134 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2076 + difference 4 1) (sourceB2076 + difference 1 4) sourceC2076) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2300) := by
    have ha : (tripleCharges (sourceA2076 + difference 4 1) (sourceB2076 + difference 1 4) sourceC2076) = raw29135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2076 sourceB2076 sourceC2076 difference raw29135; decide +kernel
    rw [ha]
    exact (canonical29135 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2076 + difference 4 2) (sourceB2076 + difference 2 4) sourceC2076) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2295) := by
    have ha : (tripleCharges (sourceA2076 + difference 4 2) (sourceB2076 + difference 2 4) sourceC2076) = raw29136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2076 sourceB2076 sourceC2076 difference raw29136; decide +kernel
    rw [ha]
    exact (canonical29136 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2076 + difference 4 3) (sourceB2076 + difference 3 4) sourceC2076) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2309) := by
    have ha : (tripleCharges (sourceA2076 + difference 4 3) (sourceB2076 + difference 3 4) sourceC2076) = raw29132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2076 sourceB2076 sourceC2076 difference raw29132; decide +kernel
    rw [ha]
    exact (canonical29132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2076 + difference 4 4) (sourceB2076 + difference 4 4) sourceC2076) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA2076 + difference 4 4) (sourceB2076 + difference 4 4) sourceC2076) = raw29123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2076 sourceB2076 sourceC2076 difference raw29123; decide +kernel
    rw [ha]
    exact (canonical29123 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2076 + difference 4 5) (sourceB2076 + difference 5 4) sourceC2076) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA2076 + difference 4 5) (sourceB2076 + difference 5 4) sourceC2076) = raw29137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2076 sourceB2076 sourceC2076 difference raw29137; decide +kernel
    rw [ha]
    exact (canonical29137 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2076 + sourceB2076) sourceC2076) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2076 + sourceB2076) sourceC2076) = raw29129 := by
      apply Matrix.ext; unfold doubleCharges sourceA2076 sourceB2076 sourceC2076 raw29129; decide +kernel
    rw [ha]
    exact (canonical29129 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2076 sourceB2076 sourceC2076
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2076, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2077 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2077 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC2077 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceForm2077 : Integer.Sparse Master := [(Sum.inr 2385, 1), (Sum.inr 2459, 1), (Sum.inr 2468, 1), (Sum.inr 2505, 1), (Sum.inr 2705, 1), (Sum.inr 3766, 1), (Sum.inr 4088, -1)]

theorem sourceEq2077 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2077 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2077 + difference 0 5) (sourceB2077 + difference 5 0) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2077 + difference 0 5) (sourceB2077 + difference 5 0) sourceC2077) = raw29128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29128; decide +kernel
    rw [ha]
    exact (canonical29128 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2077 + difference 1 5) (sourceB2077 + difference 5 1) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2077 + difference 1 5) (sourceB2077 + difference 5 1) sourceC2077) = raw29138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29138; decide +kernel
    rw [ha]
    exact (canonical29138 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2077 + difference 2 5) (sourceB2077 + difference 5 2) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2077 + difference 2 5) (sourceB2077 + difference 5 2) sourceC2077) = raw29139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29139; decide +kernel
    rw [ha]
    exact (canonical29139 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2077 + difference 3 5) (sourceB2077 + difference 5 3) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA2077 + difference 3 5) (sourceB2077 + difference 5 3) sourceC2077) = raw29140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29140; decide +kernel
    rw [ha]
    exact (canonical29140 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2077 + difference 4 5) (sourceB2077 + difference 5 4) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA2077 + difference 4 5) (sourceB2077 + difference 5 4) sourceC2077) = raw29137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29137; decide +kernel
    rw [ha]
    exact (canonical29137 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2077 + difference 5 5) (sourceB2077 + difference 5 5) sourceC2077) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA2077 + difference 5 5) (sourceB2077 + difference 5 5) sourceC2077) = raw29123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2077 sourceB2077 sourceC2077 difference raw29123; decide +kernel
    rw [ha]
    exact (canonical29123 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2077 + sourceB2077) sourceC2077) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2077 + sourceB2077) sourceC2077) = raw29129 := by
      apply Matrix.ext; unfold doubleCharges sourceA2077 sourceB2077 sourceC2077 raw29129; decide +kernel
    rw [ha]
    exact (canonical29129 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2077 sourceB2077 sourceC2077
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2077, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2078 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB2078 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceC2078 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2078 : Integer.Sparse Master := [(Sum.inr 1772, 1), (Sum.inr 1864, 1), (Sum.inr 1873, 1), (Sum.inr 1953, 1), (Sum.inr 2006, 1), (Sum.inr 3353, 1), (Sum.inr 4081, -1)]

theorem sourceEq2078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2078 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2078 + difference 0 0) (sourceB2078 + difference 0 0) sourceC2078) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3353) := by
    have ha : (tripleCharges (sourceA2078 + difference 0 0) (sourceB2078 + difference 0 0) sourceC2078) = raw29141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2078 sourceB2078 sourceC2078 difference raw29141; decide +kernel
    rw [ha]
    exact (canonical29141 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2078 + difference 1 0) (sourceB2078 + difference 0 1) sourceC2078) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2006) := by
    have ha : (tripleCharges (sourceA2078 + difference 1 0) (sourceB2078 + difference 0 1) sourceC2078) = raw29142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2078 sourceB2078 sourceC2078 difference raw29142; decide +kernel
    rw [ha]
    exact (canonical29142 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2078 + difference 2 0) (sourceB2078 + difference 0 2) sourceC2078) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1864) := by
    have ha : (tripleCharges (sourceA2078 + difference 2 0) (sourceB2078 + difference 0 2) sourceC2078) = raw29042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2078 sourceB2078 sourceC2078 difference raw29042; decide +kernel
    rw [ha]
    exact (canonical29042 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2078 + difference 3 0) (sourceB2078 + difference 0 3) sourceC2078) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1953) := by
    have ha : (tripleCharges (sourceA2078 + difference 3 0) (sourceB2078 + difference 0 3) sourceC2078) = raw29143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2078 sourceB2078 sourceC2078 difference raw29143; decide +kernel
    rw [ha]
    exact (canonical29143 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2078 + difference 4 0) (sourceB2078 + difference 0 4) sourceC2078) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1873) := by
    have ha : (tripleCharges (sourceA2078 + difference 4 0) (sourceB2078 + difference 0 4) sourceC2078) = raw29144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2078 sourceB2078 sourceC2078 difference raw29144; decide +kernel
    rw [ha]
    exact (canonical29144 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2078 + difference 5 0) (sourceB2078 + difference 0 5) sourceC2078) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1772) := by
    have ha : (tripleCharges (sourceA2078 + difference 5 0) (sourceB2078 + difference 0 5) sourceC2078) = raw29145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2078 sourceB2078 sourceC2078 difference raw29145; decide +kernel
    rw [ha]
    exact (canonical29145 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2078 + sourceB2078) sourceC2078) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA2078 + sourceB2078) sourceC2078) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2078 sourceB2078 sourceC2078 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2078 sourceB2078 sourceC2078
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2078, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2079 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2079 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2079 : Charge := ![2, 1, 0, 1, -1, -3]
def sourceForm2079 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4287, 1), (Sum.inr 4293, 1), (Sum.inr 4295, 1), (Sum.inr 4308, 1), (Sum.inr 4401, 1), (Sum.inr 4521, 1), (Sum.inr 4525, 1), (Sum.inr 4538, 1), (Sum.inr 4583, 1), (Sum.inr 4631, 1), (Sum.inr 4637, 1), (Sum.inr 4649, 1), (Sum.inr 4706, 1), (Sum.inr 4712, 1), (Sum.inr 4721, 1), (Sum.inr 4726, 1), (Sum.inr 4728, 1), (Sum.inr 4736, 1), (Sum.inr 4741, 1), (Sum.inr 4745, 1), (Sum.inr 4779, 1), (Sum.inr 4827, 1), (Sum.inr 4832, 1), (Sum.inr 4834, 1), (Sum.inr 5014, 1), (Sum.inr 5055, 1), (Sum.inr 5094, 1), (Sum.inr 5099, 1), (Sum.inr 5101, 1)]

theorem sourceEq2079 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2079 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 1) (sourceB2079 + difference 1 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 1) (sourceB2079 + difference 1 0) sourceC2079) = raw29146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29146; decide +kernel
    rw [ha]
    exact (canonical29146 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 2) (sourceB2079 + difference 2 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 2) (sourceB2079 + difference 2 0) sourceC2079) = raw29147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29147; decide +kernel
    rw [ha]
    exact (canonical29147 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 3) (sourceB2079 + difference 3 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 3) (sourceB2079 + difference 3 0) sourceC2079) = raw29148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29148; decide +kernel
    rw [ha]
    exact (canonical29148 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 4) (sourceB2079 + difference 4 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 4) (sourceB2079 + difference 4 0) sourceC2079) = raw29149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29149; decide +kernel
    rw [ha]
    exact (canonical29149 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 5) (sourceB2079 + difference 5 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 5) (sourceB2079 + difference 5 0) sourceC2079) = raw29150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29150; decide +kernel
    rw [ha]
    exact (canonical29150 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 0) (sourceB2079 + difference 0 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 0) (sourceB2079 + difference 0 1) sourceC2079) = raw29151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29151; decide +kernel
    rw [ha]
    exact (canonical29151 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 2) (sourceB2079 + difference 2 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 2) (sourceB2079 + difference 2 1) sourceC2079) = raw29152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29152; decide +kernel
    rw [ha]
    exact (canonical29152 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 3) (sourceB2079 + difference 3 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 3) (sourceB2079 + difference 3 1) sourceC2079) = raw29153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29153; decide +kernel
    rw [ha]
    exact (canonical29153 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 4) (sourceB2079 + difference 4 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 4) (sourceB2079 + difference 4 1) sourceC2079) = raw29154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29154; decide +kernel
    rw [ha]
    exact (canonical29154 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 5) (sourceB2079 + difference 5 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 5) (sourceB2079 + difference 5 1) sourceC2079) = raw29155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29155; decide +kernel
    rw [ha]
    exact (canonical29155 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 0) (sourceB2079 + difference 0 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 0) (sourceB2079 + difference 0 2) sourceC2079) = raw29156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29156; decide +kernel
    rw [ha]
    exact (canonical29156 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 1) (sourceB2079 + difference 1 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 1) (sourceB2079 + difference 1 2) sourceC2079) = raw29157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29157; decide +kernel
    rw [ha]
    exact (canonical29157 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 3) (sourceB2079 + difference 3 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4712) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 3) (sourceB2079 + difference 3 2) sourceC2079) = raw29158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29158; decide +kernel
    rw [ha]
    exact (canonical29158 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 4) (sourceB2079 + difference 4 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 4) (sourceB2079 + difference 4 2) sourceC2079) = raw29159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29159; decide +kernel
    rw [ha]
    exact (canonical29159 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 5) (sourceB2079 + difference 5 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 5) (sourceB2079 + difference 5 2) sourceC2079) = raw29160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29160; decide +kernel
    rw [ha]
    exact (canonical29160 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 0) (sourceB2079 + difference 0 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 0) (sourceB2079 + difference 0 3) sourceC2079) = raw29161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29161; decide +kernel
    rw [ha]
    exact (canonical29161 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 1) (sourceB2079 + difference 1 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 1) (sourceB2079 + difference 1 3) sourceC2079) = raw29162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29162; decide +kernel
    rw [ha]
    exact (canonical29162 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 2) (sourceB2079 + difference 2 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4721) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 2) (sourceB2079 + difference 2 3) sourceC2079) = raw29163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29163; decide +kernel
    rw [ha]
    exact (canonical29163 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 4) (sourceB2079 + difference 4 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 4) (sourceB2079 + difference 4 3) sourceC2079) = raw29164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29164; decide +kernel
    rw [ha]
    exact (canonical29164 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 5) (sourceB2079 + difference 5 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 5) (sourceB2079 + difference 5 3) sourceC2079) = raw29165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29165; decide +kernel
    rw [ha]
    exact (canonical29165 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 0) (sourceB2079 + difference 0 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 0) (sourceB2079 + difference 0 4) sourceC2079) = raw29166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29166; decide +kernel
    rw [ha]
    exact (canonical29166 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 1) (sourceB2079 + difference 1 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 1) (sourceB2079 + difference 1 4) sourceC2079) = raw29167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29167; decide +kernel
    rw [ha]
    exact (canonical29167 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 2) (sourceB2079 + difference 2 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4631) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 2) (sourceB2079 + difference 2 4) sourceC2079) = raw29168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29168; decide +kernel
    rw [ha]
    exact (canonical29168 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 3) (sourceB2079 + difference 3 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4649) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 3) (sourceB2079 + difference 3 4) sourceC2079) = raw29169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29169; decide +kernel
    rw [ha]
    exact (canonical29169 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 5) (sourceB2079 + difference 5 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 5) (sourceB2079 + difference 5 4) sourceC2079) = raw29170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29170; decide +kernel
    rw [ha]
    exact (canonical29170 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 0) (sourceB2079 + difference 0 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 0) (sourceB2079 + difference 0 5) sourceC2079) = raw29171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29171; decide +kernel
    rw [ha]
    exact (canonical29171 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 1) (sourceB2079 + difference 1 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 1) (sourceB2079 + difference 1 5) sourceC2079) = raw29172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29172; decide +kernel
    rw [ha]
    exact (canonical29172 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 2) (sourceB2079 + difference 2 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4287) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 2) (sourceB2079 + difference 2 5) sourceC2079) = raw29173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29173; decide +kernel
    rw [ha]
    exact (canonical29173 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 3) (sourceB2079 + difference 3 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4308) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 3) (sourceB2079 + difference 3 5) sourceC2079) = raw29174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29174; decide +kernel
    rw [ha]
    exact (canonical29174 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 4) (sourceB2079 + difference 4 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 4) (sourceB2079 + difference 4 5) sourceC2079) = raw29175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29175; decide +kernel
    rw [ha]
    exact (canonical29175 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2079 sourceB2079 sourceC2079
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2079, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
