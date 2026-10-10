import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical139
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical219
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical220

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1952 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1952 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1952 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceForm1952 : Integer.Sparse Master := [(Sum.inr 4353, 2), (Sum.inr 4358, 1), (Sum.inr 4362, 1), (Sum.inr 4367, 2), (Sum.inr 4374, 1), (Sum.inr 4463, 1), (Sum.inr 4464, 1), (Sum.inr 4699, 2), (Sum.inr 4705, 1), (Sum.inr 4772, 2), (Sum.inr 4777, 2), (Sum.inr 4807, 2), (Sum.inr 4853, 2), (Sum.inr 4866, 2), (Sum.inr 4875, 1), (Sum.inr 4890, 1), (Sum.inr 4895, 1), (Sum.inr 5173, 2), (Sum.inr 5175, 1), (Sum.inr 5295, 1), (Sum.inr 5304, 1)]

theorem sourceEq1952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1952 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 1) (sourceB1952 + difference 1 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 1) (sourceB1952 + difference 1 0) sourceC1952) = raw27688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27688; decide +kernel
    rw [ha]
    exact (canonical27688 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 2) (sourceB1952 + difference 2 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 2) (sourceB1952 + difference 2 0) sourceC1952) = raw27689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27689; decide +kernel
    rw [ha]
    exact (canonical27689 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 3) (sourceB1952 + difference 3 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 3) (sourceB1952 + difference 3 0) sourceC1952) = raw27690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27690; decide +kernel
    rw [ha]
    exact (canonical27690 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 4) (sourceB1952 + difference 4 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 4) (sourceB1952 + difference 4 0) sourceC1952) = raw27691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27691; decide +kernel
    rw [ha]
    exact (canonical27691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1952 + difference 0 5) (sourceB1952 + difference 5 0) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA1952 + difference 0 5) (sourceB1952 + difference 5 0) sourceC1952) = raw27692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27692; decide +kernel
    rw [ha]
    exact (canonical27692 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 0) (sourceB1952 + difference 0 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 0) (sourceB1952 + difference 0 1) sourceC1952) = raw27693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27693; decide +kernel
    rw [ha]
    exact (canonical27693 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 2) (sourceB1952 + difference 2 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 2) (sourceB1952 + difference 2 1) sourceC1952) = raw27694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27694; decide +kernel
    rw [ha]
    exact (canonical27694 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 3) (sourceB1952 + difference 3 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 3) (sourceB1952 + difference 3 1) sourceC1952) = raw27695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27695; decide +kernel
    rw [ha]
    exact (canonical27695 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 4) (sourceB1952 + difference 4 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 4) (sourceB1952 + difference 4 1) sourceC1952) = raw27696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27696; decide +kernel
    rw [ha]
    exact (canonical27696 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1952 + difference 1 5) (sourceB1952 + difference 5 1) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA1952 + difference 1 5) (sourceB1952 + difference 5 1) sourceC1952) = raw27697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27697; decide +kernel
    rw [ha]
    exact (canonical27697 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 0) (sourceB1952 + difference 0 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4353) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 0) (sourceB1952 + difference 0 2) sourceC1952) = raw27698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27698; decide +kernel
    rw [ha]
    exact (canonical27698 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 1) (sourceB1952 + difference 1 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 1) (sourceB1952 + difference 1 2) sourceC1952) = raw27699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27699; decide +kernel
    rw [ha]
    exact (canonical27699 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 3) (sourceB1952 + difference 3 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4772) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 3) (sourceB1952 + difference 3 2) sourceC1952) = raw27700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27700; decide +kernel
    rw [ha]
    exact (canonical27700 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 4) (sourceB1952 + difference 4 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 4) (sourceB1952 + difference 4 2) sourceC1952) = raw27701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27701; decide +kernel
    rw [ha]
    exact (canonical27701 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1952 + difference 2 5) (sourceB1952 + difference 5 2) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA1952 + difference 2 5) (sourceB1952 + difference 5 2) sourceC1952) = raw27702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27702; decide +kernel
    rw [ha]
    exact (canonical27702 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 0) (sourceB1952 + difference 0 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4353) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 0) (sourceB1952 + difference 0 3) sourceC1952) = raw27703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27703; decide +kernel
    rw [ha]
    exact (canonical27703 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 1) (sourceB1952 + difference 1 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 1) (sourceB1952 + difference 1 3) sourceC1952) = raw27704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27704; decide +kernel
    rw [ha]
    exact (canonical27704 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 2) (sourceB1952 + difference 2 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4772) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 2) (sourceB1952 + difference 2 3) sourceC1952) = raw27705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27705; decide +kernel
    rw [ha]
    exact (canonical27705 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 4) (sourceB1952 + difference 4 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 4) (sourceB1952 + difference 4 3) sourceC1952) = raw27706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27706; decide +kernel
    rw [ha]
    exact (canonical27706 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1952 + difference 3 5) (sourceB1952 + difference 5 3) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA1952 + difference 3 5) (sourceB1952 + difference 5 3) sourceC1952) = raw27707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27707; decide +kernel
    rw [ha]
    exact (canonical27707 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 0) (sourceB1952 + difference 0 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4362) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 0) (sourceB1952 + difference 0 4) sourceC1952) = raw27708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27708; decide +kernel
    rw [ha]
    exact (canonical27708 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 1) (sourceB1952 + difference 1 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 1) (sourceB1952 + difference 1 4) sourceC1952) = raw27709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27709; decide +kernel
    rw [ha]
    exact (canonical27709 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 2) (sourceB1952 + difference 2 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 2) (sourceB1952 + difference 2 4) sourceC1952) = raw27710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27710; decide +kernel
    rw [ha]
    exact (canonical27710 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 3) (sourceB1952 + difference 3 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 3) (sourceB1952 + difference 3 4) sourceC1952) = raw27711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27711; decide +kernel
    rw [ha]
    exact (canonical27711 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1952 + difference 4 5) (sourceB1952 + difference 5 4) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA1952 + difference 4 5) (sourceB1952 + difference 5 4) sourceC1952) = raw27712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27712; decide +kernel
    rw [ha]
    exact (canonical27712 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 0) (sourceB1952 + difference 0 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4358) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 0) (sourceB1952 + difference 0 5) sourceC1952) = raw27713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27713; decide +kernel
    rw [ha]
    exact (canonical27713 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 1) (sourceB1952 + difference 1 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 1) (sourceB1952 + difference 1 5) sourceC1952) = raw27714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27714; decide +kernel
    rw [ha]
    exact (canonical27714 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 2) (sourceB1952 + difference 2 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 2) (sourceB1952 + difference 2 5) sourceC1952) = raw27715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27715; decide +kernel
    rw [ha]
    exact (canonical27715 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 3) (sourceB1952 + difference 3 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 3) (sourceB1952 + difference 3 5) sourceC1952) = raw27716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27716; decide +kernel
    rw [ha]
    exact (canonical27716 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1952 + difference 5 4) (sourceB1952 + difference 4 5) sourceC1952) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1952 + difference 5 4) (sourceB1952 + difference 4 5) sourceC1952) = raw27717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1952 sourceB1952 sourceC1952 difference raw27717; decide +kernel
    rw [ha]
    exact (canonical27717 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1952 sourceB1952 sourceC1952
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1952, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1953 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1953 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1953 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceForm1953 : Integer.Sparse Master := [(Sum.inr 1686, 2), (Sum.inr 1687, 1), (Sum.inr 1695, 1), (Sum.inr 1720, 2), (Sum.inr 1745, 1), (Sum.inr 1748, 1), (Sum.inr 1750, 1), (Sum.inr 2198, 2), (Sum.inr 2223, 2), (Sum.inr 2224, 2), (Sum.inr 2256, 2), (Sum.inr 2259, 2), (Sum.inr 2260, 2), (Sum.inr 2286, 1), (Sum.inr 2288, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 1), (Sum.inr 2735, 2), (Sum.inr 2761, 1), (Sum.inr 2781, 1), (Sum.inr 2782, 1)]

theorem sourceEq1953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1953 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 1) (sourceB1953 + difference 1 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 1) (sourceB1953 + difference 1 0) sourceC1953) = raw27718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27718; decide +kernel
    rw [ha]
    exact (canonical27718 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 2) (sourceB1953 + difference 2 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 2) (sourceB1953 + difference 2 0) sourceC1953) = raw27719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27719; decide +kernel
    rw [ha]
    exact (canonical27719 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 3) (sourceB1953 + difference 3 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 3) (sourceB1953 + difference 3 0) sourceC1953) = raw27720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27720; decide +kernel
    rw [ha]
    exact (canonical27720 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 4) (sourceB1953 + difference 4 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 4) (sourceB1953 + difference 4 0) sourceC1953) = raw27721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27721; decide +kernel
    rw [ha]
    exact (canonical27721 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1953 + difference 0 5) (sourceB1953 + difference 5 0) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA1953 + difference 0 5) (sourceB1953 + difference 5 0) sourceC1953) = raw27722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27722; decide +kernel
    rw [ha]
    exact (canonical27722 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 0) (sourceB1953 + difference 0 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 0) (sourceB1953 + difference 0 1) sourceC1953) = raw27723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27723; decide +kernel
    rw [ha]
    exact (canonical27723 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 2) (sourceB1953 + difference 2 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 2) (sourceB1953 + difference 2 1) sourceC1953) = raw27724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27724; decide +kernel
    rw [ha]
    exact (canonical27724 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 3) (sourceB1953 + difference 3 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 3) (sourceB1953 + difference 3 1) sourceC1953) = raw27725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27725; decide +kernel
    rw [ha]
    exact (canonical27725 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 4) (sourceB1953 + difference 4 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 4) (sourceB1953 + difference 4 1) sourceC1953) = raw27726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27726; decide +kernel
    rw [ha]
    exact (canonical27726 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1953 + difference 1 5) (sourceB1953 + difference 5 1) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA1953 + difference 1 5) (sourceB1953 + difference 5 1) sourceC1953) = raw27727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27727; decide +kernel
    rw [ha]
    exact (canonical27727 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 0) (sourceB1953 + difference 0 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 0) (sourceB1953 + difference 0 2) sourceC1953) = raw27728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27728; decide +kernel
    rw [ha]
    exact (canonical27728 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 1) (sourceB1953 + difference 1 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 1) (sourceB1953 + difference 1 2) sourceC1953) = raw27729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27729; decide +kernel
    rw [ha]
    exact (canonical27729 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 3) (sourceB1953 + difference 3 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 3) (sourceB1953 + difference 3 2) sourceC1953) = raw27730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27730; decide +kernel
    rw [ha]
    exact (canonical27730 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 4) (sourceB1953 + difference 4 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 4) (sourceB1953 + difference 4 2) sourceC1953) = raw27731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27731; decide +kernel
    rw [ha]
    exact (canonical27731 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1953 + difference 2 5) (sourceB1953 + difference 5 2) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1953 + difference 2 5) (sourceB1953 + difference 5 2) sourceC1953) = raw27732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27732; decide +kernel
    rw [ha]
    exact (canonical27732 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 0) (sourceB1953 + difference 0 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 0) (sourceB1953 + difference 0 3) sourceC1953) = raw27733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27733; decide +kernel
    rw [ha]
    exact (canonical27733 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 1) (sourceB1953 + difference 1 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 1) (sourceB1953 + difference 1 3) sourceC1953) = raw27734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27734; decide +kernel
    rw [ha]
    exact (canonical27734 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 2) (sourceB1953 + difference 2 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 2) (sourceB1953 + difference 2 3) sourceC1953) = raw27735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27735; decide +kernel
    rw [ha]
    exact (canonical27735 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 4) (sourceB1953 + difference 4 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 4) (sourceB1953 + difference 4 3) sourceC1953) = raw27736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27736; decide +kernel
    rw [ha]
    exact (canonical27736 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1953 + difference 3 5) (sourceB1953 + difference 5 3) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1953 + difference 3 5) (sourceB1953 + difference 5 3) sourceC1953) = raw27737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27737; decide +kernel
    rw [ha]
    exact (canonical27737 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 0) (sourceB1953 + difference 0 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 0) (sourceB1953 + difference 0 4) sourceC1953) = raw27738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27738; decide +kernel
    rw [ha]
    exact (canonical27738 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 1) (sourceB1953 + difference 1 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 1) (sourceB1953 + difference 1 4) sourceC1953) = raw27739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27739; decide +kernel
    rw [ha]
    exact (canonical27739 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 2) (sourceB1953 + difference 2 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 2) (sourceB1953 + difference 2 4) sourceC1953) = raw27740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27740; decide +kernel
    rw [ha]
    exact (canonical27740 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 3) (sourceB1953 + difference 3 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 3) (sourceB1953 + difference 3 4) sourceC1953) = raw27741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27741; decide +kernel
    rw [ha]
    exact (canonical27741 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1953 + difference 4 5) (sourceB1953 + difference 5 4) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA1953 + difference 4 5) (sourceB1953 + difference 5 4) sourceC1953) = raw27742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27742; decide +kernel
    rw [ha]
    exact (canonical27742 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 0) (sourceB1953 + difference 0 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 0) (sourceB1953 + difference 0 5) sourceC1953) = raw27743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27743; decide +kernel
    rw [ha]
    exact (canonical27743 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 1) (sourceB1953 + difference 1 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 1) (sourceB1953 + difference 1 5) sourceC1953) = raw27744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27744; decide +kernel
    rw [ha]
    exact (canonical27744 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 2) (sourceB1953 + difference 2 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 2) (sourceB1953 + difference 2 5) sourceC1953) = raw27745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27745; decide +kernel
    rw [ha]
    exact (canonical27745 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 3) (sourceB1953 + difference 3 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 3) (sourceB1953 + difference 3 5) sourceC1953) = raw27746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27746; decide +kernel
    rw [ha]
    exact (canonical27746 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1953 + difference 5 4) (sourceB1953 + difference 4 5) sourceC1953) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1953 + difference 5 4) (sourceB1953 + difference 4 5) sourceC1953) = raw27747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1953 sourceB1953 sourceC1953 difference raw27747; decide +kernel
    rw [ha]
    exact (canonical27747 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1953 sourceB1953 sourceC1953
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1953, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1954 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1954 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1954 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceForm1954 : Integer.Sparse Master := [(Sum.inr 953, 1), (Sum.inr 1831, 1), (Sum.inr 1979, 2), (Sum.inr 2112, 1), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

theorem sourceEq1954 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1954 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1954 + difference 0 1) (sourceB1954 + difference 1 0) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA1954 + difference 0 1) (sourceB1954 + difference 1 0) sourceC1954) = raw27748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27748; decide +kernel
    rw [ha]
    exact (canonical27748 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1954 + difference 1 1) (sourceB1954 + difference 1 1) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1954 + difference 1 1) (sourceB1954 + difference 1 1) sourceC1954) = raw27749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27749; decide +kernel
    rw [ha]
    exact (canonical27749 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1954 + difference 2 1) (sourceB1954 + difference 1 2) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1979) := by
    have ha : (tripleCharges (sourceA1954 + difference 2 1) (sourceB1954 + difference 1 2) sourceC1954) = raw27750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27750; decide +kernel
    rw [ha]
    exact (canonical27750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1954 + difference 3 1) (sourceB1954 + difference 1 3) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1979) := by
    have ha : (tripleCharges (sourceA1954 + difference 3 1) (sourceB1954 + difference 1 3) sourceC1954) = raw27751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27751; decide +kernel
    rw [ha]
    exact (canonical27751 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1954 + difference 4 1) (sourceB1954 + difference 1 4) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1831) := by
    have ha : (tripleCharges (sourceA1954 + difference 4 1) (sourceB1954 + difference 1 4) sourceC1954) = raw27752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27752; decide +kernel
    rw [ha]
    exact (canonical27752 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1954 + difference 5 1) (sourceB1954 + difference 1 5) sourceC1954) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 953) := by
    have ha : (tripleCharges (sourceA1954 + difference 5 1) (sourceB1954 + difference 1 5) sourceC1954) = raw27753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1954 sourceB1954 sourceC1954 difference raw27753; decide +kernel
    rw [ha]
    exact (canonical27753 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1954 + sourceB1954) sourceC1954) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1954 + sourceB1954) sourceC1954) = raw27754 := by
      apply Matrix.ext; unfold doubleCharges sourceA1954 sourceB1954 sourceC1954 raw27754; decide +kernel
    rw [ha]
    exact (canonical27754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1954 sourceB1954 sourceC1954
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1954, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1955 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1955 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1955 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceForm1955 : Integer.Sparse Master := [(Sum.inr 1336, 1), (Sum.inr 1973, 1), (Sum.inr 1979, 1), (Sum.inr 2025, 1), (Sum.inr 2112, 1), (Sum.inr 2952, 1), (Sum.inr 4083, -1)]

theorem sourceEq1955 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1955 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 0) (sourceB1955 + difference 0 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1336) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 0) (sourceB1955 + difference 0 2) sourceC1955) = raw27755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27755; decide +kernel
    rw [ha]
    exact (canonical27755 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 1) (sourceB1955 + difference 1 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1979) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 1) (sourceB1955 + difference 1 2) sourceC1955) = raw27750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27750; decide +kernel
    rw [ha]
    exact (canonical27750 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 2) (sourceB1955 + difference 2 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 2) (sourceB1955 + difference 2 2) sourceC1955) = raw27749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27749; decide +kernel
    rw [ha]
    exact (canonical27749 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 3) (sourceB1955 + difference 3 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1973) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 3) (sourceB1955 + difference 3 2) sourceC1955) = raw27756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27756; decide +kernel
    rw [ha]
    exact (canonical27756 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 4) (sourceB1955 + difference 4 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 4) (sourceB1955 + difference 4 2) sourceC1955) = raw27757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27757; decide +kernel
    rw [ha]
    exact (canonical27757 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1955 + difference 2 5) (sourceB1955 + difference 5 2) sourceC1955) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA1955 + difference 2 5) (sourceB1955 + difference 5 2) sourceC1955) = raw27758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1955 sourceB1955 sourceC1955 difference raw27758; decide +kernel
    rw [ha]
    exact (canonical27758 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1955 + sourceB1955) sourceC1955) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1955 + sourceB1955) sourceC1955) = raw27754 := by
      apply Matrix.ext; unfold doubleCharges sourceA1955 sourceB1955 sourceC1955 raw27754; decide +kernel
    rw [ha]
    exact (canonical27754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1955 sourceB1955 sourceC1955
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1955, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1956 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB1956 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1956 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1956 : Integer.Sparse Master := [(Sum.inr 4486, 2), (Sum.inr 4490, 1), (Sum.inr 4492, 1), (Sum.inr 4504, 1), (Sum.inr 4807, 2), (Sum.inr 4808, 2), (Sum.inr 4824, 2), (Sum.inr 4827, 2), (Sum.inr 4829, 2), (Sum.inr 4840, 2), (Sum.inr 4841, 1), (Sum.inr 4843, 2), (Sum.inr 4844, 1), (Sum.inr 4853, 2), (Sum.inr 4868, 1), (Sum.inr 4872, 1), (Sum.inr 4881, 1), (Sum.inr 5109, 1), (Sum.inr 5139, 2), (Sum.inr 5174, 1)]

theorem sourceEq1956 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1956 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 1) (sourceB1956 + difference 1 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 1) (sourceB1956 + difference 1 0) sourceC1956) = raw27759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27759; decide +kernel
    rw [ha]
    exact (canonical27759 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 2) (sourceB1956 + difference 2 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 2) (sourceB1956 + difference 2 0) sourceC1956) = raw27760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27760; decide +kernel
    rw [ha]
    exact (canonical27760 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 3) (sourceB1956 + difference 3 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 3) (sourceB1956 + difference 3 0) sourceC1956) = raw27761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27761; decide +kernel
    rw [ha]
    exact (canonical27761 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 4) (sourceB1956 + difference 4 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 4) (sourceB1956 + difference 4 0) sourceC1956) = raw27642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27642; decide +kernel
    rw [ha]
    exact (canonical27642 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1956 + difference 0 5) (sourceB1956 + difference 5 0) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1956 + difference 0 5) (sourceB1956 + difference 5 0) sourceC1956) = raw27762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27762; decide +kernel
    rw [ha]
    exact (canonical27762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 0) (sourceB1956 + difference 0 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4872) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 0) (sourceB1956 + difference 0 1) sourceC1956) = raw27763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27763; decide +kernel
    rw [ha]
    exact (canonical27763 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 2) (sourceB1956 + difference 2 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4829) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 2) (sourceB1956 + difference 2 1) sourceC1956) = raw27764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27764; decide +kernel
    rw [ha]
    exact (canonical27764 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 3) (sourceB1956 + difference 3 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4829) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 3) (sourceB1956 + difference 3 1) sourceC1956) = raw27765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27765; decide +kernel
    rw [ha]
    exact (canonical27765 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 4) (sourceB1956 + difference 4 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 4) (sourceB1956 + difference 4 1) sourceC1956) = raw27647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27647; decide +kernel
    rw [ha]
    exact (canonical27647 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1956 + difference 1 5) (sourceB1956 + difference 5 1) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4492) := by
    have ha : (tripleCharges (sourceA1956 + difference 1 5) (sourceB1956 + difference 5 1) sourceC1956) = raw27766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27766; decide +kernel
    rw [ha]
    exact (canonical27766 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 0) (sourceB1956 + difference 0 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 0) (sourceB1956 + difference 0 2) sourceC1956) = raw27767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27767; decide +kernel
    rw [ha]
    exact (canonical27767 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 1) (sourceB1956 + difference 1 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 1) (sourceB1956 + difference 1 2) sourceC1956) = raw27768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27768; decide +kernel
    rw [ha]
    exact (canonical27768 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 3) (sourceB1956 + difference 3 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4824) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 3) (sourceB1956 + difference 3 2) sourceC1956) = raw27769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27769; decide +kernel
    rw [ha]
    exact (canonical27769 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 4) (sourceB1956 + difference 4 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 4) (sourceB1956 + difference 4 2) sourceC1956) = raw27652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27652; decide +kernel
    rw [ha]
    exact (canonical27652 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1956 + difference 2 5) (sourceB1956 + difference 5 2) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA1956 + difference 2 5) (sourceB1956 + difference 5 2) sourceC1956) = raw27770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27770; decide +kernel
    rw [ha]
    exact (canonical27770 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 0) (sourceB1956 + difference 0 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 0) (sourceB1956 + difference 0 3) sourceC1956) = raw27771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27771; decide +kernel
    rw [ha]
    exact (canonical27771 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 1) (sourceB1956 + difference 1 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 1) (sourceB1956 + difference 1 3) sourceC1956) = raw27772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27772; decide +kernel
    rw [ha]
    exact (canonical27772 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 2) (sourceB1956 + difference 2 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4824) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 2) (sourceB1956 + difference 2 3) sourceC1956) = raw27773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27773; decide +kernel
    rw [ha]
    exact (canonical27773 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 4) (sourceB1956 + difference 4 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 4) (sourceB1956 + difference 4 3) sourceC1956) = raw27657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27657; decide +kernel
    rw [ha]
    exact (canonical27657 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1956 + difference 3 5) (sourceB1956 + difference 5 3) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA1956 + difference 3 5) (sourceB1956 + difference 5 3) sourceC1956) = raw27774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27774; decide +kernel
    rw [ha]
    exact (canonical27774 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 0) (sourceB1956 + difference 0 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 0) (sourceB1956 + difference 0 4) sourceC1956) = raw27775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27775; decide +kernel
    rw [ha]
    exact (canonical27775 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 1) (sourceB1956 + difference 1 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 1) (sourceB1956 + difference 1 4) sourceC1956) = raw27776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27776; decide +kernel
    rw [ha]
    exact (canonical27776 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 2) (sourceB1956 + difference 2 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4840) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 2) (sourceB1956 + difference 2 4) sourceC1956) = raw27777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27777; decide +kernel
    rw [ha]
    exact (canonical27777 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 3) (sourceB1956 + difference 3 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4840) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 3) (sourceB1956 + difference 3 4) sourceC1956) = raw27778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27778; decide +kernel
    rw [ha]
    exact (canonical27778 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1956 + difference 4 5) (sourceB1956 + difference 5 4) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4504) := by
    have ha : (tripleCharges (sourceA1956 + difference 4 5) (sourceB1956 + difference 5 4) sourceC1956) = raw27779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27779; decide +kernel
    rw [ha]
    exact (canonical27779 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 0) (sourceB1956 + difference 0 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 0) (sourceB1956 + difference 0 5) sourceC1956) = raw27658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27658; decide +kernel
    rw [ha]
    exact (canonical27658 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 1) (sourceB1956 + difference 1 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 1) (sourceB1956 + difference 1 5) sourceC1956) = raw27659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27659; decide +kernel
    rw [ha]
    exact (canonical27659 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 2) (sourceB1956 + difference 2 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 2) (sourceB1956 + difference 2 5) sourceC1956) = raw27660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27660; decide +kernel
    rw [ha]
    exact (canonical27660 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 3) (sourceB1956 + difference 3 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 3) (sourceB1956 + difference 3 5) sourceC1956) = raw27661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27661; decide +kernel
    rw [ha]
    exact (canonical27661 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1956 + difference 5 4) (sourceB1956 + difference 4 5) sourceC1956) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1956 + difference 5 4) (sourceB1956 + difference 4 5) sourceC1956) = raw27780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1956 sourceB1956 sourceC1956 difference raw27780; decide +kernel
    rw [ha]
    exact (canonical27780 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1956 sourceB1956 sourceC1956
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1956, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1957 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB1957 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1957 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1957 : Integer.Sparse Master := [(Sum.inr 1639, 2), (Sum.inr 1650, 1), (Sum.inr 1651, 1), (Sum.inr 1659, 1), (Sum.inr 2025, 2), (Sum.inr 2060, 1), (Sum.inr 2062, 1), (Sum.inr 2071, 2), (Sum.inr 2079, 2), (Sum.inr 2080, 2), (Sum.inr 2090, 2), (Sum.inr 2092, 2), (Sum.inr 2109, 1), (Sum.inr 2113, 1), (Sum.inr 2121, 2), (Sum.inr 2134, 1), (Sum.inr 2136, 1), (Sum.inr 2601, 1), (Sum.inr 2618, 2), (Sum.inr 2640, 1), (Sum.inr 2642, 1)]

theorem sourceEq1957 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1957 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 1) (sourceB1957 + difference 1 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 1) (sourceB1957 + difference 1 0) sourceC1957) = raw27781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27781; decide +kernel
    rw [ha]
    exact (canonical27781 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 2) (sourceB1957 + difference 2 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 2) (sourceB1957 + difference 2 0) sourceC1957) = raw27782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27782; decide +kernel
    rw [ha]
    exact (canonical27782 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 3) (sourceB1957 + difference 3 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 3) (sourceB1957 + difference 3 0) sourceC1957) = raw27783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27783; decide +kernel
    rw [ha]
    exact (canonical27783 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 4) (sourceB1957 + difference 4 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 4) (sourceB1957 + difference 4 0) sourceC1957) = raw27784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27784; decide +kernel
    rw [ha]
    exact (canonical27784 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1957 + difference 0 5) (sourceB1957 + difference 5 0) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1957 + difference 0 5) (sourceB1957 + difference 5 0) sourceC1957) = raw27785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27785; decide +kernel
    rw [ha]
    exact (canonical27785 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 0) (sourceB1957 + difference 0 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 0) (sourceB1957 + difference 0 1) sourceC1957) = raw27786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27786; decide +kernel
    rw [ha]
    exact (canonical27786 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 2) (sourceB1957 + difference 2 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2080) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 2) (sourceB1957 + difference 2 1) sourceC1957) = raw27787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27787; decide +kernel
    rw [ha]
    exact (canonical27787 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 3) (sourceB1957 + difference 3 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2080) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 3) (sourceB1957 + difference 3 1) sourceC1957) = raw27788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27788; decide +kernel
    rw [ha]
    exact (canonical27788 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 4) (sourceB1957 + difference 4 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 4) (sourceB1957 + difference 4 1) sourceC1957) = raw27789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27789; decide +kernel
    rw [ha]
    exact (canonical27789 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1957 + difference 1 5) (sourceB1957 + difference 5 1) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1651) := by
    have ha : (tripleCharges (sourceA1957 + difference 1 5) (sourceB1957 + difference 5 1) sourceC1957) = raw27790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27790; decide +kernel
    rw [ha]
    exact (canonical27790 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 0) (sourceB1957 + difference 0 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 0) (sourceB1957 + difference 0 2) sourceC1957) = raw27791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27791; decide +kernel
    rw [ha]
    exact (canonical27791 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 1) (sourceB1957 + difference 1 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 1) (sourceB1957 + difference 1 2) sourceC1957) = raw27792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27792; decide +kernel
    rw [ha]
    exact (canonical27792 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 3) (sourceB1957 + difference 3 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 3) (sourceB1957 + difference 3 2) sourceC1957) = raw27793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27793; decide +kernel
    rw [ha]
    exact (canonical27793 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 4) (sourceB1957 + difference 4 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 4) (sourceB1957 + difference 4 2) sourceC1957) = raw27794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27794; decide +kernel
    rw [ha]
    exact (canonical27794 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1957 + difference 2 5) (sourceB1957 + difference 5 2) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1957 + difference 2 5) (sourceB1957 + difference 5 2) sourceC1957) = raw27795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27795; decide +kernel
    rw [ha]
    exact (canonical27795 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 0) (sourceB1957 + difference 0 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 0) (sourceB1957 + difference 0 3) sourceC1957) = raw27796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27796; decide +kernel
    rw [ha]
    exact (canonical27796 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 1) (sourceB1957 + difference 1 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 1) (sourceB1957 + difference 1 3) sourceC1957) = raw27797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27797; decide +kernel
    rw [ha]
    exact (canonical27797 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 2) (sourceB1957 + difference 2 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 2) (sourceB1957 + difference 2 3) sourceC1957) = raw27798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27798; decide +kernel
    rw [ha]
    exact (canonical27798 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 4) (sourceB1957 + difference 4 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 4) (sourceB1957 + difference 4 3) sourceC1957) = raw27799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27799; decide +kernel
    rw [ha]
    exact (canonical27799 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1957 + difference 3 5) (sourceB1957 + difference 5 3) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1957 + difference 3 5) (sourceB1957 + difference 5 3) sourceC1957) = raw27800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27800; decide +kernel
    rw [ha]
    exact (canonical27800 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 0) (sourceB1957 + difference 0 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 0) (sourceB1957 + difference 0 4) sourceC1957) = raw27801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27801; decide +kernel
    rw [ha]
    exact (canonical27801 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 1) (sourceB1957 + difference 1 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 1) (sourceB1957 + difference 1 4) sourceC1957) = raw27802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27802; decide +kernel
    rw [ha]
    exact (canonical27802 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 2) (sourceB1957 + difference 2 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 2) (sourceB1957 + difference 2 4) sourceC1957) = raw27803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27803; decide +kernel
    rw [ha]
    exact (canonical27803 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 3) (sourceB1957 + difference 3 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 3) (sourceB1957 + difference 3 4) sourceC1957) = raw27804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27804; decide +kernel
    rw [ha]
    exact (canonical27804 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1957 + difference 4 5) (sourceB1957 + difference 5 4) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA1957 + difference 4 5) (sourceB1957 + difference 5 4) sourceC1957) = raw27805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27805; decide +kernel
    rw [ha]
    exact (canonical27805 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 0) (sourceB1957 + difference 0 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2642) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 0) (sourceB1957 + difference 0 5) sourceC1957) = raw27806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27806; decide +kernel
    rw [ha]
    exact (canonical27806 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 1) (sourceB1957 + difference 1 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2640) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 1) (sourceB1957 + difference 1 5) sourceC1957) = raw27807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27807; decide +kernel
    rw [ha]
    exact (canonical27807 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 2) (sourceB1957 + difference 2 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 2) (sourceB1957 + difference 2 5) sourceC1957) = raw27808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27808; decide +kernel
    rw [ha]
    exact (canonical27808 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 3) (sourceB1957 + difference 3 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 3) (sourceB1957 + difference 3 5) sourceC1957) = raw27809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27809; decide +kernel
    rw [ha]
    exact (canonical27809 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1957 + difference 5 4) (sourceB1957 + difference 4 5) sourceC1957) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1957 + difference 5 4) (sourceB1957 + difference 4 5) sourceC1957) = raw27810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1957 sourceB1957 sourceC1957 difference raw27810; decide +kernel
    rw [ha]
    exact (canonical27810 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1957 sourceB1957 sourceC1957
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1957, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1958 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1958 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1958 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceForm1958 : Integer.Sparse Master := [(Sum.inr 1159, 1), (Sum.inr 2355, 1), (Sum.inr 2436, 1), (Sum.inr 2482, 1), (Sum.inr 2569, 1), (Sum.inr 2590, 1), (Sum.inr 4092, -1)]

theorem sourceEq1958 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1958 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 0) (sourceB1958 + difference 0 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1159) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 0) (sourceB1958 + difference 0 3) sourceC1958) = raw27811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27811; decide +kernel
    rw [ha]
    exact (canonical27811 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 1) (sourceB1958 + difference 1 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2355) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 1) (sourceB1958 + difference 1 3) sourceC1958) = raw27812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27812; decide +kernel
    rw [ha]
    exact (canonical27812 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 2) (sourceB1958 + difference 2 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2436) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 2) (sourceB1958 + difference 2 3) sourceC1958) = raw27813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27813; decide +kernel
    rw [ha]
    exact (canonical27813 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 3) (sourceB1958 + difference 3 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 3) (sourceB1958 + difference 3 3) sourceC1958) = raw27814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27814; decide +kernel
    rw [ha]
    exact (canonical27814 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 4) (sourceB1958 + difference 4 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 4) (sourceB1958 + difference 4 3) sourceC1958) = raw27815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27815; decide +kernel
    rw [ha]
    exact (canonical27815 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1958 + difference 3 5) (sourceB1958 + difference 5 3) sourceC1958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA1958 + difference 3 5) (sourceB1958 + difference 5 3) sourceC1958) = raw27816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1958 sourceB1958 sourceC1958 difference raw27816; decide +kernel
    rw [ha]
    exact (canonical27816 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1958 + sourceB1958) sourceC1958) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1958 + sourceB1958) sourceC1958) = raw24400 := by
      apply Matrix.ext; unfold doubleCharges sourceA1958 sourceB1958 sourceC1958 raw24400; decide +kernel
    rw [ha]
    exact (canonical24400 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1958 sourceB1958 sourceC1958
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1958, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1959 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1959 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1959 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm1959 : Integer.Sparse Master := [(Sum.inr 1320, 1), (Sum.inr 2815, 1), (Sum.inr 2847, 1), (Sum.inr 2865, 2), (Sum.inr 2884, 1), (Sum.inr 4091, -1)]

theorem sourceEq1959 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1959 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1959 + difference 0 3) (sourceB1959 + difference 3 0) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA1959 + difference 0 3) (sourceB1959 + difference 3 0) sourceC1959) = raw27817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27817; decide +kernel
    rw [ha]
    exact (canonical27817 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1959 + difference 1 3) (sourceB1959 + difference 3 1) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA1959 + difference 1 3) (sourceB1959 + difference 3 1) sourceC1959) = raw27818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27818; decide +kernel
    rw [ha]
    exact (canonical27818 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1959 + difference 2 3) (sourceB1959 + difference 3 2) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2847) := by
    have ha : (tripleCharges (sourceA1959 + difference 2 3) (sourceB1959 + difference 3 2) sourceC1959) = raw27819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27819; decide +kernel
    rw [ha]
    exact (canonical27819 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1959 + difference 3 3) (sourceB1959 + difference 3 3) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA1959 + difference 3 3) (sourceB1959 + difference 3 3) sourceC1959) = raw27820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27820; decide +kernel
    rw [ha]
    exact (canonical27820 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1959 + difference 4 3) (sourceB1959 + difference 3 4) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA1959 + difference 4 3) (sourceB1959 + difference 3 4) sourceC1959) = raw27821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27821; decide +kernel
    rw [ha]
    exact (canonical27821 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1959 + difference 5 3) (sourceB1959 + difference 3 5) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA1959 + difference 5 3) (sourceB1959 + difference 3 5) sourceC1959) = raw27822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27822; decide +kernel
    rw [ha]
    exact (canonical27822 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1959 + sourceB1959) sourceC1959) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1959 + sourceB1959) sourceC1959) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA1959 sourceB1959 sourceC1959 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1959 sourceB1959 sourceC1959
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1959, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1960 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1960 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1960 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm1960 : Integer.Sparse Master := [(Sum.inr 1334, 1), (Sum.inr 2797, 1), (Sum.inr 2802, 1), (Sum.inr 2815, 1), (Sum.inr 2865, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

theorem sourceEq1960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1960 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 0) (sourceB1960 + difference 0 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 0) (sourceB1960 + difference 0 4) sourceC1960) = raw27824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27824; decide +kernel
    rw [ha]
    exact (canonical27824 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 1) (sourceB1960 + difference 1 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 1) (sourceB1960 + difference 1 4) sourceC1960) = raw27825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27825; decide +kernel
    rw [ha]
    exact (canonical27825 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 2) (sourceB1960 + difference 2 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2797) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 2) (sourceB1960 + difference 2 4) sourceC1960) = raw27826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27826; decide +kernel
    rw [ha]
    exact (canonical27826 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 3) (sourceB1960 + difference 3 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 3) (sourceB1960 + difference 3 4) sourceC1960) = raw27821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27821; decide +kernel
    rw [ha]
    exact (canonical27821 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 4) (sourceB1960 + difference 4 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 4) (sourceB1960 + difference 4 4) sourceC1960) = raw27820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27820; decide +kernel
    rw [ha]
    exact (canonical27820 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 5) (sourceB1960 + difference 5 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 5) (sourceB1960 + difference 5 4) sourceC1960) = raw27827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27827; decide +kernel
    rw [ha]
    exact (canonical27827 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1960 + sourceB1960) sourceC1960) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1960 + sourceB1960) sourceC1960) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA1960 sourceB1960 sourceC1960 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1960 sourceB1960 sourceC1960
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1960, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1961 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB1961 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1961 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1961 : Integer.Sparse Master := [(Sum.inr 2018, 1), (Sum.inr 2074, 1), (Sum.inr 2081, 1), (Sum.inr 2099, 1), (Sum.inr 2203, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

theorem sourceEq1961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1961 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1961 + difference 0 0) (sourceB1961 + difference 0 0) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1961 + difference 0 0) (sourceB1961 + difference 0 0) sourceC1961) = raw27524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27524; decide +kernel
    rw [ha]
    exact (canonical27524 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1961 + difference 1 0) (sourceB1961 + difference 0 1) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2099) := by
    have ha : (tripleCharges (sourceA1961 + difference 1 0) (sourceB1961 + difference 0 1) sourceC1961) = raw27828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27828; decide +kernel
    rw [ha]
    exact (canonical27828 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1961 + difference 2 0) (sourceB1961 + difference 0 2) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2074) := by
    have ha : (tripleCharges (sourceA1961 + difference 2 0) (sourceB1961 + difference 0 2) sourceC1961) = raw27829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27829; decide +kernel
    rw [ha]
    exact (canonical27829 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1961 + difference 3 0) (sourceB1961 + difference 0 3) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2081) := by
    have ha : (tripleCharges (sourceA1961 + difference 3 0) (sourceB1961 + difference 0 3) sourceC1961) = raw27830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27830; decide +kernel
    rw [ha]
    exact (canonical27830 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1961 + difference 4 0) (sourceB1961 + difference 0 4) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1961 + difference 4 0) (sourceB1961 + difference 0 4) sourceC1961) = raw27368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27368; decide +kernel
    rw [ha]
    exact (canonical27368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1961 + difference 5 0) (sourceB1961 + difference 0 5) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1961 + difference 5 0) (sourceB1961 + difference 0 5) sourceC1961) = raw27831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27831; decide +kernel
    rw [ha]
    exact (canonical27831 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1961 + sourceB1961) sourceC1961) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1961 + sourceB1961) sourceC1961) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1961 sourceB1961 sourceC1961 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1961 sourceB1961 sourceC1961
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1961, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1962 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB1962 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1962 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1962 : Integer.Sparse Master := [(Sum.inr 2015, 1), (Sum.inr 2018, 1), (Sum.inr 2027, 1), (Sum.inr 2047, 1), (Sum.inr 2261, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

theorem sourceEq1962 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1962 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 0) (sourceB1962 + difference 0 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 0) (sourceB1962 + difference 0 5) sourceC1962) = raw27831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27831; decide +kernel
    rw [ha]
    exact (canonical27831 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 1) (sourceB1962 + difference 1 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 1) (sourceB1962 + difference 1 5) sourceC1962) = raw27832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27832; decide +kernel
    rw [ha]
    exact (canonical27832 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 2) (sourceB1962 + difference 2 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2015) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 2) (sourceB1962 + difference 2 5) sourceC1962) = raw27833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27833; decide +kernel
    rw [ha]
    exact (canonical27833 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 3) (sourceB1962 + difference 3 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 3) (sourceB1962 + difference 3 5) sourceC1962) = raw27834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27834; decide +kernel
    rw [ha]
    exact (canonical27834 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 4) (sourceB1962 + difference 4 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2027) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 4) (sourceB1962 + difference 4 5) sourceC1962) = raw27835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27835; decide +kernel
    rw [ha]
    exact (canonical27835 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 5) (sourceB1962 + difference 5 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 5) (sourceB1962 + difference 5 5) sourceC1962) = raw27524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27524; decide +kernel
    rw [ha]
    exact (canonical27524 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1962 + sourceB1962) sourceC1962) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1962 + sourceB1962) sourceC1962) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1962 sourceB1962 sourceC1962 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1962 sourceB1962 sourceC1962
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1962, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1963 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1963 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceC1963 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm1963 : Integer.Sparse Master := [(Sum.inr 4290, 1), (Sum.inr 4293, 1), (Sum.inr 4296, 1), (Sum.inr 4309, 1), (Sum.inr 4463, 1), (Sum.inr 4523, 1), (Sum.inr 4526, 1), (Sum.inr 4546, 1), (Sum.inr 4608, 1), (Sum.inr 4904, 1), (Sum.inr 4908, 1), (Sum.inr 4919, 1), (Sum.inr 4960, 1), (Sum.inr 4972, 1), (Sum.inr 5027, 1), (Sum.inr 5037, 1), (Sum.inr 5076, 1), (Sum.inr 5078, 2), (Sum.inr 5080, 1), (Sum.inr 5105, 1), (Sum.inr 5109, 1), (Sum.inr 5148, 1), (Sum.inr 5152, 1), (Sum.inr 5169, 1), (Sum.inr 5174, 1), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5296, 1), (Sum.inr 5434, 1)]

theorem sourceEq1963 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1963 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1963 + difference 0 1) (sourceB1963 + difference 1 0) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA1963 + difference 0 1) (sourceB1963 + difference 1 0) sourceC1963) = raw15035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw15035; decide +kernel
    rw [ha]
    exact (canonical15035 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1963 + difference 0 2) (sourceB1963 + difference 2 0) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA1963 + difference 0 2) (sourceB1963 + difference 2 0) sourceC1963) = raw15036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw15036; decide +kernel
    rw [ha]
    exact (canonical15036 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1963 + difference 0 3) (sourceB1963 + difference 3 0) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA1963 + difference 0 3) (sourceB1963 + difference 3 0) sourceC1963) = raw15037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw15037; decide +kernel
    rw [ha]
    exact (canonical15037 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1963 + difference 0 4) (sourceB1963 + difference 4 0) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1963 + difference 0 4) (sourceB1963 + difference 4 0) sourceC1963) = raw15038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw15038; decide +kernel
    rw [ha]
    exact (canonical15038 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1963 + difference 0 5) (sourceB1963 + difference 5 0) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1963 + difference 0 5) (sourceB1963 + difference 5 0) sourceC1963) = raw7806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw7806; decide +kernel
    rw [ha]
    exact (canonical7806 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1963 + difference 1 0) (sourceB1963 + difference 0 1) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1963 + difference 1 0) (sourceB1963 + difference 0 1) sourceC1963) = raw7831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw7831; decide +kernel
    rw [ha]
    exact (canonical7831 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1963 + difference 1 2) (sourceB1963 + difference 2 1) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1963 + difference 1 2) (sourceB1963 + difference 2 1) sourceC1963) = raw7833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw7833; decide +kernel
    rw [ha]
    exact (canonical7833 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1963 + difference 1 3) (sourceB1963 + difference 3 1) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1963 + difference 1 3) (sourceB1963 + difference 3 1) sourceC1963) = raw7834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw7834; decide +kernel
    rw [ha]
    exact (canonical7834 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1963 + difference 1 4) (sourceB1963 + difference 4 1) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1963 + difference 1 4) (sourceB1963 + difference 4 1) sourceC1963) = raw7835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw7835; decide +kernel
    rw [ha]
    exact (canonical7835 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1963 + difference 1 5) (sourceB1963 + difference 5 1) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1963 + difference 1 5) (sourceB1963 + difference 5 1) sourceC1963) = raw15022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw15022; decide +kernel
    rw [ha]
    exact (canonical15022 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1963 + difference 2 0) (sourceB1963 + difference 0 2) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4523) := by
    have ha : (tripleCharges (sourceA1963 + difference 2 0) (sourceB1963 + difference 0 2) sourceC1963) = raw20754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw20754; decide +kernel
    rw [ha]
    exact (canonical20754 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1963 + difference 2 1) (sourceB1963 + difference 1 2) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4960) := by
    have ha : (tripleCharges (sourceA1963 + difference 2 1) (sourceB1963 + difference 1 2) sourceC1963) = raw27836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27836; decide +kernel
    rw [ha]
    exact (canonical27836 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1963 + difference 2 3) (sourceB1963 + difference 3 2) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5027) := by
    have ha : (tripleCharges (sourceA1963 + difference 2 3) (sourceB1963 + difference 3 2) sourceC1963) = raw27837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27837; decide +kernel
    rw [ha]
    exact (canonical27837 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1963 + difference 2 4) (sourceB1963 + difference 4 2) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1963 + difference 2 4) (sourceB1963 + difference 4 2) sourceC1963) = raw27838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27838; decide +kernel
    rw [ha]
    exact (canonical27838 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1963 + difference 2 5) (sourceB1963 + difference 5 2) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA1963 + difference 2 5) (sourceB1963 + difference 5 2) sourceC1963) = raw7817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw7817; decide +kernel
    rw [ha]
    exact (canonical7817 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1963 + difference 3 0) (sourceB1963 + difference 0 3) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1963 + difference 3 0) (sourceB1963 + difference 0 3) sourceC1963) = raw20758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw20758; decide +kernel
    rw [ha]
    exact (canonical20758 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1963 + difference 3 1) (sourceB1963 + difference 1 3) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA1963 + difference 3 1) (sourceB1963 + difference 1 3) sourceC1963) = raw27839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27839; decide +kernel
    rw [ha]
    exact (canonical27839 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1963 + difference 3 2) (sourceB1963 + difference 2 3) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA1963 + difference 3 2) (sourceB1963 + difference 2 3) sourceC1963) = raw27840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27840; decide +kernel
    rw [ha]
    exact (canonical27840 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1963 + difference 3 4) (sourceB1963 + difference 4 3) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1963 + difference 3 4) (sourceB1963 + difference 4 3) sourceC1963) = raw27841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27841; decide +kernel
    rw [ha]
    exact (canonical27841 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1963 + difference 3 5) (sourceB1963 + difference 5 3) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1963 + difference 3 5) (sourceB1963 + difference 5 3) sourceC1963) = raw7822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw7822; decide +kernel
    rw [ha]
    exact (canonical7822 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1963 + difference 4 0) (sourceB1963 + difference 0 4) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA1963 + difference 4 0) (sourceB1963 + difference 0 4) sourceC1963) = raw20762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw20762; decide +kernel
    rw [ha]
    exact (canonical20762 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1963 + difference 4 1) (sourceB1963 + difference 1 4) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4908) := by
    have ha : (tripleCharges (sourceA1963 + difference 4 1) (sourceB1963 + difference 1 4) sourceC1963) = raw27842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27842; decide +kernel
    rw [ha]
    exact (canonical27842 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1963 + difference 4 2) (sourceB1963 + difference 2 4) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4904) := by
    have ha : (tripleCharges (sourceA1963 + difference 4 2) (sourceB1963 + difference 2 4) sourceC1963) = raw27843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27843; decide +kernel
    rw [ha]
    exact (canonical27843 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1963 + difference 4 3) (sourceB1963 + difference 3 4) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA1963 + difference 4 3) (sourceB1963 + difference 3 4) sourceC1963) = raw27844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27844; decide +kernel
    rw [ha]
    exact (canonical27844 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1963 + difference 4 5) (sourceB1963 + difference 5 4) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA1963 + difference 4 5) (sourceB1963 + difference 5 4) sourceC1963) = raw7827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw7827; decide +kernel
    rw [ha]
    exact (canonical7827 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1963 + difference 5 0) (sourceB1963 + difference 0 5) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1963 + difference 5 0) (sourceB1963 + difference 0 5) sourceC1963) = raw20766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw20766; decide +kernel
    rw [ha]
    exact (canonical20766 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1963 + difference 5 1) (sourceB1963 + difference 1 5) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA1963 + difference 5 1) (sourceB1963 + difference 1 5) sourceC1963) = raw27845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27845; decide +kernel
    rw [ha]
    exact (canonical27845 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1963 + difference 5 2) (sourceB1963 + difference 2 5) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4290) := by
    have ha : (tripleCharges (sourceA1963 + difference 5 2) (sourceB1963 + difference 2 5) sourceC1963) = raw27846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27846; decide +kernel
    rw [ha]
    exact (canonical27846 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1963 + difference 5 3) (sourceB1963 + difference 3 5) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1963 + difference 5 3) (sourceB1963 + difference 3 5) sourceC1963) = raw27847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27847; decide +kernel
    rw [ha]
    exact (canonical27847 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1963 + difference 5 4) (sourceB1963 + difference 4 5) sourceC1963) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1963 + difference 5 4) (sourceB1963 + difference 4 5) sourceC1963) = raw27848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1963 sourceB1963 sourceC1963 difference raw27848; decide +kernel
    rw [ha]
    exact (canonical27848 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1963 sourceB1963 sourceC1963
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1963, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1964 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1964 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceC1964 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm1964 : Integer.Sparse Master := [(Sum.inr 868, 1), (Sum.inr 871, 1), (Sum.inr 874, 1), (Sum.inr 887, 1), (Sum.inr 1046, 1), (Sum.inr 1107, 1), (Sum.inr 1110, 1), (Sum.inr 1131, 1), (Sum.inr 1242, 1), (Sum.inr 2297, 1), (Sum.inr 2301, 1), (Sum.inr 2310, 1), (Sum.inr 2412, 1), (Sum.inr 2416, 1), (Sum.inr 2429, 1), (Sum.inr 2434, 1), (Sum.inr 2483, 1), (Sum.inr 2485, 2), (Sum.inr 2488, 1), (Sum.inr 2515, 1), (Sum.inr 2519, 1), (Sum.inr 2601, 1), (Sum.inr 2768, 1), (Sum.inr 2770, 1), (Sum.inr 2927, 1), (Sum.inr 2931, 1), (Sum.inr 2960, 1), (Sum.inr 3102, 1), (Sum.inr 3982, 1)]

theorem sourceEq1964 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1964 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1964 + difference 0 1) (sourceB1964 + difference 1 0) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA1964 + difference 0 1) (sourceB1964 + difference 1 0) sourceC1964) = raw15057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw15057; decide +kernel
    rw [ha]
    exact (canonical15057 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1964 + difference 0 2) (sourceB1964 + difference 2 0) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA1964 + difference 0 2) (sourceB1964 + difference 2 0) sourceC1964) = raw15058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw15058; decide +kernel
    rw [ha]
    exact (canonical15058 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1964 + difference 0 3) (sourceB1964 + difference 3 0) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA1964 + difference 0 3) (sourceB1964 + difference 3 0) sourceC1964) = raw15059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw15059; decide +kernel
    rw [ha]
    exact (canonical15059 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1964 + difference 0 4) (sourceB1964 + difference 4 0) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA1964 + difference 0 4) (sourceB1964 + difference 4 0) sourceC1964) = raw15060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw15060; decide +kernel
    rw [ha]
    exact (canonical15060 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1964 + difference 0 5) (sourceB1964 + difference 5 0) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA1964 + difference 0 5) (sourceB1964 + difference 5 0) sourceC1964) = raw7836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw7836; decide +kernel
    rw [ha]
    exact (canonical7836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1964 + difference 1 0) (sourceB1964 + difference 0 1) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1964 + difference 1 0) (sourceB1964 + difference 0 1) sourceC1964) = raw7861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw7861; decide +kernel
    rw [ha]
    exact (canonical7861 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1964 + difference 1 2) (sourceB1964 + difference 2 1) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1964 + difference 1 2) (sourceB1964 + difference 2 1) sourceC1964) = raw7863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw7863; decide +kernel
    rw [ha]
    exact (canonical7863 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1964 + difference 1 3) (sourceB1964 + difference 3 1) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1964 + difference 1 3) (sourceB1964 + difference 3 1) sourceC1964) = raw7864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw7864; decide +kernel
    rw [ha]
    exact (canonical7864 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1964 + difference 1 4) (sourceB1964 + difference 4 1) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA1964 + difference 1 4) (sourceB1964 + difference 4 1) sourceC1964) = raw7865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw7865; decide +kernel
    rw [ha]
    exact (canonical7865 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1964 + difference 1 5) (sourceB1964 + difference 5 1) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA1964 + difference 1 5) (sourceB1964 + difference 5 1) sourceC1964) = raw15044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw15044; decide +kernel
    rw [ha]
    exact (canonical15044 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1964 + difference 2 0) (sourceB1964 + difference 0 2) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1107) := by
    have ha : (tripleCharges (sourceA1964 + difference 2 0) (sourceB1964 + difference 0 2) sourceC1964) = raw20775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw20775; decide +kernel
    rw [ha]
    exact (canonical20775 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1964 + difference 2 1) (sourceB1964 + difference 1 2) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2412) := by
    have ha : (tripleCharges (sourceA1964 + difference 2 1) (sourceB1964 + difference 1 2) sourceC1964) = raw27849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27849; decide +kernel
    rw [ha]
    exact (canonical27849 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1964 + difference 2 3) (sourceB1964 + difference 3 2) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2416) := by
    have ha : (tripleCharges (sourceA1964 + difference 2 3) (sourceB1964 + difference 3 2) sourceC1964) = raw27850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27850; decide +kernel
    rw [ha]
    exact (canonical27850 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1964 + difference 2 4) (sourceB1964 + difference 4 2) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1964 + difference 2 4) (sourceB1964 + difference 4 2) sourceC1964) = raw27851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27851; decide +kernel
    rw [ha]
    exact (canonical27851 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1964 + difference 2 5) (sourceB1964 + difference 5 2) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA1964 + difference 2 5) (sourceB1964 + difference 5 2) sourceC1964) = raw7847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw7847; decide +kernel
    rw [ha]
    exact (canonical7847 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1964 + difference 3 0) (sourceB1964 + difference 0 3) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1964 + difference 3 0) (sourceB1964 + difference 0 3) sourceC1964) = raw20779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw20779; decide +kernel
    rw [ha]
    exact (canonical20779 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1964 + difference 3 1) (sourceB1964 + difference 1 3) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA1964 + difference 3 1) (sourceB1964 + difference 1 3) sourceC1964) = raw27852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27852; decide +kernel
    rw [ha]
    exact (canonical27852 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1964 + difference 3 2) (sourceB1964 + difference 2 3) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA1964 + difference 3 2) (sourceB1964 + difference 2 3) sourceC1964) = raw27853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27853; decide +kernel
    rw [ha]
    exact (canonical27853 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1964 + difference 3 4) (sourceB1964 + difference 4 3) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1964 + difference 3 4) (sourceB1964 + difference 4 3) sourceC1964) = raw27854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27854; decide +kernel
    rw [ha]
    exact (canonical27854 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1964 + difference 3 5) (sourceB1964 + difference 5 3) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA1964 + difference 3 5) (sourceB1964 + difference 5 3) sourceC1964) = raw7852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw7852; decide +kernel
    rw [ha]
    exact (canonical7852 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1964 + difference 4 0) (sourceB1964 + difference 0 4) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA1964 + difference 4 0) (sourceB1964 + difference 0 4) sourceC1964) = raw20783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw20783; decide +kernel
    rw [ha]
    exact (canonical20783 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1964 + difference 4 1) (sourceB1964 + difference 1 4) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2301) := by
    have ha : (tripleCharges (sourceA1964 + difference 4 1) (sourceB1964 + difference 1 4) sourceC1964) = raw27855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27855; decide +kernel
    rw [ha]
    exact (canonical27855 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1964 + difference 4 2) (sourceB1964 + difference 2 4) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2297) := by
    have ha : (tripleCharges (sourceA1964 + difference 4 2) (sourceB1964 + difference 2 4) sourceC1964) = raw27856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27856; decide +kernel
    rw [ha]
    exact (canonical27856 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1964 + difference 4 3) (sourceB1964 + difference 3 4) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2310) := by
    have ha : (tripleCharges (sourceA1964 + difference 4 3) (sourceB1964 + difference 3 4) sourceC1964) = raw27857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27857; decide +kernel
    rw [ha]
    exact (canonical27857 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1964 + difference 4 5) (sourceB1964 + difference 5 4) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA1964 + difference 4 5) (sourceB1964 + difference 5 4) sourceC1964) = raw7857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw7857; decide +kernel
    rw [ha]
    exact (canonical7857 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1964 + difference 5 0) (sourceB1964 + difference 0 5) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1964 + difference 5 0) (sourceB1964 + difference 0 5) sourceC1964) = raw20787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw20787; decide +kernel
    rw [ha]
    exact (canonical20787 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1964 + difference 5 1) (sourceB1964 + difference 1 5) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 874) := by
    have ha : (tripleCharges (sourceA1964 + difference 5 1) (sourceB1964 + difference 1 5) sourceC1964) = raw27858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27858; decide +kernel
    rw [ha]
    exact (canonical27858 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1964 + difference 5 2) (sourceB1964 + difference 2 5) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 868) := by
    have ha : (tripleCharges (sourceA1964 + difference 5 2) (sourceB1964 + difference 2 5) sourceC1964) = raw27859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27859; decide +kernel
    rw [ha]
    exact (canonical27859 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1964 + difference 5 3) (sourceB1964 + difference 3 5) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1964 + difference 5 3) (sourceB1964 + difference 3 5) sourceC1964) = raw27860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27860; decide +kernel
    rw [ha]
    exact (canonical27860 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1964 + difference 5 4) (sourceB1964 + difference 4 5) sourceC1964) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1964 + difference 5 4) (sourceB1964 + difference 4 5) sourceC1964) = raw27861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1964 sourceB1964 sourceC1964 difference raw27861; decide +kernel
    rw [ha]
    exact (canonical27861 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1964 sourceB1964 sourceC1964
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1964, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1965 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1965 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1965 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceForm1965 : Integer.Sparse Master := [(Sum.inr 4327, 1), (Sum.inr 4330, 1), (Sum.inr 4335, 1), (Sum.inr 4347, 1), (Sum.inr 4440, 1), (Sum.inr 4528, 1), (Sum.inr 4535, 1), (Sum.inr 4551, 1), (Sum.inr 4591, 1), (Sum.inr 4930, 2), (Sum.inr 4935, 1), (Sum.inr 4944, 1), (Sum.inr 4948, 1), (Sum.inr 5034, 1), (Sum.inr 5037, 1), (Sum.inr 5065, 1), (Sum.inr 5073, 1), (Sum.inr 5078, 1), (Sum.inr 5081, 1), (Sum.inr 5104, 1), (Sum.inr 5128, 1), (Sum.inr 5139, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5170, 1), (Sum.inr 5252, 1), (Sum.inr 5259, 1), (Sum.inr 5284, 1), (Sum.inr 5410, 1)]

theorem sourceEq1965 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1965 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 1) (sourceB1965 + difference 1 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 1) (sourceB1965 + difference 1 0) sourceC1965) = raw17871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17871; decide +kernel
    rw [ha]
    exact (canonical17871 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 2) (sourceB1965 + difference 2 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 2) (sourceB1965 + difference 2 0) sourceC1965) = raw17872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17872; decide +kernel
    rw [ha]
    exact (canonical17872 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 3) (sourceB1965 + difference 3 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 3) (sourceB1965 + difference 3 0) sourceC1965) = raw17873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17873; decide +kernel
    rw [ha]
    exact (canonical17873 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 4) (sourceB1965 + difference 4 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 4) (sourceB1965 + difference 4 0) sourceC1965) = raw17874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17874; decide +kernel
    rw [ha]
    exact (canonical17874 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 5) (sourceB1965 + difference 5 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 5) (sourceB1965 + difference 5 0) sourceC1965) = raw27862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27862; decide +kernel
    rw [ha]
    exact (canonical27862 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 0) (sourceB1965 + difference 0 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 0) (sourceB1965 + difference 0 1) sourceC1965) = raw27863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27863; decide +kernel
    rw [ha]
    exact (canonical27863 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 2) (sourceB1965 + difference 2 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 2) (sourceB1965 + difference 2 1) sourceC1965) = raw27864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27864; decide +kernel
    rw [ha]
    exact (canonical27864 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 3) (sourceB1965 + difference 3 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 3) (sourceB1965 + difference 3 1) sourceC1965) = raw27865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27865; decide +kernel
    rw [ha]
    exact (canonical27865 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 4) (sourceB1965 + difference 4 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 4) (sourceB1965 + difference 4 1) sourceC1965) = raw27866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27866; decide +kernel
    rw [ha]
    exact (canonical27866 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 5) (sourceB1965 + difference 5 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 5) (sourceB1965 + difference 5 1) sourceC1965) = raw17850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17850; decide +kernel
    rw [ha]
    exact (canonical17850 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 0) (sourceB1965 + difference 0 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 0) (sourceB1965 + difference 0 2) sourceC1965) = raw27867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27867; decide +kernel
    rw [ha]
    exact (canonical27867 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 1) (sourceB1965 + difference 1 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 1) (sourceB1965 + difference 1 2) sourceC1965) = raw27868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27868; decide +kernel
    rw [ha]
    exact (canonical27868 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 3) (sourceB1965 + difference 3 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 3) (sourceB1965 + difference 3 2) sourceC1965) = raw27869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27869; decide +kernel
    rw [ha]
    exact (canonical27869 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 4) (sourceB1965 + difference 4 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 4) (sourceB1965 + difference 4 2) sourceC1965) = raw27870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27870; decide +kernel
    rw [ha]
    exact (canonical27870 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 5) (sourceB1965 + difference 5 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 5) (sourceB1965 + difference 5 2) sourceC1965) = raw17855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17855; decide +kernel
    rw [ha]
    exact (canonical17855 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 0) (sourceB1965 + difference 0 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 0) (sourceB1965 + difference 0 3) sourceC1965) = raw27871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27871; decide +kernel
    rw [ha]
    exact (canonical27871 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 1) (sourceB1965 + difference 1 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 1) (sourceB1965 + difference 1 3) sourceC1965) = raw27872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27872; decide +kernel
    rw [ha]
    exact (canonical27872 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 2) (sourceB1965 + difference 2 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 2) (sourceB1965 + difference 2 3) sourceC1965) = raw27873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27873; decide +kernel
    rw [ha]
    exact (canonical27873 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 4) (sourceB1965 + difference 4 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 4) (sourceB1965 + difference 4 3) sourceC1965) = raw27874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27874; decide +kernel
    rw [ha]
    exact (canonical27874 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 5) (sourceB1965 + difference 5 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 5) (sourceB1965 + difference 5 3) sourceC1965) = raw17860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17860; decide +kernel
    rw [ha]
    exact (canonical17860 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 0) (sourceB1965 + difference 0 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 0) (sourceB1965 + difference 0 4) sourceC1965) = raw27875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27875; decide +kernel
    rw [ha]
    exact (canonical27875 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 1) (sourceB1965 + difference 1 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 1) (sourceB1965 + difference 1 4) sourceC1965) = raw27876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27876; decide +kernel
    rw [ha]
    exact (canonical27876 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 2) (sourceB1965 + difference 2 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 2) (sourceB1965 + difference 2 4) sourceC1965) = raw27877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27877; decide +kernel
    rw [ha]
    exact (canonical27877 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 3) (sourceB1965 + difference 3 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 3) (sourceB1965 + difference 3 4) sourceC1965) = raw27878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27878; decide +kernel
    rw [ha]
    exact (canonical27878 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 5) (sourceB1965 + difference 5 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 5) (sourceB1965 + difference 5 4) sourceC1965) = raw17865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17865; decide +kernel
    rw [ha]
    exact (canonical17865 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 0) (sourceB1965 + difference 0 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 0) (sourceB1965 + difference 0 5) sourceC1965) = raw27879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27879; decide +kernel
    rw [ha]
    exact (canonical27879 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 1) (sourceB1965 + difference 1 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 1) (sourceB1965 + difference 1 5) sourceC1965) = raw27880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27880; decide +kernel
    rw [ha]
    exact (canonical27880 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 2) (sourceB1965 + difference 2 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 2) (sourceB1965 + difference 2 5) sourceC1965) = raw27881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27881; decide +kernel
    rw [ha]
    exact (canonical27881 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 3) (sourceB1965 + difference 3 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 3) (sourceB1965 + difference 3 5) sourceC1965) = raw27882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27882; decide +kernel
    rw [ha]
    exact (canonical27882 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 4) (sourceB1965 + difference 4 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 4) (sourceB1965 + difference 4 5) sourceC1965) = raw27883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27883; decide +kernel
    rw [ha]
    exact (canonical27883 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1965 sourceB1965 sourceC1965
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1965, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1966 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1966 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1966 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceForm1966 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 908, 1), (Sum.inr 913, 1), (Sum.inr 925, 1), (Sum.inr 1022, 1), (Sum.inr 1148, 1), (Sum.inr 1154, 1), (Sum.inr 1163, 1), (Sum.inr 1215, 1), (Sum.inr 2320, 1), (Sum.inr 2326, 1), (Sum.inr 2335, 1), (Sum.inr 2422, 1), (Sum.inr 2426, 1), (Sum.inr 2470, 1), (Sum.inr 2526, 1), (Sum.inr 2531, 1), (Sum.inr 2543, 1), (Sum.inr 2558, 1), (Sum.inr 2570, 1), (Sum.inr 2572, 1), (Sum.inr 2576, 1), (Sum.inr 2596, 1), (Sum.inr 2712, 1), (Sum.inr 2753, 1), (Sum.inr 2987, 1), (Sum.inr 2991, 1), (Sum.inr 3000, 1), (Sum.inr 3088, 1), (Sum.inr 3996, 1)]

theorem sourceEq1966 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1966 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1966 + difference 0 1) (sourceB1966 + difference 1 0) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2991) := by
    have ha : (tripleCharges (sourceA1966 + difference 0 1) (sourceB1966 + difference 1 0) sourceC1966) = raw27884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27884; decide +kernel
    rw [ha]
    exact (canonical27884 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1966 + difference 0 2) (sourceB1966 + difference 2 0) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2987) := by
    have ha : (tripleCharges (sourceA1966 + difference 0 2) (sourceB1966 + difference 2 0) sourceC1966) = raw27885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27885; decide +kernel
    rw [ha]
    exact (canonical27885 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1966 + difference 0 3) (sourceB1966 + difference 3 0) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3000) := by
    have ha : (tripleCharges (sourceA1966 + difference 0 3) (sourceB1966 + difference 3 0) sourceC1966) = raw27886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27886; decide +kernel
    rw [ha]
    exact (canonical27886 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1966 + difference 0 4) (sourceB1966 + difference 4 0) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA1966 + difference 0 4) (sourceB1966 + difference 4 0) sourceC1966) = raw27887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27887; decide +kernel
    rw [ha]
    exact (canonical27887 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1966 + difference 0 5) (sourceB1966 + difference 5 0) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA1966 + difference 0 5) (sourceB1966 + difference 5 0) sourceC1966) = raw27888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27888; decide +kernel
    rw [ha]
    exact (canonical27888 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1966 + difference 1 0) (sourceB1966 + difference 0 1) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA1966 + difference 1 0) (sourceB1966 + difference 0 1) sourceC1966) = raw27889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27889; decide +kernel
    rw [ha]
    exact (canonical27889 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1966 + difference 1 2) (sourceB1966 + difference 2 1) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA1966 + difference 1 2) (sourceB1966 + difference 2 1) sourceC1966) = raw27890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27890; decide +kernel
    rw [ha]
    exact (canonical27890 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1966 + difference 1 3) (sourceB1966 + difference 3 1) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA1966 + difference 1 3) (sourceB1966 + difference 3 1) sourceC1966) = raw27891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27891; decide +kernel
    rw [ha]
    exact (canonical27891 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1966 + difference 1 4) (sourceB1966 + difference 4 1) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA1966 + difference 1 4) (sourceB1966 + difference 4 1) sourceC1966) = raw27892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27892; decide +kernel
    rw [ha]
    exact (canonical27892 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1966 + difference 1 5) (sourceB1966 + difference 5 1) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA1966 + difference 1 5) (sourceB1966 + difference 5 1) sourceC1966) = raw27893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27893; decide +kernel
    rw [ha]
    exact (canonical27893 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1966 + difference 2 0) (sourceB1966 + difference 0 2) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 905) := by
    have ha : (tripleCharges (sourceA1966 + difference 2 0) (sourceB1966 + difference 0 2) sourceC1966) = raw27894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27894; decide +kernel
    rw [ha]
    exact (canonical27894 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1966 + difference 2 1) (sourceB1966 + difference 1 2) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2320) := by
    have ha : (tripleCharges (sourceA1966 + difference 2 1) (sourceB1966 + difference 1 2) sourceC1966) = raw27895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27895; decide +kernel
    rw [ha]
    exact (canonical27895 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1966 + difference 2 3) (sourceB1966 + difference 3 2) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2526) := by
    have ha : (tripleCharges (sourceA1966 + difference 2 3) (sourceB1966 + difference 3 2) sourceC1966) = raw27896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27896; decide +kernel
    rw [ha]
    exact (canonical27896 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1966 + difference 2 4) (sourceB1966 + difference 4 2) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA1966 + difference 2 4) (sourceB1966 + difference 4 2) sourceC1966) = raw27897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27897; decide +kernel
    rw [ha]
    exact (canonical27897 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1966 + difference 2 5) (sourceB1966 + difference 5 2) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2570) := by
    have ha : (tripleCharges (sourceA1966 + difference 2 5) (sourceB1966 + difference 5 2) sourceC1966) = raw27898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27898; decide +kernel
    rw [ha]
    exact (canonical27898 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1966 + difference 3 0) (sourceB1966 + difference 0 3) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1966 + difference 3 0) (sourceB1966 + difference 0 3) sourceC1966) = raw27899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27899; decide +kernel
    rw [ha]
    exact (canonical27899 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1966 + difference 3 1) (sourceB1966 + difference 1 3) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2335) := by
    have ha : (tripleCharges (sourceA1966 + difference 3 1) (sourceB1966 + difference 1 3) sourceC1966) = raw27900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27900; decide +kernel
    rw [ha]
    exact (canonical27900 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1966 + difference 3 2) (sourceB1966 + difference 2 3) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2426) := by
    have ha : (tripleCharges (sourceA1966 + difference 3 2) (sourceB1966 + difference 2 3) sourceC1966) = raw27901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27901; decide +kernel
    rw [ha]
    exact (canonical27901 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1966 + difference 3 4) (sourceB1966 + difference 4 3) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA1966 + difference 3 4) (sourceB1966 + difference 4 3) sourceC1966) = raw27902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27902; decide +kernel
    rw [ha]
    exact (canonical27902 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1966 + difference 3 5) (sourceB1966 + difference 5 3) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2596) := by
    have ha : (tripleCharges (sourceA1966 + difference 3 5) (sourceB1966 + difference 5 3) sourceC1966) = raw27903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27903; decide +kernel
    rw [ha]
    exact (canonical27903 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1966 + difference 4 0) (sourceB1966 + difference 0 4) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 913) := by
    have ha : (tripleCharges (sourceA1966 + difference 4 0) (sourceB1966 + difference 0 4) sourceC1966) = raw27904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27904; decide +kernel
    rw [ha]
    exact (canonical27904 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1966 + difference 4 1) (sourceB1966 + difference 1 4) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA1966 + difference 4 1) (sourceB1966 + difference 1 4) sourceC1966) = raw27905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27905; decide +kernel
    rw [ha]
    exact (canonical27905 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1966 + difference 4 2) (sourceB1966 + difference 2 4) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA1966 + difference 4 2) (sourceB1966 + difference 2 4) sourceC1966) = raw27906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27906; decide +kernel
    rw [ha]
    exact (canonical27906 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1966 + difference 4 3) (sourceB1966 + difference 3 4) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2531) := by
    have ha : (tripleCharges (sourceA1966 + difference 4 3) (sourceB1966 + difference 3 4) sourceC1966) = raw27907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27907; decide +kernel
    rw [ha]
    exact (canonical27907 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1966 + difference 4 5) (sourceB1966 + difference 5 4) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA1966 + difference 4 5) (sourceB1966 + difference 5 4) sourceC1966) = raw27908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27908; decide +kernel
    rw [ha]
    exact (canonical27908 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1966 + difference 5 0) (sourceB1966 + difference 0 5) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1966 + difference 5 0) (sourceB1966 + difference 0 5) sourceC1966) = raw27909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27909; decide +kernel
    rw [ha]
    exact (canonical27909 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1966 + difference 5 1) (sourceB1966 + difference 1 5) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1154) := by
    have ha : (tripleCharges (sourceA1966 + difference 5 1) (sourceB1966 + difference 1 5) sourceC1966) = raw27910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27910; decide +kernel
    rw [ha]
    exact (canonical27910 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1966 + difference 5 2) (sourceB1966 + difference 2 5) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1148) := by
    have ha : (tripleCharges (sourceA1966 + difference 5 2) (sourceB1966 + difference 2 5) sourceC1966) = raw27911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27911; decide +kernel
    rw [ha]
    exact (canonical27911 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1966 + difference 5 3) (sourceB1966 + difference 3 5) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1163) := by
    have ha : (tripleCharges (sourceA1966 + difference 5 3) (sourceB1966 + difference 3 5) sourceC1966) = raw27912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27912; decide +kernel
    rw [ha]
    exact (canonical27912 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1966 + difference 5 4) (sourceB1966 + difference 4 5) sourceC1966) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1966 + difference 5 4) (sourceB1966 + difference 4 5) sourceC1966) = raw27913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1966 sourceB1966 sourceC1966 difference raw27913; decide +kernel
    rw [ha]
    exact (canonical27913 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1966 sourceB1966 sourceC1966
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1966, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1967 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1967 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1967 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceForm1967 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1672, 1), (Sum.inr 1676, 1), (Sum.inr 1689, 1), (Sum.inr 1723, 1), (Sum.inr 3260, 1), (Sum.inr 3272, 1), (Sum.inr 3273, 1), (Sum.inr 3291, 1), (Sum.inr 3408, 2), (Sum.inr 3413, 1), (Sum.inr 3419, 1), (Sum.inr 3420, 1), (Sum.inr 3451, 1), (Sum.inr 3455, 1), (Sum.inr 3466, 1), (Sum.inr 3467, 1), (Sum.inr 3481, 1), (Sum.inr 3482, 1), (Sum.inr 3483, 1), (Sum.inr 3519, 1), (Sum.inr 3523, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3816, 1)]

theorem sourceEq1967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1967 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 1) (sourceB1967 + difference 1 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 1) (sourceB1967 + difference 1 0) sourceC1967) = raw27914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27914; decide +kernel
    rw [ha]
    exact (canonical27914 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 2) (sourceB1967 + difference 2 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 2) (sourceB1967 + difference 2 0) sourceC1967) = raw27915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27915; decide +kernel
    rw [ha]
    exact (canonical27915 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 3) (sourceB1967 + difference 3 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 3) (sourceB1967 + difference 3 0) sourceC1967) = raw27916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27916; decide +kernel
    rw [ha]
    exact (canonical27916 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 4) (sourceB1967 + difference 4 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 4) (sourceB1967 + difference 4 0) sourceC1967) = raw27917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27917; decide +kernel
    rw [ha]
    exact (canonical27917 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 5) (sourceB1967 + difference 5 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 5) (sourceB1967 + difference 5 0) sourceC1967) = raw27918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27918; decide +kernel
    rw [ha]
    exact (canonical27918 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 0) (sourceB1967 + difference 0 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 0) (sourceB1967 + difference 0 1) sourceC1967) = raw27919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27919; decide +kernel
    rw [ha]
    exact (canonical27919 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 2) (sourceB1967 + difference 2 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 2) (sourceB1967 + difference 2 1) sourceC1967) = raw27920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27920; decide +kernel
    rw [ha]
    exact (canonical27920 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 3) (sourceB1967 + difference 3 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 3) (sourceB1967 + difference 3 1) sourceC1967) = raw27921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27921; decide +kernel
    rw [ha]
    exact (canonical27921 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 4) (sourceB1967 + difference 4 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 4) (sourceB1967 + difference 4 1) sourceC1967) = raw27922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27922; decide +kernel
    rw [ha]
    exact (canonical27922 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 5) (sourceB1967 + difference 5 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 5) (sourceB1967 + difference 5 1) sourceC1967) = raw27923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27923; decide +kernel
    rw [ha]
    exact (canonical27923 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 0) (sourceB1967 + difference 0 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 0) (sourceB1967 + difference 0 2) sourceC1967) = raw27924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27924; decide +kernel
    rw [ha]
    exact (canonical27924 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 1) (sourceB1967 + difference 1 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 1) (sourceB1967 + difference 1 2) sourceC1967) = raw27925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27925; decide +kernel
    rw [ha]
    exact (canonical27925 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 3) (sourceB1967 + difference 3 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 3) (sourceB1967 + difference 3 2) sourceC1967) = raw27926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27926; decide +kernel
    rw [ha]
    exact (canonical27926 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 4) (sourceB1967 + difference 4 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 4) (sourceB1967 + difference 4 2) sourceC1967) = raw27927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27927; decide +kernel
    rw [ha]
    exact (canonical27927 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 5) (sourceB1967 + difference 5 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 5) (sourceB1967 + difference 5 2) sourceC1967) = raw27928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27928; decide +kernel
    rw [ha]
    exact (canonical27928 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 0) (sourceB1967 + difference 0 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 0) (sourceB1967 + difference 0 3) sourceC1967) = raw27929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27929; decide +kernel
    rw [ha]
    exact (canonical27929 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 1) (sourceB1967 + difference 1 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 1) (sourceB1967 + difference 1 3) sourceC1967) = raw27930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27930; decide +kernel
    rw [ha]
    exact (canonical27930 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 2) (sourceB1967 + difference 2 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 2) (sourceB1967 + difference 2 3) sourceC1967) = raw27931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27931; decide +kernel
    rw [ha]
    exact (canonical27931 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 4) (sourceB1967 + difference 4 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 4) (sourceB1967 + difference 4 3) sourceC1967) = raw27932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27932; decide +kernel
    rw [ha]
    exact (canonical27932 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 5) (sourceB1967 + difference 5 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 5) (sourceB1967 + difference 5 3) sourceC1967) = raw27933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27933; decide +kernel
    rw [ha]
    exact (canonical27933 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 0) (sourceB1967 + difference 0 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 0) (sourceB1967 + difference 0 4) sourceC1967) = raw27934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27934; decide +kernel
    rw [ha]
    exact (canonical27934 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 1) (sourceB1967 + difference 1 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 1) (sourceB1967 + difference 1 4) sourceC1967) = raw27935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27935; decide +kernel
    rw [ha]
    exact (canonical27935 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 2) (sourceB1967 + difference 2 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 2) (sourceB1967 + difference 2 4) sourceC1967) = raw27936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27936; decide +kernel
    rw [ha]
    exact (canonical27936 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 3) (sourceB1967 + difference 3 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 3) (sourceB1967 + difference 3 4) sourceC1967) = raw27937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27937; decide +kernel
    rw [ha]
    exact (canonical27937 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 5) (sourceB1967 + difference 5 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 5) (sourceB1967 + difference 5 4) sourceC1967) = raw27938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27938; decide +kernel
    rw [ha]
    exact (canonical27938 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 0) (sourceB1967 + difference 0 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 0) (sourceB1967 + difference 0 5) sourceC1967) = raw27939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27939; decide +kernel
    rw [ha]
    exact (canonical27939 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 1) (sourceB1967 + difference 1 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 1) (sourceB1967 + difference 1 5) sourceC1967) = raw27940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27940; decide +kernel
    rw [ha]
    exact (canonical27940 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 2) (sourceB1967 + difference 2 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 2) (sourceB1967 + difference 2 5) sourceC1967) = raw27941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27941; decide +kernel
    rw [ha]
    exact (canonical27941 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 3) (sourceB1967 + difference 3 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3273) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 3) (sourceB1967 + difference 3 5) sourceC1967) = raw27942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27942; decide +kernel
    rw [ha]
    exact (canonical27942 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 4) (sourceB1967 + difference 4 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 4) (sourceB1967 + difference 4 5) sourceC1967) = raw27943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27943; decide +kernel
    rw [ha]
    exact (canonical27943 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1967 sourceB1967 sourceC1967
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1967, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1968 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1968 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1968 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceForm1968 : Integer.Sparse Master := [(Sum.inr 1136, 1), (Sum.inr 2339, 1), (Sum.inr 2429, 1), (Sum.inr 2485, 2), (Sum.inr 2514, 1), (Sum.inr 4091, -1)]

theorem sourceEq1968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1968 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1968 + difference 0 3) (sourceB1968 + difference 3 0) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2514) := by
    have ha : (tripleCharges (sourceA1968 + difference 0 3) (sourceB1968 + difference 3 0) sourceC1968) = raw27944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27944; decide +kernel
    rw [ha]
    exact (canonical27944 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1968 + difference 1 3) (sourceB1968 + difference 3 1) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1968 + difference 1 3) (sourceB1968 + difference 3 1) sourceC1968) = raw27945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27945; decide +kernel
    rw [ha]
    exact (canonical27945 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1968 + difference 2 3) (sourceB1968 + difference 3 2) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA1968 + difference 2 3) (sourceB1968 + difference 3 2) sourceC1968) = raw27946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27946; decide +kernel
    rw [ha]
    exact (canonical27946 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1968 + difference 3 3) (sourceB1968 + difference 3 3) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1968 + difference 3 3) (sourceB1968 + difference 3 3) sourceC1968) = raw27947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27947; decide +kernel
    rw [ha]
    exact (canonical27947 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1968 + difference 4 3) (sourceB1968 + difference 3 4) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2339) := by
    have ha : (tripleCharges (sourceA1968 + difference 4 3) (sourceB1968 + difference 3 4) sourceC1968) = raw27948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27948; decide +kernel
    rw [ha]
    exact (canonical27948 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1968 + difference 5 3) (sourceB1968 + difference 3 5) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1968 + difference 5 3) (sourceB1968 + difference 3 5) sourceC1968) = raw27949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27949; decide +kernel
    rw [ha]
    exact (canonical27949 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1968 + sourceB1968) sourceC1968) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1968 + sourceB1968) sourceC1968) = raw27950 := by
      apply Matrix.ext; unfold doubleCharges sourceA1968 sourceB1968 sourceC1968 raw27950; decide +kernel
    rw [ha]
    exact (canonical27950 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1968 sourceB1968 sourceC1968
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1968, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1969 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB1969 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1969 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1969 : Integer.Sparse Master := [(Sum.inr 4729, 1), (Sum.inr 4741, 1), (Sum.inr 4742, 1), (Sum.inr 4747, 1), (Sum.inr 4792, 1), (Sum.inr 4804, 1), (Sum.inr 4807, 2), (Sum.inr 4817, 1), (Sum.inr 4853, 1), (Sum.inr 4992, 1), (Sum.inr 5000, 1), (Sum.inr 5001, 1), (Sum.inr 5008, 1), (Sum.inr 5047, 1), (Sum.inr 5048, 1), (Sum.inr 5052, 1), (Sum.inr 5065, 1), (Sum.inr 5075, 2), (Sum.inr 5078, 2), (Sum.inr 5087, 1), (Sum.inr 5107, 1), (Sum.inr 5109, 1), (Sum.inr 5127, 1), (Sum.inr 5128, 1), (Sum.inr 5147, 1), (Sum.inr 5171, 1), (Sum.inr 5174, 1)]

theorem sourceEq1969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1969 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 1) (sourceB1969 + difference 1 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 1) (sourceB1969 + difference 1 0) sourceC1969) = raw27951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27951; decide +kernel
    rw [ha]
    exact (canonical27951 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 2) (sourceB1969 + difference 2 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 2) (sourceB1969 + difference 2 0) sourceC1969) = raw27952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27952; decide +kernel
    rw [ha]
    exact (canonical27952 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 3) (sourceB1969 + difference 3 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 3) (sourceB1969 + difference 3 0) sourceC1969) = raw27641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27641; decide +kernel
    rw [ha]
    exact (canonical27641 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 4) (sourceB1969 + difference 4 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 4) (sourceB1969 + difference 4 0) sourceC1969) = raw27953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27953; decide +kernel
    rw [ha]
    exact (canonical27953 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 5) (sourceB1969 + difference 5 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 5) (sourceB1969 + difference 5 0) sourceC1969) = raw27954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27954; decide +kernel
    rw [ha]
    exact (canonical27954 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 0) (sourceB1969 + difference 0 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 0) (sourceB1969 + difference 0 1) sourceC1969) = raw27955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27955; decide +kernel
    rw [ha]
    exact (canonical27955 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 2) (sourceB1969 + difference 2 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5048) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 2) (sourceB1969 + difference 2 1) sourceC1969) = raw27956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27956; decide +kernel
    rw [ha]
    exact (canonical27956 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 3) (sourceB1969 + difference 3 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 3) (sourceB1969 + difference 3 1) sourceC1969) = raw27646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27646; decide +kernel
    rw [ha]
    exact (canonical27646 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 4) (sourceB1969 + difference 4 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5001) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 4) (sourceB1969 + difference 4 1) sourceC1969) = raw27957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27957; decide +kernel
    rw [ha]
    exact (canonical27957 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 5) (sourceB1969 + difference 5 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 5) (sourceB1969 + difference 5 1) sourceC1969) = raw27958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27958; decide +kernel
    rw [ha]
    exact (canonical27958 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 0) (sourceB1969 + difference 0 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 0) (sourceB1969 + difference 0 2) sourceC1969) = raw27959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27959; decide +kernel
    rw [ha]
    exact (canonical27959 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 1) (sourceB1969 + difference 1 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 1) (sourceB1969 + difference 1 2) sourceC1969) = raw27960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27960; decide +kernel
    rw [ha]
    exact (canonical27960 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 3) (sourceB1969 + difference 3 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 3) (sourceB1969 + difference 3 2) sourceC1969) = raw27651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27651; decide +kernel
    rw [ha]
    exact (canonical27651 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 4) (sourceB1969 + difference 4 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4992) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 4) (sourceB1969 + difference 4 2) sourceC1969) = raw27961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27961; decide +kernel
    rw [ha]
    exact (canonical27961 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 5) (sourceB1969 + difference 5 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 5) (sourceB1969 + difference 5 2) sourceC1969) = raw27962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27962; decide +kernel
    rw [ha]
    exact (canonical27962 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 0) (sourceB1969 + difference 0 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 0) (sourceB1969 + difference 0 3) sourceC1969) = raw27963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27963; decide +kernel
    rw [ha]
    exact (canonical27963 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 1) (sourceB1969 + difference 1 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 1) (sourceB1969 + difference 1 3) sourceC1969) = raw27964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27964; decide +kernel
    rw [ha]
    exact (canonical27964 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 2) (sourceB1969 + difference 2 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5052) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 2) (sourceB1969 + difference 2 3) sourceC1969) = raw27965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27965; decide +kernel
    rw [ha]
    exact (canonical27965 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 4) (sourceB1969 + difference 4 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5008) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 4) (sourceB1969 + difference 4 3) sourceC1969) = raw27966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27966; decide +kernel
    rw [ha]
    exact (canonical27966 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 5) (sourceB1969 + difference 5 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 5) (sourceB1969 + difference 5 3) sourceC1969) = raw27967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27967; decide +kernel
    rw [ha]
    exact (canonical27967 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 0) (sourceB1969 + difference 0 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 0) (sourceB1969 + difference 0 4) sourceC1969) = raw27653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27653; decide +kernel
    rw [ha]
    exact (canonical27653 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 1) (sourceB1969 + difference 1 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 1) (sourceB1969 + difference 1 4) sourceC1969) = raw27654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27654; decide +kernel
    rw [ha]
    exact (canonical27654 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 2) (sourceB1969 + difference 2 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 2) (sourceB1969 + difference 2 4) sourceC1969) = raw27655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27655; decide +kernel
    rw [ha]
    exact (canonical27655 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 3) (sourceB1969 + difference 3 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 3) (sourceB1969 + difference 3 4) sourceC1969) = raw27780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27780; decide +kernel
    rw [ha]
    exact (canonical27780 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 5) (sourceB1969 + difference 5 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 5) (sourceB1969 + difference 5 4) sourceC1969) = raw27657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27657; decide +kernel
    rw [ha]
    exact (canonical27657 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 0) (sourceB1969 + difference 0 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 0) (sourceB1969 + difference 0 5) sourceC1969) = raw27968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27968; decide +kernel
    rw [ha]
    exact (canonical27968 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 1) (sourceB1969 + difference 1 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 1) (sourceB1969 + difference 1 5) sourceC1969) = raw27969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27969; decide +kernel
    rw [ha]
    exact (canonical27969 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 2) (sourceB1969 + difference 2 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 2) (sourceB1969 + difference 2 5) sourceC1969) = raw27970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27970; decide +kernel
    rw [ha]
    exact (canonical27970 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 3) (sourceB1969 + difference 3 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 3) (sourceB1969 + difference 3 5) sourceC1969) = raw27667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27667; decide +kernel
    rw [ha]
    exact (canonical27667 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 4) (sourceB1969 + difference 4 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 4) (sourceB1969 + difference 4 5) sourceC1969) = raw27971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27971; decide +kernel
    rw [ha]
    exact (canonical27971 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1969 sourceB1969 sourceC1969
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1969, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1970 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB1970 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1970 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1970 : Integer.Sparse Master := [(Sum.inr 1898, 1), (Sum.inr 1914, 1), (Sum.inr 1915, 1), (Sum.inr 1926, 1), (Sum.inr 2025, 1), (Sum.inr 2378, 1), (Sum.inr 2385, 1), (Sum.inr 2386, 1), (Sum.inr 2393, 1), (Sum.inr 2449, 1), (Sum.inr 2450, 1), (Sum.inr 2454, 1), (Sum.inr 2470, 1), (Sum.inr 2471, 1), (Sum.inr 2482, 1), (Sum.inr 2485, 1), (Sum.inr 2486, 1), (Sum.inr 2495, 1), (Sum.inr 2497, 1), (Sum.inr 2517, 1), (Sum.inr 2519, 1), (Sum.inr 2543, 1), (Sum.inr 2572, 1), (Sum.inr 2574, 1), (Sum.inr 2601, 1), (Sum.inr 2865, 1), (Sum.inr 2914, 1), (Sum.inr 2939, 1), (Sum.inr 2941, 1), (Sum.inr 2965, 1)]

theorem sourceEq1970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1970 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1970 + difference 0 1) (sourceB1970 + difference 1 0) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1970 + difference 0 1) (sourceB1970 + difference 1 0) sourceC1970) = raw27972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27972; decide +kernel
    rw [ha]
    exact (canonical27972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1970 + difference 0 2) (sourceB1970 + difference 2 0) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA1970 + difference 0 2) (sourceB1970 + difference 2 0) sourceC1970) = raw27973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27973; decide +kernel
    rw [ha]
    exact (canonical27973 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1970 + difference 0 3) (sourceB1970 + difference 3 0) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2517) := by
    have ha : (tripleCharges (sourceA1970 + difference 0 3) (sourceB1970 + difference 3 0) sourceC1970) = raw27974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27974; decide +kernel
    rw [ha]
    exact (canonical27974 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1970 + difference 0 4) (sourceB1970 + difference 4 0) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA1970 + difference 0 4) (sourceB1970 + difference 4 0) sourceC1970) = raw27975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27975; decide +kernel
    rw [ha]
    exact (canonical27975 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1970 + difference 0 5) (sourceB1970 + difference 5 0) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1970 + difference 0 5) (sourceB1970 + difference 5 0) sourceC1970) = raw27976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27976; decide +kernel
    rw [ha]
    exact (canonical27976 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1970 + difference 1 0) (sourceB1970 + difference 0 1) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA1970 + difference 1 0) (sourceB1970 + difference 0 1) sourceC1970) = raw27977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27977; decide +kernel
    rw [ha]
    exact (canonical27977 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1970 + difference 1 2) (sourceB1970 + difference 2 1) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2450) := by
    have ha : (tripleCharges (sourceA1970 + difference 1 2) (sourceB1970 + difference 2 1) sourceC1970) = raw27978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27978; decide +kernel
    rw [ha]
    exact (canonical27978 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1970 + difference 1 3) (sourceB1970 + difference 3 1) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1970 + difference 1 3) (sourceB1970 + difference 3 1) sourceC1970) = raw27979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27979; decide +kernel
    rw [ha]
    exact (canonical27979 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1970 + difference 1 4) (sourceB1970 + difference 4 1) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2386) := by
    have ha : (tripleCharges (sourceA1970 + difference 1 4) (sourceB1970 + difference 4 1) sourceC1970) = raw27980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27980; decide +kernel
    rw [ha]
    exact (canonical27980 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1970 + difference 1 5) (sourceB1970 + difference 5 1) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA1970 + difference 1 5) (sourceB1970 + difference 5 1) sourceC1970) = raw27981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27981; decide +kernel
    rw [ha]
    exact (canonical27981 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1970 + difference 2 0) (sourceB1970 + difference 0 2) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA1970 + difference 2 0) (sourceB1970 + difference 0 2) sourceC1970) = raw27982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27982; decide +kernel
    rw [ha]
    exact (canonical27982 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1970 + difference 2 1) (sourceB1970 + difference 1 2) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA1970 + difference 2 1) (sourceB1970 + difference 1 2) sourceC1970) = raw27983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27983; decide +kernel
    rw [ha]
    exact (canonical27983 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1970 + difference 2 3) (sourceB1970 + difference 3 2) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1970 + difference 2 3) (sourceB1970 + difference 3 2) sourceC1970) = raw27984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27984; decide +kernel
    rw [ha]
    exact (canonical27984 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1970 + difference 2 4) (sourceB1970 + difference 4 2) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2378) := by
    have ha : (tripleCharges (sourceA1970 + difference 2 4) (sourceB1970 + difference 4 2) sourceC1970) = raw27985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27985; decide +kernel
    rw [ha]
    exact (canonical27985 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1970 + difference 2 5) (sourceB1970 + difference 5 2) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1970 + difference 2 5) (sourceB1970 + difference 5 2) sourceC1970) = raw27986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27986; decide +kernel
    rw [ha]
    exact (canonical27986 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1970 + difference 3 0) (sourceB1970 + difference 0 3) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA1970 + difference 3 0) (sourceB1970 + difference 0 3) sourceC1970) = raw27987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27987; decide +kernel
    rw [ha]
    exact (canonical27987 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1970 + difference 3 1) (sourceB1970 + difference 1 3) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA1970 + difference 3 1) (sourceB1970 + difference 1 3) sourceC1970) = raw27988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27988; decide +kernel
    rw [ha]
    exact (canonical27988 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1970 + difference 3 2) (sourceB1970 + difference 2 3) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2454) := by
    have ha : (tripleCharges (sourceA1970 + difference 3 2) (sourceB1970 + difference 2 3) sourceC1970) = raw27989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27989; decide +kernel
    rw [ha]
    exact (canonical27989 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1970 + difference 3 4) (sourceB1970 + difference 4 3) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA1970 + difference 3 4) (sourceB1970 + difference 4 3) sourceC1970) = raw27990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27990; decide +kernel
    rw [ha]
    exact (canonical27990 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1970 + difference 3 5) (sourceB1970 + difference 5 3) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA1970 + difference 3 5) (sourceB1970 + difference 5 3) sourceC1970) = raw27991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27991; decide +kernel
    rw [ha]
    exact (canonical27991 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1970 + difference 4 0) (sourceB1970 + difference 0 4) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA1970 + difference 4 0) (sourceB1970 + difference 0 4) sourceC1970) = raw27992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27992; decide +kernel
    rw [ha]
    exact (canonical27992 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1970 + difference 4 1) (sourceB1970 + difference 1 4) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA1970 + difference 4 1) (sourceB1970 + difference 1 4) sourceC1970) = raw27993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27993; decide +kernel
    rw [ha]
    exact (canonical27993 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1970 + difference 4 2) (sourceB1970 + difference 2 4) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA1970 + difference 4 2) (sourceB1970 + difference 2 4) sourceC1970) = raw27994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27994; decide +kernel
    rw [ha]
    exact (canonical27994 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1970 + difference 4 3) (sourceB1970 + difference 3 4) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1970 + difference 4 3) (sourceB1970 + difference 3 4) sourceC1970) = raw27810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27810; decide +kernel
    rw [ha]
    exact (canonical27810 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1970 + difference 4 5) (sourceB1970 + difference 5 4) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1970 + difference 4 5) (sourceB1970 + difference 5 4) sourceC1970) = raw27799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27799; decide +kernel
    rw [ha]
    exact (canonical27799 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1970 + difference 5 0) (sourceB1970 + difference 0 5) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA1970 + difference 5 0) (sourceB1970 + difference 0 5) sourceC1970) = raw27995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27995; decide +kernel
    rw [ha]
    exact (canonical27995 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1970 + difference 5 1) (sourceB1970 + difference 1 5) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA1970 + difference 5 1) (sourceB1970 + difference 1 5) sourceC1970) = raw27996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27996; decide +kernel
    rw [ha]
    exact (canonical27996 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1970 + difference 5 2) (sourceB1970 + difference 2 5) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2914) := by
    have ha : (tripleCharges (sourceA1970 + difference 5 2) (sourceB1970 + difference 2 5) sourceC1970) = raw27997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27997; decide +kernel
    rw [ha]
    exact (canonical27997 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1970 + difference 5 3) (sourceB1970 + difference 3 5) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA1970 + difference 5 3) (sourceB1970 + difference 3 5) sourceC1970) = raw27998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27998; decide +kernel
    rw [ha]
    exact (canonical27998 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1970 + difference 5 4) (sourceB1970 + difference 4 5) sourceC1970) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA1970 + difference 5 4) (sourceB1970 + difference 4 5) sourceC1970) = raw27999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1970 sourceB1970 sourceC1970 difference raw27999; decide +kernel
    rw [ha]
    exact (canonical27999 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1970 sourceB1970 sourceC1970
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1970, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1971 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1971 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1971 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm1971 : Integer.Sparse Master := [(Sum.inr 4199, 1), (Sum.inr 4202, 1), (Sum.inr 4205, 1), (Sum.inr 4219, 1), (Sum.inr 4253, 1), (Sum.inr 4521, 1), (Sum.inr 4525, 1), (Sum.inr 4543, 1), (Sum.inr 4605, 1), (Sum.inr 4633, 1), (Sum.inr 4638, 1), (Sum.inr 4650, 1), (Sum.inr 4707, 1), (Sum.inr 4713, 1), (Sum.inr 4729, 1), (Sum.inr 4764, 1), (Sum.inr 4770, 1), (Sum.inr 4805, 1), (Sum.inr 4807, 2), (Sum.inr 4810, 1), (Sum.inr 4839, 1), (Sum.inr 4843, 1), (Sum.inr 4889, 1), (Sum.inr 4890, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5172, 1), (Sum.inr 5294, 1), (Sum.inr 5435, 1)]

theorem sourceEq1971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1971 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 1) (sourceB1971 + difference 1 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 1) (sourceB1971 + difference 1 0) sourceC1971) = raw15180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw15180; decide +kernel
    rw [ha]
    exact (canonical15180 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 2) (sourceB1971 + difference 2 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 2) (sourceB1971 + difference 2 0) sourceC1971) = raw15181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw15181; decide +kernel
    rw [ha]
    exact (canonical15181 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 3) (sourceB1971 + difference 3 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 3) (sourceB1971 + difference 3 0) sourceC1971) = raw15182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw15182; decide +kernel
    rw [ha]
    exact (canonical15182 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 4) (sourceB1971 + difference 4 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 4) (sourceB1971 + difference 4 0) sourceC1971) = raw2687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw2687; decide +kernel
    rw [ha]
    exact (canonical2687 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 5) (sourceB1971 + difference 5 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 5) (sourceB1971 + difference 5 0) sourceC1971) = raw2682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw2682; decide +kernel
    rw [ha]
    exact (canonical2682 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 0) (sourceB1971 + difference 0 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 0) (sourceB1971 + difference 0 1) sourceC1971) = raw4617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4617; decide +kernel
    rw [ha]
    exact (canonical4617 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 2) (sourceB1971 + difference 2 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 2) (sourceB1971 + difference 2 1) sourceC1971) = raw4619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4619; decide +kernel
    rw [ha]
    exact (canonical4619 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 3) (sourceB1971 + difference 3 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 3) (sourceB1971 + difference 3 1) sourceC1971) = raw4620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4620; decide +kernel
    rw [ha]
    exact (canonical4620 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 4) (sourceB1971 + difference 4 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 4) (sourceB1971 + difference 4 1) sourceC1971) = raw2686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw2686; decide +kernel
    rw [ha]
    exact (canonical2686 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 5) (sourceB1971 + difference 5 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 5) (sourceB1971 + difference 5 1) sourceC1971) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 0) (sourceB1971 + difference 0 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 0) (sourceB1971 + difference 0 2) sourceC1971) = raw20934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw20934; decide +kernel
    rw [ha]
    exact (canonical20934 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 1) (sourceB1971 + difference 1 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4707) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 1) (sourceB1971 + difference 1 2) sourceC1971) = raw28000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28000; decide +kernel
    rw [ha]
    exact (canonical28000 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 3) (sourceB1971 + difference 3 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4713) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 3) (sourceB1971 + difference 3 2) sourceC1971) = raw28001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28001; decide +kernel
    rw [ha]
    exact (canonical28001 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 4) (sourceB1971 + difference 4 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 4) (sourceB1971 + difference 4 2) sourceC1971) = raw4610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4610; decide +kernel
    rw [ha]
    exact (canonical4610 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 5) (sourceB1971 + difference 5 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 5) (sourceB1971 + difference 5 2) sourceC1971) = raw7973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw7973; decide +kernel
    rw [ha]
    exact (canonical7973 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 0) (sourceB1971 + difference 0 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 0) (sourceB1971 + difference 0 3) sourceC1971) = raw20937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw20937; decide +kernel
    rw [ha]
    exact (canonical20937 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 1) (sourceB1971 + difference 1 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 1) (sourceB1971 + difference 1 3) sourceC1971) = raw28002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28002; decide +kernel
    rw [ha]
    exact (canonical28002 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 2) (sourceB1971 + difference 2 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4764) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 2) (sourceB1971 + difference 2 3) sourceC1971) = raw28003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28003; decide +kernel
    rw [ha]
    exact (canonical28003 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 4) (sourceB1971 + difference 4 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 4) (sourceB1971 + difference 4 3) sourceC1971) = raw4614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4614; decide +kernel
    rw [ha]
    exact (canonical4614 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 5) (sourceB1971 + difference 5 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 5) (sourceB1971 + difference 5 3) sourceC1971) = raw7977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw7977; decide +kernel
    rw [ha]
    exact (canonical7977 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 0) (sourceB1971 + difference 0 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 0) (sourceB1971 + difference 0 4) sourceC1971) = raw20940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw20940; decide +kernel
    rw [ha]
    exact (canonical20940 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 1) (sourceB1971 + difference 1 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4638) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 1) (sourceB1971 + difference 1 4) sourceC1971) = raw28004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28004; decide +kernel
    rw [ha]
    exact (canonical28004 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 2) (sourceB1971 + difference 2 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4633) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 2) (sourceB1971 + difference 2 4) sourceC1971) = raw28005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28005; decide +kernel
    rw [ha]
    exact (canonical28005 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 3) (sourceB1971 + difference 3 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 3) (sourceB1971 + difference 3 4) sourceC1971) = raw28006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28006; decide +kernel
    rw [ha]
    exact (canonical28006 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 5) (sourceB1971 + difference 5 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 5) (sourceB1971 + difference 5 4) sourceC1971) = raw7981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw7981; decide +kernel
    rw [ha]
    exact (canonical7981 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 0) (sourceB1971 + difference 0 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 0) (sourceB1971 + difference 0 5) sourceC1971) = raw20944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw20944; decide +kernel
    rw [ha]
    exact (canonical20944 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 1) (sourceB1971 + difference 1 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4205) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 1) (sourceB1971 + difference 1 5) sourceC1971) = raw28007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28007; decide +kernel
    rw [ha]
    exact (canonical28007 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 2) (sourceB1971 + difference 2 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4199) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 2) (sourceB1971 + difference 2 5) sourceC1971) = raw28008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28008; decide +kernel
    rw [ha]
    exact (canonical28008 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 3) (sourceB1971 + difference 3 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4219) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 3) (sourceB1971 + difference 3 5) sourceC1971) = raw28009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28009; decide +kernel
    rw [ha]
    exact (canonical28009 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 4) (sourceB1971 + difference 4 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 4) (sourceB1971 + difference 4 5) sourceC1971) = raw4622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4622; decide +kernel
    rw [ha]
    exact (canonical4622 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1971 sourceB1971 sourceC1971
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1971, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1972 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1972 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1972 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm1972 : Integer.Sparse Master := [(Sum.inr 702, 1), (Sum.inr 705, 1), (Sum.inr 708, 1), (Sum.inr 720, 1), (Sum.inr 787, 1), (Sum.inr 1105, 1), (Sum.inr 1109, 1), (Sum.inr 1128, 1), (Sum.inr 1239, 1), (Sum.inr 1762, 1), (Sum.inr 1767, 1), (Sum.inr 1778, 1), (Sum.inr 1861, 1), (Sum.inr 1867, 1), (Sum.inr 1898, 1), (Sum.inr 1964, 1), (Sum.inr 1970, 1), (Sum.inr 2023, 1), (Sum.inr 2025, 2), (Sum.inr 2028, 1), (Sum.inr 2058, 1), (Sum.inr 2062, 1), (Sum.inr 2245, 1), (Sum.inr 2247, 1), (Sum.inr 2924, 1), (Sum.inr 2931, 1), (Sum.inr 2959, 1), (Sum.inr 3101, 1), (Sum.inr 3853, 1)]

theorem sourceEq1972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1972 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1972 + difference 0 1) (sourceB1972 + difference 1 0) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA1972 + difference 0 1) (sourceB1972 + difference 1 0) sourceC1972) = raw15197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw15197; decide +kernel
    rw [ha]
    exact (canonical15197 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1972 + difference 0 2) (sourceB1972 + difference 2 0) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA1972 + difference 0 2) (sourceB1972 + difference 2 0) sourceC1972) = raw15198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw15198; decide +kernel
    rw [ha]
    exact (canonical15198 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1972 + difference 0 3) (sourceB1972 + difference 3 0) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA1972 + difference 0 3) (sourceB1972 + difference 3 0) sourceC1972) = raw15199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw15199; decide +kernel
    rw [ha]
    exact (canonical15199 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1972 + difference 0 4) (sourceB1972 + difference 4 0) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA1972 + difference 0 4) (sourceB1972 + difference 4 0) sourceC1972) = raw2717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw2717; decide +kernel
    rw [ha]
    exact (canonical2717 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1972 + difference 0 5) (sourceB1972 + difference 5 0) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA1972 + difference 0 5) (sourceB1972 + difference 5 0) sourceC1972) = raw2712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw2712; decide +kernel
    rw [ha]
    exact (canonical2712 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1972 + difference 1 0) (sourceB1972 + difference 0 1) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1972 + difference 1 0) (sourceB1972 + difference 0 1) sourceC1972) = raw4639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw4639; decide +kernel
    rw [ha]
    exact (canonical4639 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1972 + difference 1 2) (sourceB1972 + difference 2 1) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1972 + difference 1 2) (sourceB1972 + difference 2 1) sourceC1972) = raw4641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw4641; decide +kernel
    rw [ha]
    exact (canonical4641 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1972 + difference 1 3) (sourceB1972 + difference 3 1) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1972 + difference 1 3) (sourceB1972 + difference 3 1) sourceC1972) = raw4642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw4642; decide +kernel
    rw [ha]
    exact (canonical4642 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1972 + difference 1 4) (sourceB1972 + difference 4 1) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA1972 + difference 1 4) (sourceB1972 + difference 4 1) sourceC1972) = raw2716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw2716; decide +kernel
    rw [ha]
    exact (canonical2716 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1972 + difference 1 5) (sourceB1972 + difference 5 1) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA1972 + difference 1 5) (sourceB1972 + difference 5 1) sourceC1972) = raw2711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw2711; decide +kernel
    rw [ha]
    exact (canonical2711 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1972 + difference 2 0) (sourceB1972 + difference 0 2) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1105) := by
    have ha : (tripleCharges (sourceA1972 + difference 2 0) (sourceB1972 + difference 0 2) sourceC1972) = raw20951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw20951; decide +kernel
    rw [ha]
    exact (canonical20951 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1972 + difference 2 1) (sourceB1972 + difference 1 2) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1861) := by
    have ha : (tripleCharges (sourceA1972 + difference 2 1) (sourceB1972 + difference 1 2) sourceC1972) = raw28010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28010; decide +kernel
    rw [ha]
    exact (canonical28010 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1972 + difference 2 3) (sourceB1972 + difference 3 2) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1867) := by
    have ha : (tripleCharges (sourceA1972 + difference 2 3) (sourceB1972 + difference 3 2) sourceC1972) = raw28011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28011; decide +kernel
    rw [ha]
    exact (canonical28011 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1972 + difference 2 4) (sourceB1972 + difference 4 2) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA1972 + difference 2 4) (sourceB1972 + difference 4 2) sourceC1972) = raw4632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw4632; decide +kernel
    rw [ha]
    exact (canonical4632 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1972 + difference 2 5) (sourceB1972 + difference 5 2) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA1972 + difference 2 5) (sourceB1972 + difference 5 2) sourceC1972) = raw7990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw7990; decide +kernel
    rw [ha]
    exact (canonical7990 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1972 + difference 3 0) (sourceB1972 + difference 0 3) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1972 + difference 3 0) (sourceB1972 + difference 0 3) sourceC1972) = raw20954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw20954; decide +kernel
    rw [ha]
    exact (canonical20954 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1972 + difference 3 1) (sourceB1972 + difference 1 3) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA1972 + difference 3 1) (sourceB1972 + difference 1 3) sourceC1972) = raw28012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28012; decide +kernel
    rw [ha]
    exact (canonical28012 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1972 + difference 3 2) (sourceB1972 + difference 2 3) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1964) := by
    have ha : (tripleCharges (sourceA1972 + difference 3 2) (sourceB1972 + difference 2 3) sourceC1972) = raw28013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28013; decide +kernel
    rw [ha]
    exact (canonical28013 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1972 + difference 3 4) (sourceB1972 + difference 4 3) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1972 + difference 3 4) (sourceB1972 + difference 4 3) sourceC1972) = raw4636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw4636; decide +kernel
    rw [ha]
    exact (canonical4636 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1972 + difference 3 5) (sourceB1972 + difference 5 3) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA1972 + difference 3 5) (sourceB1972 + difference 5 3) sourceC1972) = raw7994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw7994; decide +kernel
    rw [ha]
    exact (canonical7994 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1972 + difference 4 0) (sourceB1972 + difference 0 4) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1109) := by
    have ha : (tripleCharges (sourceA1972 + difference 4 0) (sourceB1972 + difference 0 4) sourceC1972) = raw20957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw20957; decide +kernel
    rw [ha]
    exact (canonical20957 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1972 + difference 4 1) (sourceB1972 + difference 1 4) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1767) := by
    have ha : (tripleCharges (sourceA1972 + difference 4 1) (sourceB1972 + difference 1 4) sourceC1972) = raw28014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28014; decide +kernel
    rw [ha]
    exact (canonical28014 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1972 + difference 4 2) (sourceB1972 + difference 2 4) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1762) := by
    have ha : (tripleCharges (sourceA1972 + difference 4 2) (sourceB1972 + difference 2 4) sourceC1972) = raw28015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28015; decide +kernel
    rw [ha]
    exact (canonical28015 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1972 + difference 4 3) (sourceB1972 + difference 3 4) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1778) := by
    have ha : (tripleCharges (sourceA1972 + difference 4 3) (sourceB1972 + difference 3 4) sourceC1972) = raw28016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28016; decide +kernel
    rw [ha]
    exact (canonical28016 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1972 + difference 4 5) (sourceB1972 + difference 5 4) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA1972 + difference 4 5) (sourceB1972 + difference 5 4) sourceC1972) = raw7998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw7998; decide +kernel
    rw [ha]
    exact (canonical7998 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1972 + difference 5 0) (sourceB1972 + difference 0 5) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 705) := by
    have ha : (tripleCharges (sourceA1972 + difference 5 0) (sourceB1972 + difference 0 5) sourceC1972) = raw20961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw20961; decide +kernel
    rw [ha]
    exact (canonical20961 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1972 + difference 5 1) (sourceB1972 + difference 1 5) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 708) := by
    have ha : (tripleCharges (sourceA1972 + difference 5 1) (sourceB1972 + difference 1 5) sourceC1972) = raw28017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28017; decide +kernel
    rw [ha]
    exact (canonical28017 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1972 + difference 5 2) (sourceB1972 + difference 2 5) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 702) := by
    have ha : (tripleCharges (sourceA1972 + difference 5 2) (sourceB1972 + difference 2 5) sourceC1972) = raw28018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28018; decide +kernel
    rw [ha]
    exact (canonical28018 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1972 + difference 5 3) (sourceB1972 + difference 3 5) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 720) := by
    have ha : (tripleCharges (sourceA1972 + difference 5 3) (sourceB1972 + difference 3 5) sourceC1972) = raw28019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw28019; decide +kernel
    rw [ha]
    exact (canonical28019 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1972 + difference 5 4) (sourceB1972 + difference 4 5) sourceC1972) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1972 + difference 5 4) (sourceB1972 + difference 4 5) sourceC1972) = raw4644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1972 sourceB1972 sourceC1972 difference raw4644; decide +kernel
    rw [ha]
    exact (canonical4644 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1972 sourceB1972 sourceC1972
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1972, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1973 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1973 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1973 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceForm1973 : Integer.Sparse Master := [(Sum.inr 4327, 1), (Sum.inr 4331, 1), (Sum.inr 4333, 1), (Sum.inr 4335, 1), (Sum.inr 4336, 1), (Sum.inr 4352, 1), (Sum.inr 4353, 1), (Sum.inr 4442, 1), (Sum.inr 4463, 1), (Sum.inr 4664, 1), (Sum.inr 4670, 1), (Sum.inr 4686, 1), (Sum.inr 4757, 1), (Sum.inr 4764, 1), (Sum.inr 4772, 1), (Sum.inr 4777, 1), (Sum.inr 4792, 1), (Sum.inr 4802, 1), (Sum.inr 4807, 2), (Sum.inr 4811, 1), (Sum.inr 4838, 1), (Sum.inr 4871, 1), (Sum.inr 4890, 1), (Sum.inr 4895, 1), (Sum.inr 5150, 1), (Sum.inr 5151, 1), (Sum.inr 5173, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 1)]

theorem sourceEq1973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1973 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 1) (sourceB1973 + difference 1 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 1) (sourceB1973 + difference 1 0) sourceC1973) = raw28020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28020; decide +kernel
    rw [ha]
    exact (canonical28020 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 2) (sourceB1973 + difference 2 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 2) (sourceB1973 + difference 2 0) sourceC1973) = raw28021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28021; decide +kernel
    rw [ha]
    exact (canonical28021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 3) (sourceB1973 + difference 3 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 3) (sourceB1973 + difference 3 0) sourceC1973) = raw28022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28022; decide +kernel
    rw [ha]
    exact (canonical28022 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 4) (sourceB1973 + difference 4 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 4) (sourceB1973 + difference 4 0) sourceC1973) = raw28023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28023; decide +kernel
    rw [ha]
    exact (canonical28023 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 5) (sourceB1973 + difference 5 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 5) (sourceB1973 + difference 5 0) sourceC1973) = raw28024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28024; decide +kernel
    rw [ha]
    exact (canonical28024 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 0) (sourceB1973 + difference 0 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 0) (sourceB1973 + difference 0 1) sourceC1973) = raw28025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28025; decide +kernel
    rw [ha]
    exact (canonical28025 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 2) (sourceB1973 + difference 2 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 2) (sourceB1973 + difference 2 1) sourceC1973) = raw28026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28026; decide +kernel
    rw [ha]
    exact (canonical28026 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 3) (sourceB1973 + difference 3 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 3) (sourceB1973 + difference 3 1) sourceC1973) = raw28027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28027; decide +kernel
    rw [ha]
    exact (canonical28027 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 4) (sourceB1973 + difference 4 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 4) (sourceB1973 + difference 4 1) sourceC1973) = raw28028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28028; decide +kernel
    rw [ha]
    exact (canonical28028 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 5) (sourceB1973 + difference 5 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 5) (sourceB1973 + difference 5 1) sourceC1973) = raw28029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28029; decide +kernel
    rw [ha]
    exact (canonical28029 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 0) (sourceB1973 + difference 0 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4331) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 0) (sourceB1973 + difference 0 2) sourceC1973) = raw28030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28030; decide +kernel
    rw [ha]
    exact (canonical28030 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 1) (sourceB1973 + difference 1 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4757) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 1) (sourceB1973 + difference 1 2) sourceC1973) = raw28031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28031; decide +kernel
    rw [ha]
    exact (canonical28031 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 3) (sourceB1973 + difference 3 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4764) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 3) (sourceB1973 + difference 3 2) sourceC1973) = raw28032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28032; decide +kernel
    rw [ha]
    exact (canonical28032 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 4) (sourceB1973 + difference 4 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 4) (sourceB1973 + difference 4 2) sourceC1973) = raw28033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28033; decide +kernel
    rw [ha]
    exact (canonical28033 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 5) (sourceB1973 + difference 5 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 5) (sourceB1973 + difference 5 2) sourceC1973) = raw28034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28034; decide +kernel
    rw [ha]
    exact (canonical28034 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 0) (sourceB1973 + difference 0 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4353) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 0) (sourceB1973 + difference 0 3) sourceC1973) = raw28035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28035; decide +kernel
    rw [ha]
    exact (canonical28035 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 1) (sourceB1973 + difference 1 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 1) (sourceB1973 + difference 1 3) sourceC1973) = raw28036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28036; decide +kernel
    rw [ha]
    exact (canonical28036 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 2) (sourceB1973 + difference 2 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4772) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 2) (sourceB1973 + difference 2 3) sourceC1973) = raw28037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28037; decide +kernel
    rw [ha]
    exact (canonical28037 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 4) (sourceB1973 + difference 4 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 4) (sourceB1973 + difference 4 3) sourceC1973) = raw28038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28038; decide +kernel
    rw [ha]
    exact (canonical28038 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 5) (sourceB1973 + difference 5 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 5) (sourceB1973 + difference 5 3) sourceC1973) = raw28039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28039; decide +kernel
    rw [ha]
    exact (canonical28039 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 0) (sourceB1973 + difference 0 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4336) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 0) (sourceB1973 + difference 0 4) sourceC1973) = raw28040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28040; decide +kernel
    rw [ha]
    exact (canonical28040 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 1) (sourceB1973 + difference 1 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4670) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 1) (sourceB1973 + difference 1 4) sourceC1973) = raw28041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28041; decide +kernel
    rw [ha]
    exact (canonical28041 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 2) (sourceB1973 + difference 2 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4664) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 2) (sourceB1973 + difference 2 4) sourceC1973) = raw28042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28042; decide +kernel
    rw [ha]
    exact (canonical28042 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 3) (sourceB1973 + difference 3 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 3) (sourceB1973 + difference 3 4) sourceC1973) = raw28043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28043; decide +kernel
    rw [ha]
    exact (canonical28043 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 5) (sourceB1973 + difference 5 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 5) (sourceB1973 + difference 5 4) sourceC1973) = raw28044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28044; decide +kernel
    rw [ha]
    exact (canonical28044 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 0) (sourceB1973 + difference 0 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4333) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 0) (sourceB1973 + difference 0 5) sourceC1973) = raw28045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28045; decide +kernel
    rw [ha]
    exact (canonical28045 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 1) (sourceB1973 + difference 1 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 1) (sourceB1973 + difference 1 5) sourceC1973) = raw28046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28046; decide +kernel
    rw [ha]
    exact (canonical28046 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 2) (sourceB1973 + difference 2 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 2) (sourceB1973 + difference 2 5) sourceC1973) = raw28047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28047; decide +kernel
    rw [ha]
    exact (canonical28047 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 3) (sourceB1973 + difference 3 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 3) (sourceB1973 + difference 3 5) sourceC1973) = raw28048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28048; decide +kernel
    rw [ha]
    exact (canonical28048 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 4) (sourceB1973 + difference 4 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 4) (sourceB1973 + difference 4 5) sourceC1973) = raw28049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28049; decide +kernel
    rw [ha]
    exact (canonical28049 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1973 sourceB1973 sourceC1973
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1973, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1974 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1974 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1974 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceForm1974 : Integer.Sparse Master := [(Sum.inr 909, 1), (Sum.inr 911, 1), (Sum.inr 914, 1), (Sum.inr 931, 1), (Sum.inr 1024, 1), (Sum.inr 1327, 1), (Sum.inr 1333, 1), (Sum.inr 1340, 1), (Sum.inr 1413, 1), (Sum.inr 2323, 1), (Sum.inr 2327, 1), (Sum.inr 2340, 1), (Sum.inr 2423, 1), (Sum.inr 2430, 1), (Sum.inr 2471, 1), (Sum.inr 2528, 1), (Sum.inr 2532, 1), (Sum.inr 2573, 1), (Sum.inr 2574, 2), (Sum.inr 2575, 1), (Sum.inr 2600, 1), (Sum.inr 2602, 1), (Sum.inr 2754, 1), (Sum.inr 2755, 1), (Sum.inr 3109, 1), (Sum.inr 3204, 1), (Sum.inr 3207, 1), (Sum.inr 3213, 1), (Sum.inr 3229, 1)]

theorem sourceEq1974 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1974 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1974 + difference 0 1) (sourceB1974 + difference 1 0) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3207) := by
    have ha : (tripleCharges (sourceA1974 + difference 0 1) (sourceB1974 + difference 1 0) sourceC1974) = raw28050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28050; decide +kernel
    rw [ha]
    exact (canonical28050 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1974 + difference 0 2) (sourceB1974 + difference 2 0) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA1974 + difference 0 2) (sourceB1974 + difference 2 0) sourceC1974) = raw28051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28051; decide +kernel
    rw [ha]
    exact (canonical28051 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1974 + difference 0 3) (sourceB1974 + difference 3 0) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3213) := by
    have ha : (tripleCharges (sourceA1974 + difference 0 3) (sourceB1974 + difference 3 0) sourceC1974) = raw28052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28052; decide +kernel
    rw [ha]
    exact (canonical28052 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1974 + difference 0 4) (sourceB1974 + difference 4 0) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA1974 + difference 0 4) (sourceB1974 + difference 4 0) sourceC1974) = raw28053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28053; decide +kernel
    rw [ha]
    exact (canonical28053 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1974 + difference 0 5) (sourceB1974 + difference 5 0) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA1974 + difference 0 5) (sourceB1974 + difference 5 0) sourceC1974) = raw28054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28054; decide +kernel
    rw [ha]
    exact (canonical28054 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1974 + difference 1 0) (sourceB1974 + difference 0 1) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA1974 + difference 1 0) (sourceB1974 + difference 0 1) sourceC1974) = raw28055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28055; decide +kernel
    rw [ha]
    exact (canonical28055 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1974 + difference 1 2) (sourceB1974 + difference 2 1) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA1974 + difference 1 2) (sourceB1974 + difference 2 1) sourceC1974) = raw28056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28056; decide +kernel
    rw [ha]
    exact (canonical28056 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1974 + difference 1 3) (sourceB1974 + difference 3 1) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA1974 + difference 1 3) (sourceB1974 + difference 3 1) sourceC1974) = raw28057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28057; decide +kernel
    rw [ha]
    exact (canonical28057 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1974 + difference 1 4) (sourceB1974 + difference 4 1) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA1974 + difference 1 4) (sourceB1974 + difference 4 1) sourceC1974) = raw28058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28058; decide +kernel
    rw [ha]
    exact (canonical28058 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1974 + difference 1 5) (sourceB1974 + difference 5 1) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA1974 + difference 1 5) (sourceB1974 + difference 5 1) sourceC1974) = raw28059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28059; decide +kernel
    rw [ha]
    exact (canonical28059 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1974 + difference 2 0) (sourceB1974 + difference 0 2) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 909) := by
    have ha : (tripleCharges (sourceA1974 + difference 2 0) (sourceB1974 + difference 0 2) sourceC1974) = raw28060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28060; decide +kernel
    rw [ha]
    exact (canonical28060 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1974 + difference 2 1) (sourceB1974 + difference 1 2) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2323) := by
    have ha : (tripleCharges (sourceA1974 + difference 2 1) (sourceB1974 + difference 1 2) sourceC1974) = raw28061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28061; decide +kernel
    rw [ha]
    exact (canonical28061 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1974 + difference 2 3) (sourceB1974 + difference 3 2) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2528) := by
    have ha : (tripleCharges (sourceA1974 + difference 2 3) (sourceB1974 + difference 3 2) sourceC1974) = raw28062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28062; decide +kernel
    rw [ha]
    exact (canonical28062 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1974 + difference 2 4) (sourceB1974 + difference 4 2) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA1974 + difference 2 4) (sourceB1974 + difference 4 2) sourceC1974) = raw28063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28063; decide +kernel
    rw [ha]
    exact (canonical28063 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1974 + difference 2 5) (sourceB1974 + difference 5 2) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA1974 + difference 2 5) (sourceB1974 + difference 5 2) sourceC1974) = raw28064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28064; decide +kernel
    rw [ha]
    exact (canonical28064 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1974 + difference 3 0) (sourceB1974 + difference 0 3) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 931) := by
    have ha : (tripleCharges (sourceA1974 + difference 3 0) (sourceB1974 + difference 0 3) sourceC1974) = raw28065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28065; decide +kernel
    rw [ha]
    exact (canonical28065 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1974 + difference 3 1) (sourceB1974 + difference 1 3) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA1974 + difference 3 1) (sourceB1974 + difference 1 3) sourceC1974) = raw28066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28066; decide +kernel
    rw [ha]
    exact (canonical28066 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1974 + difference 3 2) (sourceB1974 + difference 2 3) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2430) := by
    have ha : (tripleCharges (sourceA1974 + difference 3 2) (sourceB1974 + difference 2 3) sourceC1974) = raw28067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28067; decide +kernel
    rw [ha]
    exact (canonical28067 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1974 + difference 3 4) (sourceB1974 + difference 4 3) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2602) := by
    have ha : (tripleCharges (sourceA1974 + difference 3 4) (sourceB1974 + difference 4 3) sourceC1974) = raw28068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28068; decide +kernel
    rw [ha]
    exact (canonical28068 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1974 + difference 3 5) (sourceB1974 + difference 5 3) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA1974 + difference 3 5) (sourceB1974 + difference 5 3) sourceC1974) = raw28069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28069; decide +kernel
    rw [ha]
    exact (canonical28069 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1974 + difference 4 0) (sourceB1974 + difference 0 4) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 914) := by
    have ha : (tripleCharges (sourceA1974 + difference 4 0) (sourceB1974 + difference 0 4) sourceC1974) = raw28070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28070; decide +kernel
    rw [ha]
    exact (canonical28070 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1974 + difference 4 1) (sourceB1974 + difference 1 4) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2327) := by
    have ha : (tripleCharges (sourceA1974 + difference 4 1) (sourceB1974 + difference 1 4) sourceC1974) = raw28071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28071; decide +kernel
    rw [ha]
    exact (canonical28071 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1974 + difference 4 2) (sourceB1974 + difference 2 4) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2423) := by
    have ha : (tripleCharges (sourceA1974 + difference 4 2) (sourceB1974 + difference 2 4) sourceC1974) = raw28072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28072; decide +kernel
    rw [ha]
    exact (canonical28072 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1974 + difference 4 3) (sourceB1974 + difference 3 4) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2532) := by
    have ha : (tripleCharges (sourceA1974 + difference 4 3) (sourceB1974 + difference 3 4) sourceC1974) = raw28073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28073; decide +kernel
    rw [ha]
    exact (canonical28073 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1974 + difference 4 5) (sourceB1974 + difference 5 4) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA1974 + difference 4 5) (sourceB1974 + difference 5 4) sourceC1974) = raw28074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28074; decide +kernel
    rw [ha]
    exact (canonical28074 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1974 + difference 5 0) (sourceB1974 + difference 0 5) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1974 + difference 5 0) (sourceB1974 + difference 0 5) sourceC1974) = raw28075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28075; decide +kernel
    rw [ha]
    exact (canonical28075 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1974 + difference 5 1) (sourceB1974 + difference 1 5) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1974 + difference 5 1) (sourceB1974 + difference 1 5) sourceC1974) = raw28076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28076; decide +kernel
    rw [ha]
    exact (canonical28076 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1974 + difference 5 2) (sourceB1974 + difference 2 5) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1974 + difference 5 2) (sourceB1974 + difference 2 5) sourceC1974) = raw28077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28077; decide +kernel
    rw [ha]
    exact (canonical28077 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1974 + difference 5 3) (sourceB1974 + difference 3 5) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1340) := by
    have ha : (tripleCharges (sourceA1974 + difference 5 3) (sourceB1974 + difference 3 5) sourceC1974) = raw28078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28078; decide +kernel
    rw [ha]
    exact (canonical28078 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1974 + difference 5 4) (sourceB1974 + difference 4 5) sourceC1974) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1974 + difference 5 4) (sourceB1974 + difference 4 5) sourceC1974) = raw28079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1974 sourceB1974 sourceC1974 difference raw28079; decide +kernel
    rw [ha]
    exact (canonical28079 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1974 sourceB1974 sourceC1974
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1974, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1975 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1975 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1975 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceForm1975 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1684, 1), (Sum.inr 1685, 1), (Sum.inr 1686, 1), (Sum.inr 1688, 1), (Sum.inr 1689, 1), (Sum.inr 1690, 1), (Sum.inr 1744, 1), (Sum.inr 1750, 1), (Sum.inr 2147, 1), (Sum.inr 2164, 1), (Sum.inr 2165, 1), (Sum.inr 2181, 1), (Sum.inr 2182, 1), (Sum.inr 2198, 1), (Sum.inr 2201, 1), (Sum.inr 2202, 1), (Sum.inr 2223, 1), (Sum.inr 2224, 2), (Sum.inr 2225, 1), (Sum.inr 2227, 1), (Sum.inr 2287, 1), (Sum.inr 2290, 1), (Sum.inr 2291, 1), (Sum.inr 2681, 1), (Sum.inr 2700, 1), (Sum.inr 2735, 1), (Sum.inr 2738, 1), (Sum.inr 2739, 1)]

theorem sourceEq1975 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1975 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 1) (sourceB1975 + difference 1 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 1) (sourceB1975 + difference 1 0) sourceC1975) = raw28080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28080; decide +kernel
    rw [ha]
    exact (canonical28080 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 2) (sourceB1975 + difference 2 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 2) (sourceB1975 + difference 2 0) sourceC1975) = raw28081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28081; decide +kernel
    rw [ha]
    exact (canonical28081 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 3) (sourceB1975 + difference 3 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 3) (sourceB1975 + difference 3 0) sourceC1975) = raw28082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28082; decide +kernel
    rw [ha]
    exact (canonical28082 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 4) (sourceB1975 + difference 4 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 4) (sourceB1975 + difference 4 0) sourceC1975) = raw28083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28083; decide +kernel
    rw [ha]
    exact (canonical28083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 5) (sourceB1975 + difference 5 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 5) (sourceB1975 + difference 5 0) sourceC1975) = raw28084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28084; decide +kernel
    rw [ha]
    exact (canonical28084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 0) (sourceB1975 + difference 0 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 0) (sourceB1975 + difference 0 1) sourceC1975) = raw28085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28085; decide +kernel
    rw [ha]
    exact (canonical28085 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 2) (sourceB1975 + difference 2 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 2) (sourceB1975 + difference 2 1) sourceC1975) = raw28086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28086; decide +kernel
    rw [ha]
    exact (canonical28086 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 3) (sourceB1975 + difference 3 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 3) (sourceB1975 + difference 3 1) sourceC1975) = raw28087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28087; decide +kernel
    rw [ha]
    exact (canonical28087 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 4) (sourceB1975 + difference 4 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 4) (sourceB1975 + difference 4 1) sourceC1975) = raw28088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28088; decide +kernel
    rw [ha]
    exact (canonical28088 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 5) (sourceB1975 + difference 5 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 5) (sourceB1975 + difference 5 1) sourceC1975) = raw28089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28089; decide +kernel
    rw [ha]
    exact (canonical28089 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 0) (sourceB1975 + difference 0 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1684) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 0) (sourceB1975 + difference 0 2) sourceC1975) = raw28090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28090; decide +kernel
    rw [ha]
    exact (canonical28090 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 1) (sourceB1975 + difference 1 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 1) (sourceB1975 + difference 1 2) sourceC1975) = raw28091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28091; decide +kernel
    rw [ha]
    exact (canonical28091 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 3) (sourceB1975 + difference 3 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2182) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 3) (sourceB1975 + difference 3 2) sourceC1975) = raw28092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28092; decide +kernel
    rw [ha]
    exact (canonical28092 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 4) (sourceB1975 + difference 4 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 4) (sourceB1975 + difference 4 2) sourceC1975) = raw28093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28093; decide +kernel
    rw [ha]
    exact (canonical28093 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 5) (sourceB1975 + difference 5 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 5) (sourceB1975 + difference 5 2) sourceC1975) = raw28094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28094; decide +kernel
    rw [ha]
    exact (canonical28094 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 0) (sourceB1975 + difference 0 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 0) (sourceB1975 + difference 0 3) sourceC1975) = raw28095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28095; decide +kernel
    rw [ha]
    exact (canonical28095 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 1) (sourceB1975 + difference 1 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 1) (sourceB1975 + difference 1 3) sourceC1975) = raw28096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28096; decide +kernel
    rw [ha]
    exact (canonical28096 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 2) (sourceB1975 + difference 2 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 2) (sourceB1975 + difference 2 3) sourceC1975) = raw28097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28097; decide +kernel
    rw [ha]
    exact (canonical28097 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 4) (sourceB1975 + difference 4 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 4) (sourceB1975 + difference 4 3) sourceC1975) = raw28098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28098; decide +kernel
    rw [ha]
    exact (canonical28098 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 5) (sourceB1975 + difference 5 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 5) (sourceB1975 + difference 5 3) sourceC1975) = raw28099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28099; decide +kernel
    rw [ha]
    exact (canonical28099 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 0) (sourceB1975 + difference 0 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 0) (sourceB1975 + difference 0 4) sourceC1975) = raw28100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28100; decide +kernel
    rw [ha]
    exact (canonical28100 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 1) (sourceB1975 + difference 1 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 1) (sourceB1975 + difference 1 4) sourceC1975) = raw28101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28101; decide +kernel
    rw [ha]
    exact (canonical28101 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 2) (sourceB1975 + difference 2 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 2) (sourceB1975 + difference 2 4) sourceC1975) = raw28102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28102; decide +kernel
    rw [ha]
    exact (canonical28102 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 3) (sourceB1975 + difference 3 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 3) (sourceB1975 + difference 3 4) sourceC1975) = raw28103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28103; decide +kernel
    rw [ha]
    exact (canonical28103 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 5) (sourceB1975 + difference 5 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 5) (sourceB1975 + difference 5 4) sourceC1975) = raw28104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28104; decide +kernel
    rw [ha]
    exact (canonical28104 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 0) (sourceB1975 + difference 0 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 0) (sourceB1975 + difference 0 5) sourceC1975) = raw28105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28105; decide +kernel
    rw [ha]
    exact (canonical28105 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 1) (sourceB1975 + difference 1 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 1) (sourceB1975 + difference 1 5) sourceC1975) = raw28106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28106; decide +kernel
    rw [ha]
    exact (canonical28106 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 2) (sourceB1975 + difference 2 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 2) (sourceB1975 + difference 2 5) sourceC1975) = raw28107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28107; decide +kernel
    rw [ha]
    exact (canonical28107 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 3) (sourceB1975 + difference 3 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 3) (sourceB1975 + difference 3 5) sourceC1975) = raw28108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28108; decide +kernel
    rw [ha]
    exact (canonical28108 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 4) (sourceB1975 + difference 4 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 4) (sourceB1975 + difference 4 5) sourceC1975) = raw28109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28109; decide +kernel
    rw [ha]
    exact (canonical28109 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1975 sourceB1975 sourceC1975
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1975, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1976 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1976 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1976 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceForm1976 : Integer.Sparse Master := [(Sum.inr 913, 1), (Sum.inr 1796, 1), (Sum.inr 1956, 1), (Sum.inr 1979, 1), (Sum.inr 2025, 1), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

theorem sourceEq1976 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1976 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1976 + difference 0 1) (sourceB1976 + difference 1 0) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA1976 + difference 0 1) (sourceB1976 + difference 1 0) sourceC1976) = raw28110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28110; decide +kernel
    rw [ha]
    exact (canonical28110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1976 + difference 1 1) (sourceB1976 + difference 1 1) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1976 + difference 1 1) (sourceB1976 + difference 1 1) sourceC1976) = raw28111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28111; decide +kernel
    rw [ha]
    exact (canonical28111 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1976 + difference 2 1) (sourceB1976 + difference 1 2) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1956) := by
    have ha : (tripleCharges (sourceA1976 + difference 2 1) (sourceB1976 + difference 1 2) sourceC1976) = raw28112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28112; decide +kernel
    rw [ha]
    exact (canonical28112 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1976 + difference 3 1) (sourceB1976 + difference 1 3) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1979) := by
    have ha : (tripleCharges (sourceA1976 + difference 3 1) (sourceB1976 + difference 1 3) sourceC1976) = raw28113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28113; decide +kernel
    rw [ha]
    exact (canonical28113 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1976 + difference 4 1) (sourceB1976 + difference 1 4) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1796) := by
    have ha : (tripleCharges (sourceA1976 + difference 4 1) (sourceB1976 + difference 1 4) sourceC1976) = raw28114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28114; decide +kernel
    rw [ha]
    exact (canonical28114 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1976 + difference 5 1) (sourceB1976 + difference 1 5) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 913) := by
    have ha : (tripleCharges (sourceA1976 + difference 5 1) (sourceB1976 + difference 1 5) sourceC1976) = raw28115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28115; decide +kernel
    rw [ha]
    exact (canonical28115 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1976 + sourceB1976) sourceC1976) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1976 + sourceB1976) sourceC1976) = raw28116 := by
      apply Matrix.ext; unfold doubleCharges sourceA1976 sourceB1976 sourceC1976 raw28116; decide +kernel
    rw [ha]
    exact (canonical28116 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1976 sourceB1976 sourceC1976
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1976, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1977 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1977 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1977 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceForm1977 : Integer.Sparse Master := [(Sum.inr 1326, 1), (Sum.inr 1956, 1), (Sum.inr 1964, 1), (Sum.inr 2025, 2), (Sum.inr 2923, 1), (Sum.inr 4083, -1)]

theorem sourceEq1977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1977 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 0) (sourceB1977 + difference 0 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1326) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 0) (sourceB1977 + difference 0 2) sourceC1977) = raw28117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28117; decide +kernel
    rw [ha]
    exact (canonical28117 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 1) (sourceB1977 + difference 1 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1956) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 1) (sourceB1977 + difference 1 2) sourceC1977) = raw28112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28112; decide +kernel
    rw [ha]
    exact (canonical28112 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 2) (sourceB1977 + difference 2 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 2) (sourceB1977 + difference 2 2) sourceC1977) = raw28111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28111; decide +kernel
    rw [ha]
    exact (canonical28111 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 3) (sourceB1977 + difference 3 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1964) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 3) (sourceB1977 + difference 3 2) sourceC1977) = raw28118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28118; decide +kernel
    rw [ha]
    exact (canonical28118 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 4) (sourceB1977 + difference 4 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 4) (sourceB1977 + difference 4 2) sourceC1977) = raw28119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28119; decide +kernel
    rw [ha]
    exact (canonical28119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 5) (sourceB1977 + difference 5 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 5) (sourceB1977 + difference 5 2) sourceC1977) = raw28120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28120; decide +kernel
    rw [ha]
    exact (canonical28120 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1977 + sourceB1977) sourceC1977) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1977 + sourceB1977) sourceC1977) = raw28116 := by
      apply Matrix.ext; unfold doubleCharges sourceA1977 sourceB1977 sourceC1977 raw28116; decide +kernel
    rw [ha]
    exact (canonical28116 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1977 sourceB1977 sourceC1977
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1977, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1978 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1978 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1978 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceForm1978 : Integer.Sparse Master := [(Sum.inr 930, 1), (Sum.inr 1812, 1), (Sum.inr 1964, 1), (Sum.inr 2025, 2), (Sum.inr 2057, 1), (Sum.inr 4083, -1)]

theorem sourceEq1978 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1978 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1978 + difference 0 3) (sourceB1978 + difference 3 0) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2057) := by
    have ha : (tripleCharges (sourceA1978 + difference 0 3) (sourceB1978 + difference 3 0) sourceC1978) = raw28121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28121; decide +kernel
    rw [ha]
    exact (canonical28121 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1978 + difference 1 3) (sourceB1978 + difference 3 1) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1978 + difference 1 3) (sourceB1978 + difference 3 1) sourceC1978) = raw28122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28122; decide +kernel
    rw [ha]
    exact (canonical28122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1978 + difference 2 3) (sourceB1978 + difference 3 2) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1964) := by
    have ha : (tripleCharges (sourceA1978 + difference 2 3) (sourceB1978 + difference 3 2) sourceC1978) = raw28118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28118; decide +kernel
    rw [ha]
    exact (canonical28118 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1978 + difference 3 3) (sourceB1978 + difference 3 3) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1978 + difference 3 3) (sourceB1978 + difference 3 3) sourceC1978) = raw28111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28111; decide +kernel
    rw [ha]
    exact (canonical28111 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1978 + difference 4 3) (sourceB1978 + difference 3 4) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1812) := by
    have ha : (tripleCharges (sourceA1978 + difference 4 3) (sourceB1978 + difference 3 4) sourceC1978) = raw28123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28123; decide +kernel
    rw [ha]
    exact (canonical28123 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1978 + difference 5 3) (sourceB1978 + difference 3 5) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1978 + difference 5 3) (sourceB1978 + difference 3 5) sourceC1978) = raw28124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28124; decide +kernel
    rw [ha]
    exact (canonical28124 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1978 + sourceB1978) sourceC1978) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1978 + sourceB1978) sourceC1978) = raw28116 := by
      apply Matrix.ext; unfold doubleCharges sourceA1978 sourceB1978 sourceC1978 raw28116; decide +kernel
    rw [ha]
    exact (canonical28116 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1978 sourceB1978 sourceC1978
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1978, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1979 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceB1979 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1979 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1979 : Integer.Sparse Master := [(Sum.inr 4414, 1), (Sum.inr 4418, 1), (Sum.inr 4420, 1), (Sum.inr 4425, 1), (Sum.inr 4486, 1), (Sum.inr 4729, 1), (Sum.inr 4741, 1), (Sum.inr 4742, 1), (Sum.inr 4747, 1), (Sum.inr 4779, 1), (Sum.inr 4780, 1), (Sum.inr 4783, 1), (Sum.inr 4792, 1), (Sum.inr 4793, 1), (Sum.inr 4804, 1), (Sum.inr 4807, 2), (Sum.inr 4808, 2), (Sum.inr 4817, 1), (Sum.inr 4819, 1), (Sum.inr 4824, 1), (Sum.inr 4841, 1), (Sum.inr 4843, 1), (Sum.inr 4853, 1), (Sum.inr 4871, 1), (Sum.inr 5078, 2), (Sum.inr 5128, 1), (Sum.inr 5174, 1)]

theorem sourceEq1979 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1979 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 1) (sourceB1979 + difference 1 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 1) (sourceB1979 + difference 1 0) sourceC1979) = raw28125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28125; decide +kernel
    rw [ha]
    exact (canonical28125 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 2) (sourceB1979 + difference 2 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 2) (sourceB1979 + difference 2 0) sourceC1979) = raw28126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28126; decide +kernel
    rw [ha]
    exact (canonical28126 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 3) (sourceB1979 + difference 3 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 3) (sourceB1979 + difference 3 0) sourceC1979) = raw27642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27642; decide +kernel
    rw [ha]
    exact (canonical27642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 4) (sourceB1979 + difference 4 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 4) (sourceB1979 + difference 4 0) sourceC1979) = raw27954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27954; decide +kernel
    rw [ha]
    exact (canonical27954 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 5) (sourceB1979 + difference 5 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 5) (sourceB1979 + difference 5 0) sourceC1979) = raw28127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28127; decide +kernel
    rw [ha]
    exact (canonical28127 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 0) (sourceB1979 + difference 0 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 0) (sourceB1979 + difference 0 1) sourceC1979) = raw28128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28128; decide +kernel
    rw [ha]
    exact (canonical28128 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 2) (sourceB1979 + difference 2 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4780) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 2) (sourceB1979 + difference 2 1) sourceC1979) = raw28129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28129; decide +kernel
    rw [ha]
    exact (canonical28129 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 3) (sourceB1979 + difference 3 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 3) (sourceB1979 + difference 3 1) sourceC1979) = raw27647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27647; decide +kernel
    rw [ha]
    exact (canonical27647 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 4) (sourceB1979 + difference 4 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 4) (sourceB1979 + difference 4 1) sourceC1979) = raw27958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27958; decide +kernel
    rw [ha]
    exact (canonical27958 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 5) (sourceB1979 + difference 5 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4420) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 5) (sourceB1979 + difference 5 1) sourceC1979) = raw28130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28130; decide +kernel
    rw [ha]
    exact (canonical28130 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 0) (sourceB1979 + difference 0 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 0) (sourceB1979 + difference 0 2) sourceC1979) = raw28131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28131; decide +kernel
    rw [ha]
    exact (canonical28131 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 1) (sourceB1979 + difference 1 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 1) (sourceB1979 + difference 1 2) sourceC1979) = raw28132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28132; decide +kernel
    rw [ha]
    exact (canonical28132 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 3) (sourceB1979 + difference 3 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 3) (sourceB1979 + difference 3 2) sourceC1979) = raw27652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27652; decide +kernel
    rw [ha]
    exact (canonical27652 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 4) (sourceB1979 + difference 4 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 4) (sourceB1979 + difference 4 2) sourceC1979) = raw27962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27962; decide +kernel
    rw [ha]
    exact (canonical27962 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 5) (sourceB1979 + difference 5 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4414) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 5) (sourceB1979 + difference 5 2) sourceC1979) = raw28133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28133; decide +kernel
    rw [ha]
    exact (canonical28133 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 0) (sourceB1979 + difference 0 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 0) (sourceB1979 + difference 0 3) sourceC1979) = raw28134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28134; decide +kernel
    rw [ha]
    exact (canonical28134 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 1) (sourceB1979 + difference 1 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 1) (sourceB1979 + difference 1 3) sourceC1979) = raw28135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28135; decide +kernel
    rw [ha]
    exact (canonical28135 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 2) (sourceB1979 + difference 2 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4783) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 2) (sourceB1979 + difference 2 3) sourceC1979) = raw28136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28136; decide +kernel
    rw [ha]
    exact (canonical28136 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 4) (sourceB1979 + difference 4 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 4) (sourceB1979 + difference 4 3) sourceC1979) = raw27967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27967; decide +kernel
    rw [ha]
    exact (canonical27967 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 5) (sourceB1979 + difference 5 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4425) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 5) (sourceB1979 + difference 5 3) sourceC1979) = raw28137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28137; decide +kernel
    rw [ha]
    exact (canonical28137 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 0) (sourceB1979 + difference 0 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 0) (sourceB1979 + difference 0 4) sourceC1979) = raw27771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27771; decide +kernel
    rw [ha]
    exact (canonical27771 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 1) (sourceB1979 + difference 1 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 1) (sourceB1979 + difference 1 4) sourceC1979) = raw27772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27772; decide +kernel
    rw [ha]
    exact (canonical27772 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 2) (sourceB1979 + difference 2 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4824) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 2) (sourceB1979 + difference 2 4) sourceC1979) = raw27773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27773; decide +kernel
    rw [ha]
    exact (canonical27773 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 3) (sourceB1979 + difference 3 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 3) (sourceB1979 + difference 3 4) sourceC1979) = raw27662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27662; decide +kernel
    rw [ha]
    exact (canonical27662 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 5) (sourceB1979 + difference 5 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 5) (sourceB1979 + difference 5 4) sourceC1979) = raw27774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27774; decide +kernel
    rw [ha]
    exact (canonical27774 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 0) (sourceB1979 + difference 0 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 0) (sourceB1979 + difference 0 5) sourceC1979) = raw27653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27653; decide +kernel
    rw [ha]
    exact (canonical27653 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 1) (sourceB1979 + difference 1 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 1) (sourceB1979 + difference 1 5) sourceC1979) = raw27654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27654; decide +kernel
    rw [ha]
    exact (canonical27654 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 2) (sourceB1979 + difference 2 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 2) (sourceB1979 + difference 2 5) sourceC1979) = raw27655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27655; decide +kernel
    rw [ha]
    exact (canonical27655 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 3) (sourceB1979 + difference 3 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 3) (sourceB1979 + difference 3 5) sourceC1979) = raw27780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27780; decide +kernel
    rw [ha]
    exact (canonical27780 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 4) (sourceB1979 + difference 4 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 4) (sourceB1979 + difference 4 5) sourceC1979) = raw27656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27656; decide +kernel
    rw [ha]
    exact (canonical27656 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1979 sourceB1979 sourceC1979
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1979, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1980 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceB1980 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1980 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1980 : Integer.Sparse Master := [(Sum.inr 1421, 1), (Sum.inr 1422, 1), (Sum.inr 1423, 1), (Sum.inr 1427, 1), (Sum.inr 1433, 1), (Sum.inr 2010, 1), (Sum.inr 2025, 1), (Sum.inr 2026, 1), (Sum.inr 2037, 1), (Sum.inr 2092, 1), (Sum.inr 2471, 1), (Sum.inr 2485, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2543, 1), (Sum.inr 2544, 1), (Sum.inr 2548, 1), (Sum.inr 2563, 1), (Sum.inr 2572, 1), (Sum.inr 2574, 1), (Sum.inr 2581, 1), (Sum.inr 2601, 1), (Sum.inr 2602, 1), (Sum.inr 2611, 1), (Sum.inr 2626, 1), (Sum.inr 2642, 1), (Sum.inr 2941, 1), (Sum.inr 2982, 1), (Sum.inr 2993, 1), (Sum.inr 3004, 1)]

theorem sourceEq1980 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1980 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1980 + difference 0 1) (sourceB1980 + difference 1 0) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA1980 + difference 0 1) (sourceB1980 + difference 1 0) sourceC1980) = raw28138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28138; decide +kernel
    rw [ha]
    exact (canonical28138 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1980 + difference 0 2) (sourceB1980 + difference 2 0) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2982) := by
    have ha : (tripleCharges (sourceA1980 + difference 0 2) (sourceB1980 + difference 2 0) sourceC1980) = raw28139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28139; decide +kernel
    rw [ha]
    exact (canonical28139 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1980 + difference 0 3) (sourceB1980 + difference 3 0) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3004) := by
    have ha : (tripleCharges (sourceA1980 + difference 0 3) (sourceB1980 + difference 3 0) sourceC1980) = raw28140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28140; decide +kernel
    rw [ha]
    exact (canonical28140 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1980 + difference 0 4) (sourceB1980 + difference 4 0) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2993) := by
    have ha : (tripleCharges (sourceA1980 + difference 0 4) (sourceB1980 + difference 4 0) sourceC1980) = raw28141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28141; decide +kernel
    rw [ha]
    exact (canonical28141 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1980 + difference 0 5) (sourceB1980 + difference 5 0) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1427) := by
    have ha : (tripleCharges (sourceA1980 + difference 0 5) (sourceB1980 + difference 5 0) sourceC1980) = raw28142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28142; decide +kernel
    rw [ha]
    exact (canonical28142 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1980 + difference 1 0) (sourceB1980 + difference 0 1) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA1980 + difference 1 0) (sourceB1980 + difference 0 1) sourceC1980) = raw28143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28143; decide +kernel
    rw [ha]
    exact (canonical28143 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1980 + difference 1 2) (sourceB1980 + difference 2 1) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2611) := by
    have ha : (tripleCharges (sourceA1980 + difference 1 2) (sourceB1980 + difference 2 1) sourceC1980) = raw28144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28144; decide +kernel
    rw [ha]
    exact (canonical28144 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1980 + difference 1 3) (sourceB1980 + difference 3 1) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2642) := by
    have ha : (tripleCharges (sourceA1980 + difference 1 3) (sourceB1980 + difference 3 1) sourceC1980) = raw28145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28145; decide +kernel
    rw [ha]
    exact (canonical28145 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1980 + difference 1 4) (sourceB1980 + difference 4 1) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2626) := by
    have ha : (tripleCharges (sourceA1980 + difference 1 4) (sourceB1980 + difference 4 1) sourceC1980) = raw28146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28146; decide +kernel
    rw [ha]
    exact (canonical28146 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1980 + difference 1 5) (sourceB1980 + difference 5 1) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1423) := by
    have ha : (tripleCharges (sourceA1980 + difference 1 5) (sourceB1980 + difference 5 1) sourceC1980) = raw28147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28147; decide +kernel
    rw [ha]
    exact (canonical28147 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1980 + difference 2 0) (sourceB1980 + difference 0 2) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA1980 + difference 2 0) (sourceB1980 + difference 0 2) sourceC1980) = raw28148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28148; decide +kernel
    rw [ha]
    exact (canonical28148 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1980 + difference 2 1) (sourceB1980 + difference 1 2) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA1980 + difference 2 1) (sourceB1980 + difference 1 2) sourceC1980) = raw28149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28149; decide +kernel
    rw [ha]
    exact (canonical28149 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1980 + difference 2 3) (sourceB1980 + difference 3 2) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA1980 + difference 2 3) (sourceB1980 + difference 3 2) sourceC1980) = raw28150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28150; decide +kernel
    rw [ha]
    exact (canonical28150 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1980 + difference 2 4) (sourceB1980 + difference 4 2) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2563) := by
    have ha : (tripleCharges (sourceA1980 + difference 2 4) (sourceB1980 + difference 4 2) sourceC1980) = raw28151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28151; decide +kernel
    rw [ha]
    exact (canonical28151 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1980 + difference 2 5) (sourceB1980 + difference 5 2) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1421) := by
    have ha : (tripleCharges (sourceA1980 + difference 2 5) (sourceB1980 + difference 5 2) sourceC1980) = raw28152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28152; decide +kernel
    rw [ha]
    exact (canonical28152 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1980 + difference 3 0) (sourceB1980 + difference 0 3) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA1980 + difference 3 0) (sourceB1980 + difference 0 3) sourceC1980) = raw28153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28153; decide +kernel
    rw [ha]
    exact (canonical28153 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1980 + difference 3 1) (sourceB1980 + difference 1 3) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA1980 + difference 3 1) (sourceB1980 + difference 1 3) sourceC1980) = raw28154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28154; decide +kernel
    rw [ha]
    exact (canonical28154 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1980 + difference 3 2) (sourceB1980 + difference 2 3) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2548) := by
    have ha : (tripleCharges (sourceA1980 + difference 3 2) (sourceB1980 + difference 2 3) sourceC1980) = raw28155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28155; decide +kernel
    rw [ha]
    exact (canonical28155 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1980 + difference 3 4) (sourceB1980 + difference 4 3) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2581) := by
    have ha : (tripleCharges (sourceA1980 + difference 3 4) (sourceB1980 + difference 4 3) sourceC1980) = raw28156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28156; decide +kernel
    rw [ha]
    exact (canonical28156 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1980 + difference 3 5) (sourceB1980 + difference 5 3) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1422) := by
    have ha : (tripleCharges (sourceA1980 + difference 3 5) (sourceB1980 + difference 5 3) sourceC1980) = raw28157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28157; decide +kernel
    rw [ha]
    exact (canonical28157 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1980 + difference 4 0) (sourceB1980 + difference 0 4) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA1980 + difference 4 0) (sourceB1980 + difference 0 4) sourceC1980) = raw28158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28158; decide +kernel
    rw [ha]
    exact (canonical28158 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1980 + difference 4 1) (sourceB1980 + difference 1 4) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA1980 + difference 4 1) (sourceB1980 + difference 1 4) sourceC1980) = raw28159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28159; decide +kernel
    rw [ha]
    exact (canonical28159 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1980 + difference 4 2) (sourceB1980 + difference 2 4) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2544) := by
    have ha : (tripleCharges (sourceA1980 + difference 4 2) (sourceB1980 + difference 2 4) sourceC1980) = raw28160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28160; decide +kernel
    rw [ha]
    exact (canonical28160 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1980 + difference 4 3) (sourceB1980 + difference 3 4) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2602) := by
    have ha : (tripleCharges (sourceA1980 + difference 4 3) (sourceB1980 + difference 3 4) sourceC1980) = raw28161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28161; decide +kernel
    rw [ha]
    exact (canonical28161 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1980 + difference 4 5) (sourceB1980 + difference 5 4) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1433) := by
    have ha : (tripleCharges (sourceA1980 + difference 4 5) (sourceB1980 + difference 5 4) sourceC1980) = raw28162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28162; decide +kernel
    rw [ha]
    exact (canonical28162 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1980 + difference 5 0) (sourceB1980 + difference 0 5) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1980 + difference 5 0) (sourceB1980 + difference 0 5) sourceC1980) = raw28163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28163; decide +kernel
    rw [ha]
    exact (canonical28163 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1980 + difference 5 1) (sourceB1980 + difference 1 5) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1980 + difference 5 1) (sourceB1980 + difference 1 5) sourceC1980) = raw28164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28164; decide +kernel
    rw [ha]
    exact (canonical28164 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1980 + difference 5 2) (sourceB1980 + difference 2 5) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA1980 + difference 5 2) (sourceB1980 + difference 2 5) sourceC1980) = raw28165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28165; decide +kernel
    rw [ha]
    exact (canonical28165 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1980 + difference 5 3) (sourceB1980 + difference 3 5) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1980 + difference 5 3) (sourceB1980 + difference 3 5) sourceC1980) = raw28166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28166; decide +kernel
    rw [ha]
    exact (canonical28166 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1980 + difference 5 4) (sourceB1980 + difference 4 5) sourceC1980) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA1980 + difference 5 4) (sourceB1980 + difference 4 5) sourceC1980) = raw28167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1980 sourceB1980 sourceC1980 difference raw28167; decide +kernel
    rw [ha]
    exact (canonical28167 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1980 sourceB1980 sourceC1980
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1980, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1981 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1981 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1981 : Charge := ![1, 1, 0, 2, -2, -2]
def sourceForm1981 : Integer.Sparse Master := [(Sum.inr 2390, 1), (Sum.inr 2393, 1), (Sum.inr 2395, 1), (Sum.inr 2404, 1), (Sum.inr 2678, 1), (Sum.inr 3771, 1), (Sum.inr 4088, -1)]

theorem sourceEq1981 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1981 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 0) (sourceB1981 + difference 0 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 0) (sourceB1981 + difference 0 0) sourceC1981) = raw28168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28168; decide +kernel
    rw [ha]
    exact (canonical28168 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 1) (sourceB1981 + difference 1 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2395) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 1) (sourceB1981 + difference 1 0) sourceC1981) = raw28169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28169; decide +kernel
    rw [ha]
    exact (canonical28169 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 2) (sourceB1981 + difference 2 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2390) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 2) (sourceB1981 + difference 2 0) sourceC1981) = raw28170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28170; decide +kernel
    rw [ha]
    exact (canonical28170 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 3) (sourceB1981 + difference 3 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2404) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 3) (sourceB1981 + difference 3 0) sourceC1981) = raw28171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28171; decide +kernel
    rw [ha]
    exact (canonical28171 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 4) (sourceB1981 + difference 4 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 4) (sourceB1981 + difference 4 0) sourceC1981) = raw28172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28172; decide +kernel
    rw [ha]
    exact (canonical28172 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1981 + difference 0 5) (sourceB1981 + difference 5 0) sourceC1981) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA1981 + difference 0 5) (sourceB1981 + difference 5 0) sourceC1981) = raw28173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1981 sourceB1981 sourceC1981 difference raw28173; decide +kernel
    rw [ha]
    exact (canonical28173 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1981 + sourceB1981) sourceC1981) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1981 + sourceB1981) sourceC1981) = raw28174 := by
      apply Matrix.ext; unfold doubleCharges sourceA1981 sourceB1981 sourceC1981 raw28174; decide +kernel
    rw [ha]
    exact (canonical28174 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1981 sourceB1981 sourceC1981
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1981, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1982 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1982 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1982 : Charge := ![1, 1, 0, 2, -2, -2]
def sourceForm1982 : Integer.Sparse Master := [(Sum.inr 2393, 1), (Sum.inr 2733, 1), (Sum.inr 2907, 1), (Sum.inr 2911, 1), (Sum.inr 3025, 1), (Sum.inr 3771, 1), (Sum.inr 4088, -1)]

theorem sourceEq1982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1982 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1982 + difference 0 5) (sourceB1982 + difference 5 0) sourceC1982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA1982 + difference 0 5) (sourceB1982 + difference 5 0) sourceC1982) = raw28173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1982 sourceB1982 sourceC1982 difference raw28173; decide +kernel
    rw [ha]
    exact (canonical28173 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1982 + difference 1 5) (sourceB1982 + difference 5 1) sourceC1982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA1982 + difference 1 5) (sourceB1982 + difference 5 1) sourceC1982) = raw28175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1982 sourceB1982 sourceC1982 difference raw28175; decide +kernel
    rw [ha]
    exact (canonical28175 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1982 + difference 2 5) (sourceB1982 + difference 5 2) sourceC1982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2907) := by
    have ha : (tripleCharges (sourceA1982 + difference 2 5) (sourceB1982 + difference 5 2) sourceC1982) = raw28176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1982 sourceB1982 sourceC1982 difference raw28176; decide +kernel
    rw [ha]
    exact (canonical28176 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1982 + difference 3 5) (sourceB1982 + difference 5 3) sourceC1982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2733) := by
    have ha : (tripleCharges (sourceA1982 + difference 3 5) (sourceB1982 + difference 5 3) sourceC1982) = raw28177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1982 sourceB1982 sourceC1982 difference raw28177; decide +kernel
    rw [ha]
    exact (canonical28177 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1982 + difference 4 5) (sourceB1982 + difference 5 4) sourceC1982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2911) := by
    have ha : (tripleCharges (sourceA1982 + difference 4 5) (sourceB1982 + difference 5 4) sourceC1982) = raw28178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1982 sourceB1982 sourceC1982 difference raw28178; decide +kernel
    rw [ha]
    exact (canonical28178 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1982 + difference 5 5) (sourceB1982 + difference 5 5) sourceC1982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA1982 + difference 5 5) (sourceB1982 + difference 5 5) sourceC1982) = raw28168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1982 sourceB1982 sourceC1982 difference raw28168; decide +kernel
    rw [ha]
    exact (canonical28168 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1982 + sourceB1982) sourceC1982) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1982 + sourceB1982) sourceC1982) = raw28174 := by
      apply Matrix.ext; unfold doubleCharges sourceA1982 sourceB1982 sourceC1982 raw28174; decide +kernel
    rw [ha]
    exact (canonical28174 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1982 sourceB1982 sourceC1982
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1982, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1983 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1983 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1983 : Charge := ![1, 1, 0, 2, -1, -3]
def sourceForm1983 : Integer.Sparse Master := [(Sum.inr 887, 1), (Sum.inr 1778, 1), (Sum.inr 1867, 1), (Sum.inr 1915, 1), (Sum.inr 1926, 1), (Sum.inr 1947, 1), (Sum.inr 4080, -1)]

theorem sourceEq1983 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1983 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1983 + difference 0 3) (sourceB1983 + difference 3 0) sourceC1983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1947) := by
    have ha : (tripleCharges (sourceA1983 + difference 0 3) (sourceB1983 + difference 3 0) sourceC1983) = raw28179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1983 sourceB1983 sourceC1983 difference raw28179; decide +kernel
    rw [ha]
    exact (canonical28179 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1983 + difference 1 3) (sourceB1983 + difference 3 1) sourceC1983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA1983 + difference 1 3) (sourceB1983 + difference 3 1) sourceC1983) = raw28180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1983 sourceB1983 sourceC1983 difference raw28180; decide +kernel
    rw [ha]
    exact (canonical28180 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1983 + difference 2 3) (sourceB1983 + difference 3 2) sourceC1983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1867) := by
    have ha : (tripleCharges (sourceA1983 + difference 2 3) (sourceB1983 + difference 3 2) sourceC1983) = raw28181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1983 sourceB1983 sourceC1983 difference raw28181; decide +kernel
    rw [ha]
    exact (canonical28181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1983 + difference 3 3) (sourceB1983 + difference 3 3) sourceC1983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA1983 + difference 3 3) (sourceB1983 + difference 3 3) sourceC1983) = raw28182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1983 sourceB1983 sourceC1983 difference raw28182; decide +kernel
    rw [ha]
    exact (canonical28182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1983 + difference 4 3) (sourceB1983 + difference 3 4) sourceC1983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1778) := by
    have ha : (tripleCharges (sourceA1983 + difference 4 3) (sourceB1983 + difference 3 4) sourceC1983) = raw28183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1983 sourceB1983 sourceC1983 difference raw28183; decide +kernel
    rw [ha]
    exact (canonical28183 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1983 + difference 5 3) (sourceB1983 + difference 3 5) sourceC1983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1983 + difference 5 3) (sourceB1983 + difference 3 5) sourceC1983) = raw28184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1983 sourceB1983 sourceC1983 difference raw28184; decide +kernel
    rw [ha]
    exact (canonical28184 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1983 + sourceB1983) sourceC1983) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1983 + sourceB1983) sourceC1983) = raw28185 := by
      apply Matrix.ext; unfold doubleCharges sourceA1983 sourceB1983 sourceC1983 raw28185; decide +kernel
    rw [ha]
    exact (canonical28185 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1983 sourceB1983 sourceC1983
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1983, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
