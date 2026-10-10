import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue7 : Sparse (Fin 909) := [(0, (19 / 72)), (1, (5 / 72))]

theorem singlePair7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node7 node7Labels = Sparse.eval singlePairValue7 (familyPairVector B) := by
  have hp := single_label_two B hB node7
  have hl : node7Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node7 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node7 (EqualityPatterns.family2.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext; unfold node7 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node7 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node7 (EqualityPatterns.family2.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext; unfold node7 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue7, PairSemantics.value0, PairSemantics.value65, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
