import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue4 : Sparse (Fin 909) := [(0, (11 / 72)), (1, (-5 / 36)), (2, (5 / 72))]

theorem singlePair4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4 node4Labels = Sparse.eval singlePairValue4 (familyPairVector B) := by
  have hp := single_label_two B hB node4
  have hl : node4Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node4 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node4 (EqualityPatterns.family2.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext
      unfold node4 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node4 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node4 (EqualityPatterns.family2.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext
      unfold node4 PairSemantics.raw5141
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue4, PairSemantics.value0, PairSemantics.value46, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
