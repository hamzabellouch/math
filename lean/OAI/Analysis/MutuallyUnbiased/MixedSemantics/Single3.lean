import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue3 : Sparse (Fin 909) := [(0, (1 / 9)), (1, (5 / 24)), (2, (-5 / 72))]

theorem singlePair3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3 node3Labels = Sparse.eval singlePairValue3 (familyPairVector B) := by
  have hp := single_label_two B hB node3
  have hl : node3Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node3 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node3 (EqualityPatterns.family2.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext; unfold node3 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node3 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node3 (EqualityPatterns.family2.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext; unfold node3 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue3, PairSemantics.value0, PairSemantics.value232, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
