import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue2 : Sparse (Fin 909) := [(0, (1 / 6)), (2, (5 / 6))]

theorem singlePair2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2 node2Labels = Sparse.eval singlePairValue2 (familyPairVector B) := by
  have hp := single_label_two B hB node2
  have hl : node2Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node2 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node2 (EqualityPatterns.family2.label 0) = PairSemantics.raw7978 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext
      unfold node2 PairSemantics.raw7978
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7978 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node2 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node2 (EqualityPatterns.family2.label 1) = PairSemantics.raw926 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext
      unfold node2 PairSemantics.raw926
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical926 hH).trans (PairSemantics.sound3 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue2, PairSemantics.value0, PairSemantics.value3, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
