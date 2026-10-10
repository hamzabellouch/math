import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3844 node3844Labels = 0 := by
  exact mixedMoment_order_one B hB node3844 node3844Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3859 node3859Labels = 0 := by
  exact mixedMoment_order_one B hB node3859 node3859Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = 0 := by
  exact mixedMoment_order_one B hB node3860 node3860Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3861 node3861Labels = 0 := by
  exact mixedMoment_order_one B hB node3861 node3861Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
