import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4708 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4708 node4708Labels = 0 := by
  exact mixedMoment_order_one B hB node4708 node4708Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4711 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4711 node4711Labels = 0 := by
  exact mixedMoment_order_one B hB node4711 node4711Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4712 node4712Labels = 0 := by
  exact mixedMoment_order_one B hB node4712 node4712Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4715 node4715Labels = 0 := by
  exact mixedMoment_order_one B hB node4715 node4715Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4718 node4718Labels = 0 := by
  exact mixedMoment_order_one B hB node4718 node4718Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
