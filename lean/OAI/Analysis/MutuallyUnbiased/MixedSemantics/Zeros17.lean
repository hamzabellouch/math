import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1089 node1089Labels = 0 := by
  exact mixedMoment_order_one B hB node1089 node1089Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1095 node1095Labels = 0 := by
  exact mixedMoment_order_one B hB node1095 node1095Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1096 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1096 node1096Labels = 0 := by
  exact mixedMoment_order_one B hB node1096 node1096Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
