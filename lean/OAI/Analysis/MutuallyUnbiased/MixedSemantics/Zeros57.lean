import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3650 node3650Labels = 0 := by
  exact mixedMoment_order_one B hB node3650 node3650Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3652 node3652Labels = 0 := by
  exact mixedMoment_order_one B hB node3652 node3652Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3654 node3654Labels = 0 := by
  exact mixedMoment_order_one B hB node3654 node3654Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3664 node3664Labels = 0 := by
  exact mixedMoment_order_one B hB node3664 node3664Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3665 node3665Labels = 0 := by
  exact mixedMoment_order_one B hB node3665 node3665Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3667 node3667Labels = 0 := by
  exact mixedMoment_order_one B hB node3667 node3667Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3682 node3682Labels = 0 := by
  exact mixedMoment_order_one B hB node3682 node3682Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3704 node3704Labels = 0 := by
  exact mixedMoment_order_one B hB node3704 node3704Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3707 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3707 node3707Labels = 0 := by
  exact mixedMoment_order_one B hB node3707 node3707Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
