import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4641 node4641Labels = 0 := by
  exact mixedMoment_order_one B hB node4641 node4641Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4643 node4643Labels = 0 := by
  exact mixedMoment_order_one B hB node4643 node4643Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4646 node4646Labels = 0 := by
  exact mixedMoment_order_one B hB node4646 node4646Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4647 node4647Labels = 0 := by
  exact mixedMoment_order_one B hB node4647 node4647Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4649 node4649Labels = 0 := by
  exact mixedMoment_order_one B hB node4649 node4649Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4652 node4652Labels = 0 := by
  exact mixedMoment_order_one B hB node4652 node4652Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4655 node4655Labels = 0 := by
  exact mixedMoment_order_one B hB node4655 node4655Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4656 node4656Labels = 0 := by
  exact mixedMoment_order_one B hB node4656 node4656Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
