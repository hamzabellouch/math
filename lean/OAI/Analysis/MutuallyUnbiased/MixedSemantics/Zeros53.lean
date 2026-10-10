import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3403 node3403Labels = 0 := by
  exact mixedMoment_alpha B hF node3403 node3403Labels 1 permutation485
    (by decide +kernel)

theorem zero3405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3405 node3405Labels = 0 := by
  exact mixedMoment_alpha B hF node3405 node3405Labels 1 permutation484
    (by decide +kernel)

theorem zero3409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3409 node3409Labels = 0 := by
  exact mixedMoment_alpha B hF node3409 node3409Labels 1 permutation487
    (by decide +kernel)

theorem zero3424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3424 node3424Labels = 0 := by
  exact mixedMoment_order_one B hB node3424 node3424Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3435 node3435Labels = 0 := by
  exact mixedMoment_order_one B hB node3435 node3435Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3439 node3439Labels = 0 := by
  exact mixedMoment_order_one B hB node3439 node3439Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
