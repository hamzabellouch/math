import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node389 node389Labels = 0 := by
  exact mixedMoment_order_one B hB node389 node389Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node396 node396Labels = 0 := by
  exact mixedMoment_alpha B hF node396 node396Labels 1 permutation152
    (by decide +kernel)

theorem zero417 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node417 node417Labels = 0 := by
  exact mixedMoment_order_one B hB node417 node417Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero418 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node418 node418Labels = 0 := by
  exact mixedMoment_order_one B hB node418 node418Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero419 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node419 node419Labels = 0 := by
  exact mixedMoment_order_one B hB node419 node419Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node422 node422Labels = 0 := by
  exact mixedMoment_order_one B hB node422 node422Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
