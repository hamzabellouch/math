import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4422 node4422Labels = 0 := by
  exact mixedMoment_order_one B hB node4422 node4422Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4423 node4423Labels = 0 := by
  exact mixedMoment_order_one B hB node4423 node4423Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4426 node4426Labels = 0 := by
  exact mixedMoment_order_one B hB node4426 node4426Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4432 node4432Labels = 0 := by
  exact mixedMoment_order_one B hB node4432 node4432Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4438 node4438Labels = 0 := by
  exact mixedMoment_alpha B hF node4438 node4438Labels 1 permutation152
    (by decide +kernel)

theorem zero4455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4455 node4455Labels = 0 := by
  exact mixedMoment_alpha B hF node4455 node4455Labels 1 permutation161
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
