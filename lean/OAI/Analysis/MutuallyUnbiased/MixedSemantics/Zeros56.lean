import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3601 node3601Labels = 0 := by
  exact mixedMoment_alpha B hF node3601 node3601Labels 1 permutation485
    (by decide +kernel)

theorem zero3618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3618 node3618Labels = 0 := by
  exact mixedMoment_alpha B hF node3618 node3618Labels 1 permutation434
    (by decide +kernel)

theorem zero3628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3628 node3628Labels = 0 := by
  exact mixedMoment_order_one B hB node3628 node3628Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3629 node3629Labels = 0 := by
  exact mixedMoment_order_one B hB node3629 node3629Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3635 node3635Labels = 0 := by
  exact mixedMoment_order_one B hB node3635 node3635Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3636 node3636Labels = 0 := by
  exact mixedMoment_order_one B hB node3636 node3636Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3637 node3637Labels = 0 := by
  exact mixedMoment_order_one B hB node3637 node3637Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3644 node3644Labels = 0 := by
  exact mixedMoment_order_one B hB node3644 node3644Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
