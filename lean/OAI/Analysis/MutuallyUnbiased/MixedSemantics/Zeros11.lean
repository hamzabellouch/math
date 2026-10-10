import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node712 node712Labels = 0 := by
  exact mixedMoment_order_one B hB node712 node712Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node714 node714Labels = 0 := by
  exact mixedMoment_order_one B hB node714 node714Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero717 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node717 node717Labels = 0 := by
  exact mixedMoment_order_one B hB node717 node717Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node718 node718Labels = 0 := by
  exact mixedMoment_order_one B hB node718 node718Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node722 node722Labels = 0 := by
  exact mixedMoment_order_one B hB node722 node722Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node723 node723Labels = 0 := by
  exact mixedMoment_order_one B hB node723 node723Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node728 node728Labels = 0 := by
  exact mixedMoment_order_one B hB node728 node728Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node766 node766Labels = 0 := by
  exact mixedMoment_order_one B hB node766 node766Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node767 node767Labels = 0 := by
  exact mixedMoment_order_one B hB node767 node767Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
