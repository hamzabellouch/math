import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node512 node512Labels = 0 := by
  exact mixedMoment_alpha B hF node512 node512Labels 1 permutation200
    (by decide +kernel)

theorem zero515 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node515 node515Labels = 0 := by
  exact mixedMoment_order_one B hB node515 node515Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node518 node518Labels = 0 := by
  exact mixedMoment_alpha B hF node518 node518Labels 2 permutation152
    (by decide +kernel)

theorem zero524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node524 node524Labels = 0 := by
  exact mixedMoment_alpha B hF node524 node524Labels 1 permutation212
    (by decide +kernel)

theorem zero525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node525 node525Labels = 0 := by
  exact mixedMoment_alpha B hF node525 node525Labels 2 permutation152
    (by decide +kernel)

theorem zero529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node529 node529Labels = 0 := by
  exact mixedMoment_order_one B hB node529 node529Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero532 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node532 node532Labels = 0 := by
  exact mixedMoment_order_one B hB node532 node532Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero534 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node534 node534Labels = 0 := by
  exact mixedMoment_order_one B hB node534 node534Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero558 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node558 node558Labels = 0 := by
  exact mixedMoment_order_one B hB node558 node558Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node561 node561Labels = 0 := by
  exact mixedMoment_order_one B hB node561 node561Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
