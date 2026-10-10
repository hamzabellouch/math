import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2510 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2510 node2510Labels = 0 := by
  exact mixedMoment_order_one B hB node2510 node2510Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2511 node2511Labels = 0 := by
  exact mixedMoment_order_one B hB node2511 node2511Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2514 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2514 node2514Labels = 0 := by
  exact mixedMoment_order_one B hB node2514 node2514Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2517 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2517 node2517Labels = 0 := by
  exact mixedMoment_order_one B hB node2517 node2517Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2523 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2523 node2523Labels = 0 := by
  exact mixedMoment_order_one B hB node2523 node2523Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2540 node2540Labels = 0 := by
  exact mixedMoment_alpha B hF node2540 node2540Labels 1 permutation161
    (by decide +kernel)

theorem zero2542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2542 node2542Labels = 0 := by
  exact mixedMoment_alpha B hF node2542 node2542Labels 1 permutation158
    (by decide +kernel)

theorem zero2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2546 node2546Labels = 0 := by
  exact mixedMoment_alpha B hF node2546 node2546Labels 1 permutation158
    (by decide +kernel)

theorem zero2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2552 node2552Labels = 0 := by
  exact mixedMoment_alpha B hF node2552 node2552Labels 1 permutation161
    (by decide +kernel)

theorem zero2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2554 node2554Labels = 0 := by
  exact mixedMoment_alpha B hF node2554 node2554Labels 1 permutation160
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
