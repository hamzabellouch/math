import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2304 node2304Labels = 0 := by
  exact mixedMoment_order_one B hB node2304 node2304Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2309 node2309Labels = 0 := by
  exact mixedMoment_order_one B hB node2309 node2309Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2312 node2312Labels = 0 := by
  exact mixedMoment_order_one B hB node2312 node2312Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2319 node2319Labels = 0 := by
  exact mixedMoment_alpha B hF node2319 node2319Labels 1 permutation152
    (by decide +kernel)

theorem zero2322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2322 node2322Labels = 0 := by
  exact mixedMoment_alpha B hF node2322 node2322Labels 1 permutation152
    (by decide +kernel)

theorem zero2331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2331 node2331Labels = 0 := by
  exact mixedMoment_alpha B hF node2331 node2331Labels 1 permutation160
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
