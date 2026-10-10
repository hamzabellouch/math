import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2053 node2053Labels = 0 := by
  exact mixedMoment_order_one B hB node2053 node2053Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2056 node2056Labels = 0 := by
  exact mixedMoment_order_one B hB node2056 node2056Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2057 node2057Labels = 0 := by
  exact mixedMoment_order_one B hB node2057 node2057Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = 0 := by
  exact mixedMoment_order_one B hB node2060 node2060Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2066 node2066Labels = 0 := by
  exact mixedMoment_order_one B hB node2066 node2066Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
