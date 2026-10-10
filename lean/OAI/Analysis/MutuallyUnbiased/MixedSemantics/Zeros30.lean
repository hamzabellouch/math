import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1943 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1943 node1943Labels = 0 := by
  exact mixedMoment_order_one B hB node1943 node1943Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1944 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1944 node1944Labels = 0 := by
  exact mixedMoment_order_one B hB node1944 node1944Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1945 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1945 node1945Labels = 0 := by
  exact mixedMoment_order_one B hB node1945 node1945Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1947 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1947 node1947Labels = 0 := by
  exact mixedMoment_order_one B hB node1947 node1947Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1950 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1950 node1950Labels = 0 := by
  exact mixedMoment_order_one B hB node1950 node1950Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1953 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1953 node1953Labels = 0 := by
  exact mixedMoment_order_one B hB node1953 node1953Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
