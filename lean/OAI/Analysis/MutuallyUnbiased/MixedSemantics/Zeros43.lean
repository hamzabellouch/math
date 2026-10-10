import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2752 node2752Labels = 0 := by
  exact mixedMoment_alpha B hF node2752 node2752Labels 1 permutation152
    (by decide +kernel)

theorem zero2785 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2785 node2785Labels = 0 := by
  exact mixedMoment_order_one B hB node2785 node2785Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2786 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2786 node2786Labels = 0 := by
  exact mixedMoment_order_one B hB node2786 node2786Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2787 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2787 node2787Labels = 0 := by
  exact mixedMoment_order_one B hB node2787 node2787Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2790 node2790Labels = 0 := by
  exact mixedMoment_order_one B hB node2790 node2790Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
