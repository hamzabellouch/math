import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2953 node2953Labels = 0 := by
  exact mixedMoment_alpha B hF node2953 node2953Labels 2 permutation152
    (by decide +kernel)

theorem zero2993 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2993 node2993Labels = 0 := by
  exact mixedMoment_order_one B hB node2993 node2993Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero2999 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2999 node2999Labels = 0 := by
  exact mixedMoment_order_one B hB node2999 node2999Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3000 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3000 node3000Labels = 0 := by
  exact mixedMoment_order_one B hB node3000 node3000Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3001 node3001Labels = 0 := by
  exact mixedMoment_order_one B hB node3001 node3001Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3002 node3002Labels = 0 := by
  exact mixedMoment_order_one B hB node3002 node3002Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3004 node3004Labels = 0 := by
  exact mixedMoment_order_one B hB node3004 node3004Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3006 node3006Labels = 0 := by
  exact mixedMoment_order_one B hB node3006 node3006Labels 2
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
