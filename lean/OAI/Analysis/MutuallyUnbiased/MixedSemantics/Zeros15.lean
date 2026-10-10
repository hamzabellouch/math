import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node971 node971Labels = 0 := by
  exact mixedMoment_alpha B hF node971 node971Labels 1 permutation200
    (by decide +kernel)

theorem zero974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node974 node974Labels = 0 := by
  exact mixedMoment_alpha B hF node974 node974Labels 1 permutation200
    (by decide +kernel)

theorem zero976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node976 node976Labels = 0 := by
  exact mixedMoment_alpha B hF node976 node976Labels 1 permutation203
    (by decide +kernel)

theorem zero978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node978 node978Labels = 0 := by
  exact mixedMoment_alpha B hF node978 node978Labels 1 permutation202
    (by decide +kernel)

theorem zero996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node996 node996Labels = 0 := by
  exact mixedMoment_alpha B hF node996 node996Labels 1 permutation216
    (by decide +kernel)

theorem zero1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1003 node1003Labels = 0 := by
  exact mixedMoment_order_one B hB node1003 node1003Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1004 node1004Labels = 0 := by
  exact mixedMoment_order_one B hB node1004 node1004Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1007 node1007Labels = 0 := by
  exact mixedMoment_order_one B hB node1007 node1007Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1013 node1013Labels = 0 := by
  exact mixedMoment_order_one B hB node1013 node1013Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1020 node1020Labels = 0 := by
  exact mixedMoment_alpha B hF node1020 node1020Labels 1 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
