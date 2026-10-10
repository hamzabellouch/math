import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4929 node4929Labels = 0 := by
  exact mixedMoment_alpha B hF node4929 node4929Labels 1 permutation152
    (by decide +kernel)

theorem zero4932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4932 node4932Labels = 0 := by
  exact mixedMoment_alpha B hF node4932 node4932Labels 1 permutation152
    (by decide +kernel)

theorem zero4938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4938 node4938Labels = 0 := by
  exact mixedMoment_alpha B hF node4938 node4938Labels 1 permutation161
    (by decide +kernel)

theorem zero4940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4940 node4940Labels = 0 := by
  exact mixedMoment_alpha B hF node4940 node4940Labels 1 permutation160
    (by decide +kernel)

theorem zero4991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4991 node4991Labels = 0 := by
  exact mixedMoment_alpha B hF node4991 node4991Labels 1 permutation200
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
