import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5239 node5239Labels = 0 := by
  exact mixedMoment_alpha B hF node5239 node5239Labels 1 permutation212
    (by decide +kernel)

theorem zero5242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5242 node5242Labels = 0 := by
  exact mixedMoment_alpha B hF node5242 node5242Labels 1 permutation212
    (by decide +kernel)

theorem zero5246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5246 node5246Labels = 0 := by
  exact mixedMoment_alpha B hF node5246 node5246Labels 1 permutation216
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
