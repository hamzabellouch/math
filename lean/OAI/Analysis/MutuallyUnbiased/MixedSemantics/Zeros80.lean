import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5127 node5127Labels = 0 := by
  exact mixedMoment_alpha B hF node5127 node5127Labels 1 permutation158
    (by decide +kernel)

theorem zero5130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5130 node5130Labels = 0 := by
  exact mixedMoment_alpha B hF node5130 node5130Labels 1 permutation158
    (by decide +kernel)

theorem zero5133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5133 node5133Labels = 0 := by
  exact mixedMoment_alpha B hF node5133 node5133Labels 1 permutation161
    (by decide +kernel)

theorem zero5135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5135 node5135Labels = 0 := by
  exact mixedMoment_alpha B hF node5135 node5135Labels 1 permutation160
    (by decide +kernel)

theorem zero5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5148 node5148Labels = 0 := by
  exact mixedMoment_alpha B hF node5148 node5148Labels 1 permutation152
    (by decide +kernel)

theorem zero5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5166 node5166Labels = 0 := by
  exact mixedMoment_alpha B hF node5166 node5166Labels 1 permutation161
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
