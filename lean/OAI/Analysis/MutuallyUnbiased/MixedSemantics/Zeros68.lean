import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4390 node4390Labels = 0 := by
  exact mixedMoment_alpha B hF node4390 node4390Labels 1 permutation200
    (by decide +kernel)

theorem zero4393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4393 node4393Labels = 0 := by
  exact mixedMoment_alpha B hF node4393 node4393Labels 1 permutation200
    (by decide +kernel)

theorem zero4395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4395 node4395Labels = 0 := by
  exact mixedMoment_alpha B hF node4395 node4395Labels 1 permutation203
    (by decide +kernel)

theorem zero4397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4397 node4397Labels = 0 := by
  exact mixedMoment_alpha B hF node4397 node4397Labels 1 permutation202
    (by decide +kernel)

theorem zero4415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4415 node4415Labels = 0 := by
  exact mixedMoment_alpha B hF node4415 node4415Labels 1 permutation216
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
