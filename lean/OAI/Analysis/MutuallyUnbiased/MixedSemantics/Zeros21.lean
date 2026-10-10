import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1345 node1345Labels = 0 := by
  exact mixedMoment_alpha B hF node1345 node1345Labels 2 permutation161
    (by decide +kernel)

theorem zero1379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1379 node1379Labels = 0 := by
  exact mixedMoment_alpha B hF node1379 node1379Labels 2 permutation152
    (by decide +kernel)

theorem zero1381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1381 node1381Labels = 0 := by
  exact mixedMoment_alpha B hF node1381 node1381Labels 2 permutation152
    (by decide +kernel)

theorem zero1386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1386 node1386Labels = 0 := by
  exact mixedMoment_alpha B hF node1386 node1386Labels 2 permutation152
    (by decide +kernel)

theorem zero1393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1393 node1393Labels = 0 := by
  exact mixedMoment_alpha B hF node1393 node1393Labels 2 permutation158
    (by decide +kernel)

theorem zero1398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1398 node1398Labels = 0 := by
  exact mixedMoment_alpha B hF node1398 node1398Labels 2 permutation161
    (by decide +kernel)

theorem zero1405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1405 node1405Labels = 0 := by
  exact mixedMoment_alpha B hF node1405 node1405Labels 2 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
