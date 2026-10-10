import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2894 node2894Labels = 0 := by
  exact mixedMoment_alpha B hF node2894 node2894Labels 2 permutation152
    (by decide +kernel)

theorem zero2897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2897 node2897Labels = 0 := by
  exact mixedMoment_alpha B hF node2897 node2897Labels 2 permutation152
    (by decide +kernel)

theorem zero2914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2914 node2914Labels = 0 := by
  exact mixedMoment_alpha B hF node2914 node2914Labels 2 permutation152
    (by decide +kernel)

theorem zero2917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2917 node2917Labels = 0 := by
  exact mixedMoment_alpha B hF node2917 node2917Labels 2 permutation152
    (by decide +kernel)

theorem zero2927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2927 node2927Labels = 0 := by
  exact mixedMoment_alpha B hF node2927 node2927Labels 2 permutation152
    (by decide +kernel)

theorem zero2934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2934 node2934Labels = 0 := by
  exact mixedMoment_alpha B hF node2934 node2934Labels 2 permutation158
    (by decide +kernel)

theorem zero2940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2940 node2940Labels = 0 := by
  exact mixedMoment_alpha B hF node2940 node2940Labels 2 permutation161
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
