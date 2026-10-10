import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4994 node4994Labels = 0 := by
  exact mixedMoment_alpha B hF node4994 node4994Labels 1 permutation200
    (by decide +kernel)

theorem zero4995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4995 node4995Labels = 0 := by
  exact mixedMoment_alpha B hF node4995 node4995Labels 1 permutation203
    (by decide +kernel)

theorem zero4997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4997 node4997Labels = 0 := by
  exact mixedMoment_alpha B hF node4997 node4997Labels 1 permutation202
    (by decide +kernel)

theorem zero5012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5012 node5012Labels = 0 := by
  exact mixedMoment_alpha B hF node5012 node5012Labels 1 permutation216
    (by decide +kernel)

theorem zero5017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5017 node5017Labels = 0 := by
  exact mixedMoment_order_one B hB node5017 node5017Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5024 node5024Labels = 0 := by
  exact mixedMoment_order_one B hB node5024 node5024Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5025 node5025Labels = 0 := by
  exact mixedMoment_order_one B hB node5025 node5025Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5026 node5026Labels = 0 := by
  exact mixedMoment_order_one B hB node5026 node5026Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5029 node5029Labels = 0 := by
  exact mixedMoment_order_one B hB node5029 node5029Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
