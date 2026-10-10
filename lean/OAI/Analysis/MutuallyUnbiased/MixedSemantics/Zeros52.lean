import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3328 node3328Labels = 0 := by
  exact mixedMoment_order_one B hB node3328 node3328Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3331 node3331Labels = 0 := by
  exact mixedMoment_order_one B hB node3331 node3331Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3338 node3338Labels = 0 := by
  exact mixedMoment_alpha B hF node3338 node3338Labels 1 permutation434
    (by decide +kernel)

theorem zero3339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3339 node3339Labels = 0 := by
  exact mixedMoment_alpha B hF node3339 node3339Labels 1 permutation437
    (by decide +kernel)

theorem zero3351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3351 node3351Labels = 0 := by
  exact mixedMoment_alpha B hF node3351 node3351Labels 1 permutation446
    (by decide +kernel)

theorem zero3356 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3356 node3356Labels = 0 := by
  exact mixedMoment_order_one B hB node3356 node3356Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3361 node3361Labels = 0 := by
  exact mixedMoment_order_one B hB node3361 node3361Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
