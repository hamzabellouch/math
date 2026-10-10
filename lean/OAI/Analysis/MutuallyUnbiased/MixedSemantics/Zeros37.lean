import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2377 node2377Labels = 0 := by
  exact mixedMoment_alpha B hF node2377 node2377Labels 1 permutation200
    (by decide +kernel)

theorem zero2380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2380 node2380Labels = 0 := by
  exact mixedMoment_alpha B hF node2380 node2380Labels 1 permutation200
    (by decide +kernel)

theorem zero2381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2381 node2381Labels = 0 := by
  exact mixedMoment_alpha B hF node2381 node2381Labels 1 permutation203
    (by decide +kernel)

theorem zero2402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2402 node2402Labels = 0 := by
  exact mixedMoment_order_one B hB node2402 node2402Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2403 node2403Labels = 0 := by
  exact mixedMoment_order_one B hB node2403 node2403Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2411 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2411 node2411Labels = 0 := by
  exact mixedMoment_order_one B hB node2411 node2411Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2414 node2414Labels = 0 := by
  exact mixedMoment_order_one B hB node2414 node2414Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2415 node2415Labels = 0 := by
  exact mixedMoment_order_one B hB node2415 node2415Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2418 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2418 node2418Labels = 0 := by
  exact mixedMoment_order_one B hB node2418 node2418Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
