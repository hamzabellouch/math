import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4034 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4034 node4034Labels = 0 := by
  exact mixedMoment_order_one B hB node4034 node4034Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero4035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4035 node4035Labels = 0 := by
  exact mixedMoment_order_one B hB node4035 node4035Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero4036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4036 node4036Labels = 0 := by
  exact mixedMoment_order_one B hB node4036 node4036Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero4037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4037 node4037Labels = 0 := by
  exact mixedMoment_order_one B hB node4037 node4037Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero4038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4038 node4038Labels = 0 := by
  exact mixedMoment_order_one B hB node4038 node4038Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero4040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4040 node4040Labels = 0 := by
  exact mixedMoment_order_one B hB node4040 node4040Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero4044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4044 node4044Labels = 0 := by
  exact mixedMoment_alpha B hF node4044 node4044Labels 0 permutation499
    (by decide +kernel)

theorem zero4048 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4048 node4048Labels = 0 := by
  exact mixedMoment_order_one B hB node4048 node4048Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4049 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4049 node4049Labels = 0 := by
  exact mixedMoment_order_one B hB node4049 node4049Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4052 node4052Labels = 0 := by
  exact mixedMoment_order_one B hB node4052 node4052Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4054 node4054Labels = 0 := by
  exact mixedMoment_order_one B hB node4054 node4054Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero4055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4055 node4055Labels = 0 := by
  exact mixedMoment_order_one B hB node4055 node4055Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4095 node4095Labels = 0 := by
  exact mixedMoment_alpha B hF node4095 node4095Labels 0 permutation499
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
