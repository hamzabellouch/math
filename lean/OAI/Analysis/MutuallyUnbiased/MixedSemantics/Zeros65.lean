import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4209 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4209 node4209Labels = 0 := by
  exact mixedMoment_order_one B hB node4209 node4209Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4211 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4211 node4211Labels = 0 := by
  exact mixedMoment_order_one B hB node4211 node4211Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4214 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4214 node4214Labels = 0 := by
  exact mixedMoment_order_one B hB node4214 node4214Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4215 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4215 node4215Labels = 0 := by
  exact mixedMoment_order_one B hB node4215 node4215Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4216 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4216 node4216Labels = 0 := by
  exact mixedMoment_order_one B hB node4216 node4216Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4218 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4218 node4218Labels = 0 := by
  exact mixedMoment_order_one B hB node4218 node4218Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4221 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4221 node4221Labels = 0 := by
  exact mixedMoment_order_one B hB node4221 node4221Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4222 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4222 node4222Labels = 0 := by
  exact mixedMoment_order_one B hB node4222 node4222Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
