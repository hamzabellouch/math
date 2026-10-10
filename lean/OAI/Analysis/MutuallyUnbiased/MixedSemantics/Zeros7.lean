import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node464 node464Labels = 0 := by
  exact mixedMoment_order_one B hB node464 node464Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node465 node465Labels = 0 := by
  exact mixedMoment_order_one B hB node465 node465Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node466 node466Labels = 0 := by
  exact mixedMoment_order_one B hB node466 node466Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node469 node469Labels = 0 := by
  exact mixedMoment_order_one B hB node469 node469Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero482 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node482 node482Labels = 0 := by
  exact mixedMoment_order_one B hB node482 node482Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node495 node495Labels = 0 := by
  exact mixedMoment_order_one B hB node495 node495Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node506 node506Labels = 0 := by
  exact mixedMoment_order_one B hB node506 node506Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
