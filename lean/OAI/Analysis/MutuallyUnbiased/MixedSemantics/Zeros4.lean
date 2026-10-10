import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node265 node265Labels = 0 := by
  exact mixedMoment_order_one B hB node265 node265Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node266 node266Labels = 0 := by
  exact mixedMoment_order_one B hB node266 node266Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node267 node267Labels = 0 := by
  exact mixedMoment_order_one B hB node267 node267Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node272 node272Labels = 0 := by
  exact mixedMoment_order_one B hB node272 node272Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
