import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1482 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1482 node1482Labels = 0 := by
  exact mixedMoment_order_one B hB node1482 node1482Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero1483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1483 node1483Labels = 0 := by
  exact mixedMoment_order_one B hB node1483 node1483Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero1484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1484 node1484Labels = 0 := by
  exact mixedMoment_order_one B hB node1484 node1484Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1485 node1485Labels = 0 := by
  exact mixedMoment_order_one B hB node1485 node1485Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero1486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1486 node1486Labels = 0 := by
  exact mixedMoment_order_one B hB node1486 node1486Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero1487 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1487 node1487Labels = 0 := by
  exact mixedMoment_order_one B hB node1487 node1487Labels 2
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
