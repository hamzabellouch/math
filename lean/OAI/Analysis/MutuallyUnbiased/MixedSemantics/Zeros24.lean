import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1557 node1557Labels = 0 := by
  exact mixedMoment_order_one B hB node1557 node1557Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1560 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1560 node1560Labels = 0 := by
  exact mixedMoment_order_one B hB node1560 node1560Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1571 node1571Labels = 0 := by
  exact mixedMoment_order_one B hB node1571 node1571Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1572 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1572 node1572Labels = 0 := by
  exact mixedMoment_order_one B hB node1572 node1572Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1574 node1574Labels = 0 := by
  exact mixedMoment_order_one B hB node1574 node1574Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1576 node1576Labels = 0 := by
  exact mixedMoment_order_one B hB node1576 node1576Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1579 node1579Labels = 0 := by
  exact mixedMoment_order_one B hB node1579 node1579Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1592 node1592Labels = 0 := by
  exact mixedMoment_alpha B hF node1592 node1592Labels 1 permutation434
    (by decide +kernel)

theorem zero1595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1595 node1595Labels = 0 := by
  exact mixedMoment_alpha B hF node1595 node1595Labels 1 permutation434
    (by decide +kernel)

theorem zero1596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1596 node1596Labels = 0 := by
  exact mixedMoment_alpha B hF node1596 node1596Labels 1 permutation437
    (by decide +kernel)

theorem zero1598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1598 node1598Labels = 0 := by
  exact mixedMoment_alpha B hF node1598 node1598Labels 1 permutation436
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
