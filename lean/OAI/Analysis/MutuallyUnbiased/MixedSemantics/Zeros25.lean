import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1614 node1614Labels = 0 := by
  exact mixedMoment_alpha B hF node1614 node1614Labels 1 permutation446
    (by decide +kernel)

theorem zero1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1621 node1621Labels = 0 := by
  exact mixedMoment_order_one B hB node1621 node1621Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1622 node1622Labels = 0 := by
  exact mixedMoment_order_one B hB node1622 node1622Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1625 node1625Labels = 0 := by
  exact mixedMoment_order_one B hB node1625 node1625Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1631 node1631Labels = 0 := by
  exact mixedMoment_order_one B hB node1631 node1631Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1662 node1662Labels = 0 := by
  exact mixedMoment_alpha B hF node1662 node1662Labels 1 permutation484
    (by decide +kernel)

theorem zero1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1663 node1663Labels = 0 := by
  exact mixedMoment_alpha B hF node1663 node1663Labels 1 permutation485
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
