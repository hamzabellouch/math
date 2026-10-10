import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1839 node1839Labels = 0 := by
  exact mixedMoment_order_one B hB node1839 node1839Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1852 node1852Labels = 0 := by
  exact mixedMoment_order_one B hB node1852 node1852Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1853 node1853Labels = 0 := by
  exact mixedMoment_order_one B hB node1853 node1853Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
