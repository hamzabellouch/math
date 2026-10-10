import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4097 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4097 node4097Labels = 0 := by
  exact mixedMoment_order_one B hB node4097 node4097Labels 0
    (by decide +kernel) (by decide +kernel)

theorem zero4117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4117 node4117Labels = 0 := by
  exact mixedMoment_order_one B hB node4117 node4117Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4118 node4118Labels = 0 := by
  exact mixedMoment_order_one B hB node4118 node4118Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4120 node4120Labels = 0 := by
  exact mixedMoment_order_one B hB node4120 node4120Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4123 node4123Labels = 0 := by
  exact mixedMoment_order_one B hB node4123 node4123Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4124 node4124Labels = 0 := by
  exact mixedMoment_order_one B hB node4124 node4124Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4125 node4125Labels = 0 := by
  exact mixedMoment_order_one B hB node4125 node4125Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4127 node4127Labels = 0 := by
  exact mixedMoment_order_one B hB node4127 node4127Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4130 node4130Labels = 0 := by
  exact mixedMoment_order_one B hB node4130 node4130Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4131 node4131Labels = 0 := by
  exact mixedMoment_order_one B hB node4131 node4131Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4136 node4136Labels = 0 := by
  exact mixedMoment_order_one B hB node4136 node4136Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4137 node4137Labels = 0 := by
  exact mixedMoment_order_one B hB node4137 node4137Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
