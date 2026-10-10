import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3076 node3076Labels = 0 := by
  exact mixedMoment_alpha B hF node3076 node3076Labels 2 permutation152
    (by decide +kernel)

theorem zero3080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3080 node3080Labels = 0 := by
  exact mixedMoment_alpha B hF node3080 node3080Labels 2 permutation160
    (by decide +kernel)

theorem zero3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = 0 := by
  exact mixedMoment_alpha B hF node3085 node3085Labels 2 permutation158
    (by decide +kernel)

theorem zero3104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3104 node3104Labels = 0 := by
  exact mixedMoment_alpha B hF node3104 node3104Labels 2 permutation212
    (by decide +kernel)

theorem zero3111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3111 node3111Labels = 0 := by
  exact mixedMoment_order_one B hB node3111 node3111Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3112 node3112Labels = 0 := by
  exact mixedMoment_order_one B hB node3112 node3112Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3114 node3114Labels = 0 := by
  exact mixedMoment_order_one B hB node3114 node3114Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3122 node3122Labels = 0 := by
  exact mixedMoment_order_one B hB node3122 node3122Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3123 node3123Labels = 0 := by
  exact mixedMoment_order_one B hB node3123 node3123Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3124 node3124Labels = 0 := by
  exact mixedMoment_order_one B hB node3124 node3124Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3126 node3126Labels = 0 := by
  exact mixedMoment_order_one B hB node3126 node3126Labels 2
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
