import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4300 node4300Labels = 0 := by
  exact mixedMoment_order_one B hB node4300 node4300Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4302 node4302Labels = 0 := by
  exact mixedMoment_order_one B hB node4302 node4302Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4305 node4305Labels = 0 := by
  exact mixedMoment_order_one B hB node4305 node4305Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4306 node4306Labels = 0 := by
  exact mixedMoment_order_one B hB node4306 node4306Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4308 node4308Labels = 0 := by
  exact mixedMoment_order_one B hB node4308 node4308Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4311 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4311 node4311Labels = 0 := by
  exact mixedMoment_order_one B hB node4311 node4311Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4312 node4312Labels = 0 := by
  exact mixedMoment_order_one B hB node4312 node4312Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4317 node4317Labels = 0 := by
  exact mixedMoment_order_one B hB node4317 node4317Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4318 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4318 node4318Labels = 0 := by
  exact mixedMoment_order_one B hB node4318 node4318Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4326 node4326Labels = 0 := by
  exact mixedMoment_alpha B hF node4326 node4326Labels 1 permutation152
    (by decide +kernel)

theorem zero4329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4329 node4329Labels = 0 := by
  exact mixedMoment_alpha B hF node4329 node4329Labels 1 permutation152
    (by decide +kernel)

theorem zero4340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4340 node4340Labels = 0 := by
  exact mixedMoment_alpha B hF node4340 node4340Labels 1 permutation161
    (by decide +kernel)

theorem zero4342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4342 node4342Labels = 0 := by
  exact mixedMoment_alpha B hF node4342 node4342Labels 1 permutation160
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
