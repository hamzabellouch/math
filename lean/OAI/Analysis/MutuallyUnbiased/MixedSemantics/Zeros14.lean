import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero896 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node896 node896Labels = 0 := by
  exact mixedMoment_order_one B hB node896 node896Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node904 node904Labels = 0 := by
  exact mixedMoment_alpha B hF node904 node904Labels 1 permutation152
    (by decide +kernel)

theorem zero907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node907 node907Labels = 0 := by
  exact mixedMoment_alpha B hF node907 node907Labels 1 permutation152
    (by decide +kernel)

theorem zero918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node918 node918Labels = 0 := by
  exact mixedMoment_alpha B hF node918 node918Labels 1 permutation161
    (by decide +kernel)

theorem zero920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node920 node920Labels = 0 := by
  exact mixedMoment_alpha B hF node920 node920Labels 1 permutation160
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
