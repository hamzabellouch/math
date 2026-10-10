import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node768 node768Labels = 0 := by
  exact mixedMoment_order_one B hB node768 node768Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node770 node770Labels = 0 := by
  exact mixedMoment_order_one B hB node770 node770Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node772 node772Labels = 0 := by
  exact mixedMoment_order_one B hB node772 node772Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node775 node775Labels = 0 := by
  exact mixedMoment_order_one B hB node775 node775Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node805 node805Labels = 0 := by
  exact mixedMoment_order_one B hB node805 node805Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node806 node806Labels = 0 := by
  exact mixedMoment_order_one B hB node806 node806Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = 0 := by
  exact mixedMoment_order_one B hB node809 node809Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node810 node810Labels = 0 := by
  exact mixedMoment_order_one B hB node810 node810Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node812 node812Labels = 0 := by
  exact mixedMoment_order_one B hB node812 node812Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node816 node816Labels = 0 := by
  exact mixedMoment_order_one B hB node816 node816Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node817 node817Labels = 0 := by
  exact mixedMoment_order_one B hB node817 node817Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
