import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3904 node3904Labels = 0 := by
  exact mixedMoment_order_one B hB node3904 node3904Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3905 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3905 node3905Labels = 0 := by
  exact mixedMoment_order_one B hB node3905 node3905Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3908 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3908 node3908Labels = 0 := by
  exact mixedMoment_order_one B hB node3908 node3908Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3914 node3914Labels = 0 := by
  exact mixedMoment_order_one B hB node3914 node3914Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3917 node3917Labels = 0 := by
  exact mixedMoment_alpha B hF node3917 node3917Labels 2 permutation152
    (by decide +kernel)

theorem zero3920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3920 node3920Labels = 0 := by
  exact mixedMoment_alpha B hF node3920 node3920Labels 1 permutation160
    (by decide +kernel)

theorem zero3921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3921 node3921Labels = 0 := by
  exact mixedMoment_alpha B hF node3921 node3921Labels 2 permutation152
    (by decide +kernel)

theorem zero3923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3923 node3923Labels = 0 := by
  exact mixedMoment_alpha B hF node3923 node3923Labels 2 permutation158
    (by decide +kernel)

theorem zero3928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3928 node3928Labels = 0 := by
  exact mixedMoment_alpha B hF node3928 node3928Labels 2 permutation152
    (by decide +kernel)

theorem zero3940 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3940 node3940Labels = 0 := by
  exact mixedMoment_order_one B hB node3940 node3940Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3941 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3941 node3941Labels = 0 := by
  exact mixedMoment_order_one B hB node3941 node3941Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero3944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3944 node3944Labels = 0 := by
  exact mixedMoment_alpha B hF node3944 node3944Labels 1 permutation202
    (by decide +kernel)

theorem zero3950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3950 node3950Labels = 0 := by
  exact mixedMoment_alpha B hF node3950 node3950Labels 1 permutation212
    (by decide +kernel)

theorem zero3951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3951 node3951Labels = 0 := by
  exact mixedMoment_alpha B hF node3951 node3951Labels 1 permutation216
    (by decide +kernel)

theorem zero3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = 0 := by
  exact mixedMoment_alpha B hF node3953 node3953Labels 1 permutation200
    (by decide +kernel)

theorem zero3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = 0 := by
  exact mixedMoment_alpha B hF node3956 node3956Labels 1 permutation203
    (by decide +kernel)

theorem zero3962 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3962 node3962Labels = 0 := by
  exact mixedMoment_order_one B hB node3962 node3962Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
