import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons64

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4096 node4096Labels = Sparse.eval nodeValue4096 (mixedVector B) := by
  have h := singleton4096 B _hB
  rw [sound7 B _hB _hF] at h
  norm_num [nodeValue4096, nodeValue7, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4097 node4097Labels = Sparse.eval nodeValue4097 (mixedVector B) := by
  simpa only [nodeValue4097, Sparse.eval_nil] using zero4097 B _hB _hF

theorem sound4098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4098 node4098Labels = Sparse.eval nodeValue4098 (mixedVector B) := by
  have h := singleton4098 B _hB
  rw [sound535 B _hB _hF, sound656 B _hB _hF] at h
  norm_num [nodeValue4098, nodeValue535, nodeValue656, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4099 node4099Labels = Sparse.eval nodeValue4099 (mixedVector B) := by
  have h := singleton4099 B _hB
  rw [sound536 B _hB _hF, sound657 B _hB _hF] at h
  norm_num [nodeValue4099, nodeValue536, nodeValue657, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4100 node4100Labels = Sparse.eval nodeValue4100 (mixedVector B) := by
  have h := singleton4100 B _hB
  rw [sound537 B _hB _hF, sound662 B _hB _hF] at h
  norm_num [nodeValue4100, nodeValue537, nodeValue662, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4101 node4101Labels = Sparse.eval nodeValue4101 (mixedVector B) := by
  have h := singleton4101 B _hB
  rw [sound538 B _hB _hF, sound663 B _hB _hF] at h
  norm_num [nodeValue4101, nodeValue538, nodeValue663, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4102 node4102Labels = Sparse.eval nodeValue4102 (mixedVector B) := by
  have h := singleton4102 B _hB
  rw [sound539 B _hB _hF, sound664 B _hB _hF] at h
  norm_num [nodeValue4102, nodeValue539, nodeValue664, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4103 node4103Labels = Sparse.eval nodeValue4103 (mixedVector B) := by
  have h := singleton4103 B _hB
  rw [sound540 B _hB _hF, sound665 B _hB _hF] at h
  norm_num [nodeValue4103, nodeValue540, nodeValue665, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4104 node4104Labels = Sparse.eval nodeValue4104 (mixedVector B) := by
  have h := singleton4104 B _hB
  rw [sound541 B _hB _hF, sound674 B _hB _hF] at h
  norm_num [nodeValue4104, nodeValue541, nodeValue674, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4105 node4105Labels = Sparse.eval nodeValue4105 (mixedVector B) := by
  have h := singleton4105 B _hB
  rw [sound542 B _hB _hF, sound681 B _hB _hF] at h
  norm_num [nodeValue4105, nodeValue542, nodeValue681, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4106 node4106Labels = Sparse.eval nodeValue4106 (mixedVector B) := by
  have h := singleton4106 B _hB
  rw [sound543 B _hB _hF, sound675 B _hB _hF] at h
  norm_num [nodeValue4106, nodeValue543, nodeValue675, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4107 node4107Labels = Sparse.eval nodeValue4107 (mixedVector B) := by
  have h := singleton4107 B _hB
  rw [sound544 B _hB _hF, sound682 B _hB _hF] at h
  norm_num [nodeValue4107, nodeValue544, nodeValue682, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4108 node4108Labels = Sparse.eval nodeValue4108 (mixedVector B) := by
  have h := singleton4108 B _hB
  rw [sound545 B _hB _hF, sound683 B _hB _hF] at h
  norm_num [nodeValue4108, nodeValue545, nodeValue683, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4109 node4109Labels = Sparse.eval nodeValue4109 (mixedVector B) := by
  have h := singleton4109 B _hB
  rw [sound546 B _hB _hF, sound676 B _hB _hF] at h
  norm_num [nodeValue4109, nodeValue546, nodeValue676, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4110 node4110Labels = Sparse.eval nodeValue4110 (mixedVector B) := by
  have h := singleton4110 B _hB
  rw [sound547 B _hB _hF, sound684 B _hB _hF] at h
  norm_num [nodeValue4110, nodeValue547, nodeValue684, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4111 node4111Labels = Sparse.eval nodeValue4111 (mixedVector B) := by
  have h := singleton4111 B _hB
  rw [sound548 B _hB _hF, sound685 B _hB _hF] at h
  norm_num [nodeValue4111, nodeValue548, nodeValue685, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4112 node4112Labels = Sparse.eval nodeValue4112 (mixedVector B) := by
  have h := singleton4112 B _hB
  rw [sound549 B _hB _hF, sound686 B _hB _hF] at h
  norm_num [nodeValue4112, nodeValue549, nodeValue686, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4113 node4113Labels = Sparse.eval nodeValue4113 (mixedVector B) := by
  have h := singleton4113 B _hB
  rw [sound550 B _hB _hF, sound658 B _hB _hF] at h
  norm_num [nodeValue4113, nodeValue550, nodeValue658, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4114 node4114Labels = Sparse.eval nodeValue4114 (mixedVector B) := by
  have h := singleton4114 B _hB
  rw [sound551 B _hB _hF, sound659 B _hB _hF] at h
  norm_num [nodeValue4114, nodeValue551, nodeValue659, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4115 node4115Labels = Sparse.eval nodeValue4115 (mixedVector B) := by
  have h := singleton4115 B _hB
  rw [sound552 B _hB _hF, sound660 B _hB _hF] at h
  norm_num [nodeValue4115, nodeValue552, nodeValue660, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4116 node4116Labels = Sparse.eval nodeValue4116 (mixedVector B) := by
  have h := singleton4116 B _hB
  rw [sound553 B _hB _hF, sound661 B _hB _hF] at h
  norm_num [nodeValue4116, nodeValue553, nodeValue661, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4117 node4117Labels = Sparse.eval nodeValue4117 (mixedVector B) := by
  simpa only [nodeValue4117, Sparse.eval_nil] using zero4117 B _hB _hF

theorem sound4118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4118 node4118Labels = Sparse.eval nodeValue4118 (mixedVector B) := by
  simpa only [nodeValue4118, Sparse.eval_nil] using zero4118 B _hB _hF

theorem sound4119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4119 node4119Labels = Sparse.eval nodeValue4119 (mixedVector B) := by
  have h := singleton4119 B _hB
  rw [sound554 B _hB _hF, sound668 B _hB _hF] at h
  norm_num [nodeValue4119, nodeValue554, nodeValue668, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4120 node4120Labels = Sparse.eval nodeValue4120 (mixedVector B) := by
  simpa only [nodeValue4120, Sparse.eval_nil] using zero4120 B _hB _hF

theorem sound4121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4121 node4121Labels = Sparse.eval nodeValue4121 (mixedVector B) := by
  have h := singleton4121 B _hB
  rw [sound555 B _hB _hF, sound671 B _hB _hF] at h
  norm_num [nodeValue4121, nodeValue555, nodeValue671, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4122 node4122Labels = Sparse.eval nodeValue4122 (mixedVector B) := by
  have h := singleton4122 B _hB
  rw [sound556 B _hB _hF, sound670 B _hB _hF] at h
  norm_num [nodeValue4122, nodeValue556, nodeValue670, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4123 node4123Labels = Sparse.eval nodeValue4123 (mixedVector B) := by
  simpa only [nodeValue4123, Sparse.eval_nil] using zero4123 B _hB _hF

theorem sound4124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4124 node4124Labels = Sparse.eval nodeValue4124 (mixedVector B) := by
  simpa only [nodeValue4124, Sparse.eval_nil] using zero4124 B _hB _hF

theorem sound4125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4125 node4125Labels = Sparse.eval nodeValue4125 (mixedVector B) := by
  simpa only [nodeValue4125, Sparse.eval_nil] using zero4125 B _hB _hF

theorem sound4126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4126 node4126Labels = Sparse.eval nodeValue4126 (mixedVector B) := by
  have h := singleton4126 B _hB
  rw [sound557 B _hB _hF, sound677 B _hB _hF] at h
  norm_num [nodeValue4126, nodeValue557, nodeValue677, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4127 node4127Labels = Sparse.eval nodeValue4127 (mixedVector B) := by
  simpa only [nodeValue4127, Sparse.eval_nil] using zero4127 B _hB _hF

theorem sound4128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4128 node4128Labels = Sparse.eval nodeValue4128 (mixedVector B) := by
  have h := singleton4128 B _hB
  rw [sound559 B _hB _hF, sound690 B _hB _hF] at h
  norm_num [nodeValue4128, nodeValue559, nodeValue690, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4129 node4129Labels = Sparse.eval nodeValue4129 (mixedVector B) := by
  have h := singleton4129 B _hB
  rw [sound560 B _hB _hF, sound678 B _hB _hF] at h
  norm_num [nodeValue4129, nodeValue560, nodeValue678, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4130 node4130Labels = Sparse.eval nodeValue4130 (mixedVector B) := by
  simpa only [nodeValue4130, Sparse.eval_nil] using zero4130 B _hB _hF

theorem sound4131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4131 node4131Labels = Sparse.eval nodeValue4131 (mixedVector B) := by
  simpa only [nodeValue4131, Sparse.eval_nil] using zero4131 B _hB _hF

theorem sound4132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4132 node4132Labels = Sparse.eval nodeValue4132 (mixedVector B) := by
  have h := singleton4132 B _hB
  rw [sound562 B _hB _hF, sound679 B _hB _hF] at h
  norm_num [nodeValue4132, nodeValue562, nodeValue679, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4133 node4133Labels = Sparse.eval nodeValue4133 (mixedVector B) := by
  have h := singleton4133 B _hB
  rw [sound563 B _hB _hF, sound692 B _hB _hF] at h
  norm_num [nodeValue4133, nodeValue563, nodeValue692, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4134 node4134Labels = Sparse.eval nodeValue4134 (mixedVector B) := by
  have h := singleton4134 B _hB
  rw [sound564 B _hB _hF, sound695 B _hB _hF] at h
  norm_num [nodeValue4134, nodeValue564, nodeValue695, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4135 node4135Labels = Sparse.eval nodeValue4135 (mixedVector B) := by
  have h := singleton4135 B _hB
  rw [sound565 B _hB _hF, sound680 B _hB _hF] at h
  norm_num [nodeValue4135, nodeValue565, nodeValue680, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4136 node4136Labels = Sparse.eval nodeValue4136 (mixedVector B) := by
  simpa only [nodeValue4136, Sparse.eval_nil] using zero4136 B _hB _hF

theorem sound4137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4137 node4137Labels = Sparse.eval nodeValue4137 (mixedVector B) := by
  simpa only [nodeValue4137, Sparse.eval_nil] using zero4137 B _hB _hF

theorem sound4138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4138 node4138Labels = Sparse.eval nodeValue4138 (mixedVector B) := by
  have h := singleton4138 B _hB
  rw [sound566 B _hB _hF, sound694 B _hB _hF] at h
  norm_num [nodeValue4138, nodeValue566, nodeValue694, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4139 node4139Labels = Sparse.eval nodeValue4139 (mixedVector B) := by
  have h := singleton4139 B _hB
  rw [sound567 B _hB _hF, sound1488 B _hB _hF] at h
  norm_num [nodeValue4139, nodeValue567, nodeValue1488, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4140 node4140Labels = Sparse.eval nodeValue4140 (mixedVector B) := by
  have h := singleton4140 B _hB
  rw [sound568 B _hB _hF, sound1489 B _hB _hF] at h
  norm_num [nodeValue4140, nodeValue568, nodeValue1489, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4141 node4141Labels = Sparse.eval nodeValue4141 (mixedVector B) := by
  have h := singleton4141 B _hB
  rw [sound569 B _hB _hF, sound1490 B _hB _hF] at h
  norm_num [nodeValue4141, nodeValue569, nodeValue1490, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4142 node4142Labels = Sparse.eval nodeValue4142 (mixedVector B) := by
  have h := singleton4142 B _hB
  rw [sound570 B _hB _hF, sound765 B _hB _hF] at h
  norm_num [nodeValue4142, nodeValue570, nodeValue765, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4143 node4143Labels = Sparse.eval nodeValue4143 (mixedVector B) := by
  have h := singleton4143 B _hB
  rw [sound571 B _hB _hF, sound1491 B _hB _hF] at h
  norm_num [nodeValue4143, nodeValue571, nodeValue1491, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4144 node4144Labels = Sparse.eval nodeValue4144 (mixedVector B) := by
  have h := singleton4144 B _hB
  rw [sound572 B _hB _hF, sound1492 B _hB _hF] at h
  norm_num [nodeValue4144, nodeValue572, nodeValue1492, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4145 node4145Labels = Sparse.eval nodeValue4145 (mixedVector B) := by
  have h := singleton4145 B _hB
  rw [sound573 B _hB _hF, sound1493 B _hB _hF] at h
  norm_num [nodeValue4145, nodeValue573, nodeValue1493, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4146 node4146Labels = Sparse.eval nodeValue4146 (mixedVector B) := by
  have h := singleton4146 B _hB
  rw [sound574 B _hB _hF, sound1494 B _hB _hF] at h
  norm_num [nodeValue4146, nodeValue574, nodeValue1494, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4147 node4147Labels = Sparse.eval nodeValue4147 (mixedVector B) := by
  have h := singleton4147 B _hB
  rw [sound575 B _hB _hF, sound1495 B _hB _hF] at h
  norm_num [nodeValue4147, nodeValue575, nodeValue1495, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4148 node4148Labels = Sparse.eval nodeValue4148 (mixedVector B) := by
  have h := singleton4148 B _hB
  rw [sound576 B _hB _hF, sound1496 B _hB _hF] at h
  norm_num [nodeValue4148, nodeValue576, nodeValue1496, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4149 node4149Labels = Sparse.eval nodeValue4149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4149) = mixedMoment B node4149 node4149Labels := rfl
  simpa [nodeValue4149, Sparse.eval] using hc.symm

theorem sound4150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4150 node4150Labels = Sparse.eval nodeValue4150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4150) = mixedMoment B node4150 node4150Labels := rfl
  simpa [nodeValue4150, Sparse.eval] using hc.symm

theorem sound4151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4151 node4151Labels = Sparse.eval nodeValue4151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4151) = mixedMoment B node4151 node4151Labels := rfl
  simpa [nodeValue4151, Sparse.eval] using hc.symm

theorem sound4152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4152 node4152Labels = Sparse.eval nodeValue4152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4152) = mixedMoment B node4152 node4152Labels := rfl
  simpa [nodeValue4152, Sparse.eval] using hc.symm

theorem sound4153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4153 node4153Labels = Sparse.eval nodeValue4153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4153) = mixedMoment B node4153 node4153Labels := rfl
  simpa [nodeValue4153, Sparse.eval] using hc.symm

theorem sound4154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4154 node4154Labels = Sparse.eval nodeValue4154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4154) = mixedMoment B node4154 node4154Labels := rfl
  simpa [nodeValue4154, Sparse.eval] using hc.symm

theorem sound4155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4155 node4155Labels = Sparse.eval nodeValue4155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4155) = mixedMoment B node4155 node4155Labels := rfl
  simpa [nodeValue4155, Sparse.eval] using hc.symm

theorem sound4156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4156 node4156Labels = Sparse.eval nodeValue4156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4156) = mixedMoment B node4156 node4156Labels := rfl
  simpa [nodeValue4156, Sparse.eval] using hc.symm

theorem sound4157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4157 node4157Labels = Sparse.eval nodeValue4157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4157) = mixedMoment B node4157 node4157Labels := rfl
  simpa [nodeValue4157, Sparse.eval] using hc.symm

theorem sound4158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4158 node4158Labels = Sparse.eval nodeValue4158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4158) = mixedMoment B node4158 node4158Labels := rfl
  simpa [nodeValue4158, Sparse.eval] using hc.symm

theorem sound4159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4159 node4159Labels = Sparse.eval nodeValue4159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4159) = mixedMoment B node4159 node4159Labels := rfl
  simpa [nodeValue4159, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
