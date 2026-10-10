import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons71

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4544 node4544Labels = Sparse.eval nodeValue4544 (mixedVector B) := by
  have h := singleton4544 B _hB
  rw [sound1129 B _hB _hF, sound3263 B _hB _hF] at h
  norm_num [nodeValue4544, nodeValue1129, nodeValue3263, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4545 node4545Labels = Sparse.eval nodeValue4545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4545) = mixedMoment B node4545 node4545Labels := rfl
  simpa [nodeValue4545, Sparse.eval] using hc.symm

theorem sound4546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4546 node4546Labels = Sparse.eval nodeValue4546 (mixedVector B) := by
  have h := singleton4546 B _hB
  rw [sound1131 B _hB _hF, sound3264 B _hB _hF] at h
  norm_num [nodeValue4546, nodeValue1131, nodeValue3264, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4547 node4547Labels = Sparse.eval nodeValue4547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4547) = mixedMoment B node4547 node4547Labels := rfl
  simpa [nodeValue4547, Sparse.eval] using hc.symm

theorem sound4548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4548 node4548Labels = Sparse.eval nodeValue4548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4548) = mixedMoment B node4548 node4548Labels := rfl
  simpa [nodeValue4548, Sparse.eval] using hc.symm

theorem sound4549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4549 node4549Labels = Sparse.eval nodeValue4549 (mixedVector B) := by
  have h := singleton4549 B _hB
  rw [sound1134 B _hB _hF, sound3265 B _hB _hF] at h
  norm_num [nodeValue4549, nodeValue1134, nodeValue3265, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4550 node4550Labels = Sparse.eval nodeValue4550 (mixedVector B) := by
  have h := singleton4550 B _hB
  rw [sound1135 B _hB _hF, sound3269 B _hB _hF] at h
  norm_num [nodeValue4550, nodeValue1135, nodeValue3269, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4551 node4551Labels = Sparse.eval nodeValue4551 (mixedVector B) := by
  have h := singleton4551 B _hB
  rw [sound1136 B _hB _hF, sound3273 B _hB _hF] at h
  norm_num [nodeValue4551, nodeValue1136, nodeValue3273, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4552 node4552Labels = Sparse.eval nodeValue4552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4552) = mixedMoment B node4552 node4552Labels := rfl
  simpa [nodeValue4552, Sparse.eval] using hc.symm

theorem sound4553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4553 node4553Labels = Sparse.eval nodeValue4553 (mixedVector B) := by
  have h := singleton4553 B _hB
  rw [sound1138 B _hB _hF, sound3270 B _hB _hF] at h
  norm_num [nodeValue4553, nodeValue1138, nodeValue3270, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4554 node4554Labels = Sparse.eval nodeValue4554 (mixedVector B) := by
  have h := singleton4554 B _hB
  rw [sound1139 B _hB _hF, sound3274 B _hB _hF] at h
  norm_num [nodeValue4554, nodeValue1139, nodeValue3274, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4555 node4555Labels = Sparse.eval nodeValue4555 (mixedVector B) := by
  have h := singleton4555 B _hB
  rw [sound1140 B _hB _hF, sound3275 B _hB _hF] at h
  norm_num [nodeValue4555, nodeValue1140, nodeValue3275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4556 node4556Labels = Sparse.eval nodeValue4556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4556) = mixedMoment B node4556 node4556Labels := rfl
  simpa [nodeValue4556, Sparse.eval] using hc.symm

theorem sound4557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4557 node4557Labels = Sparse.eval nodeValue4557 (mixedVector B) := by
  have h := singleton4557 B _hB
  rw [sound1143 B _hB _hF, sound2167 B _hB _hF] at h
  norm_num [nodeValue4557, nodeValue1143, nodeValue2167, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4558 node4558Labels = Sparse.eval nodeValue4558 (mixedVector B) := by
  have h := singleton4558 B _hB
  rw [sound1144 B _hB _hF, sound3276 B _hB _hF] at h
  norm_num [nodeValue4558, nodeValue1144, nodeValue3276, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4559 node4559Labels = Sparse.eval nodeValue4559 (mixedVector B) := by
  have h := singleton4559 B _hB
  rw [sound1145 B _hB _hF, sound3277 B _hB _hF] at h
  norm_num [nodeValue4559, nodeValue1145, nodeValue3277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4560 node4560Labels = Sparse.eval nodeValue4560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4560) = mixedMoment B node4560 node4560Labels := rfl
  simpa [nodeValue4560, Sparse.eval] using hc.symm

theorem sound4561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4561 node4561Labels = Sparse.eval nodeValue4561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4561) = mixedMoment B node4561 node4561Labels := rfl
  simpa [nodeValue4561, Sparse.eval] using hc.symm

theorem sound4562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4562 node4562Labels = Sparse.eval nodeValue4562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4562) = mixedMoment B node4562 node4562Labels := rfl
  simpa [nodeValue4562, Sparse.eval] using hc.symm

theorem sound4563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4563 node4563Labels = Sparse.eval nodeValue4563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4563) = mixedMoment B node4563 node4563Labels := rfl
  simpa [nodeValue4563, Sparse.eval] using hc.symm

theorem sound4564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4564 node4564Labels = Sparse.eval nodeValue4564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4564) = mixedMoment B node4564 node4564Labels := rfl
  simpa [nodeValue4564, Sparse.eval] using hc.symm

theorem sound4565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4565 node4565Labels = Sparse.eval nodeValue4565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4565) = mixedMoment B node4565 node4565Labels := rfl
  simpa [nodeValue4565, Sparse.eval] using hc.symm

theorem sound4566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4566 node4566Labels = Sparse.eval nodeValue4566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4566) = mixedMoment B node4566 node4566Labels := rfl
  simpa [nodeValue4566, Sparse.eval] using hc.symm

theorem sound4567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4567 node4567Labels = Sparse.eval nodeValue4567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4567) = mixedMoment B node4567 node4567Labels := rfl
  simpa [nodeValue4567, Sparse.eval] using hc.symm

theorem sound4568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4568 node4568Labels = Sparse.eval nodeValue4568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4568) = mixedMoment B node4568 node4568Labels := rfl
  simpa [nodeValue4568, Sparse.eval] using hc.symm

theorem sound4569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4569 node4569Labels = Sparse.eval nodeValue4569 (mixedVector B) := by
  have h := singleton4569 B _hB
  rw [sound1187 B _hB _hF, sound3244 B _hB _hF] at h
  norm_num [nodeValue4569, nodeValue1187, nodeValue3244, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4570 node4570Labels = Sparse.eval nodeValue4570 (mixedVector B) := by
  have h := singleton4570 B _hB
  rw [sound1188 B _hB _hF, sound3245 B _hB _hF] at h
  norm_num [nodeValue4570, nodeValue1188, nodeValue3245, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4571 node4571Labels = Sparse.eval nodeValue4571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4571) = mixedMoment B node4571 node4571Labels := rfl
  simpa [nodeValue4571, Sparse.eval] using hc.symm

theorem sound4572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4572 node4572Labels = Sparse.eval nodeValue4572 (mixedVector B) := by
  have h := singleton4572 B _hB
  rw [sound1190 B _hB _hF, sound1952 B _hB _hF] at h
  norm_num [nodeValue4572, nodeValue1190, nodeValue1952, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4573 node4573Labels = Sparse.eval nodeValue4573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4573) = mixedMoment B node4573 node4573Labels := rfl
  simpa [nodeValue4573, Sparse.eval] using hc.symm

theorem sound4574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4574 node4574Labels = Sparse.eval nodeValue4574 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4574) = mixedMoment B node4574 node4574Labels := rfl
  simpa [nodeValue4574, Sparse.eval] using hc.symm

theorem sound4575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4575 node4575Labels = Sparse.eval nodeValue4575 (mixedVector B) := by
  have h := singleton4575 B _hB
  rw [sound1193 B _hB _hF, sound3248 B _hB _hF] at h
  norm_num [nodeValue4575, nodeValue1193, nodeValue3248, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4576 node4576Labels = Sparse.eval nodeValue4576 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4576) = mixedMoment B node4576 node4576Labels := rfl
  simpa [nodeValue4576, Sparse.eval] using hc.symm

theorem sound4577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4577 node4577Labels = Sparse.eval nodeValue4577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4577) = mixedMoment B node4577 node4577Labels := rfl
  simpa [nodeValue4577, Sparse.eval] using hc.symm

theorem sound4578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4578 node4578Labels = Sparse.eval nodeValue4578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4578) = mixedMoment B node4578 node4578Labels := rfl
  simpa [nodeValue4578, Sparse.eval] using hc.symm

theorem sound4579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4579 node4579Labels = Sparse.eval nodeValue4579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4579) = mixedMoment B node4579 node4579Labels := rfl
  simpa [nodeValue4579, Sparse.eval] using hc.symm

theorem sound4580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4580 node4580Labels = Sparse.eval nodeValue4580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4580) = mixedMoment B node4580 node4580Labels := rfl
  simpa [nodeValue4580, Sparse.eval] using hc.symm

theorem sound4581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4581 node4581Labels = Sparse.eval nodeValue4581 (mixedVector B) := by
  have h := singleton4581 B _hB
  rw [sound1200 B _hB _hF, sound3281 B _hB _hF] at h
  norm_num [nodeValue4581, nodeValue1200, nodeValue3281, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4582 node4582Labels = Sparse.eval nodeValue4582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4582) = mixedMoment B node4582 node4582Labels := rfl
  simpa [nodeValue4582, Sparse.eval] using hc.symm

theorem sound4583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4583 node4583Labels = Sparse.eval nodeValue4583 (mixedVector B) := by
  have h := singleton4583 B _hB
  rw [sound1202 B _hB _hF, sound1942 B _hB _hF] at h
  norm_num [nodeValue4583, nodeValue1202, nodeValue1942, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4584 node4584Labels = Sparse.eval nodeValue4584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4584) = mixedMoment B node4584 node4584Labels := rfl
  simpa [nodeValue4584, Sparse.eval] using hc.symm

theorem sound4585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4585 node4585Labels = Sparse.eval nodeValue4585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4585) = mixedMoment B node4585 node4585Labels := rfl
  simpa [nodeValue4585, Sparse.eval] using hc.symm

theorem sound4586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4586 node4586Labels = Sparse.eval nodeValue4586 (mixedVector B) := by
  have h := singleton4586 B _hB
  rw [sound1205 B _hB _hF, sound3284 B _hB _hF] at h
  norm_num [nodeValue4586, nodeValue1205, nodeValue3284, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4587 node4587Labels = Sparse.eval nodeValue4587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4587) = mixedMoment B node4587 node4587Labels := rfl
  simpa [nodeValue4587, Sparse.eval] using hc.symm

theorem sound4588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4588 node4588Labels = Sparse.eval nodeValue4588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4588) = mixedMoment B node4588 node4588Labels := rfl
  simpa [nodeValue4588, Sparse.eval] using hc.symm

theorem sound4589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4589 node4589Labels = Sparse.eval nodeValue4589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4589) = mixedMoment B node4589 node4589Labels := rfl
  simpa [nodeValue4589, Sparse.eval] using hc.symm

theorem sound4590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4590 node4590Labels = Sparse.eval nodeValue4590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4590) = mixedMoment B node4590 node4590Labels := rfl
  simpa [nodeValue4590, Sparse.eval] using hc.symm

theorem sound4591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4591 node4591Labels = Sparse.eval nodeValue4591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4591) = mixedMoment B node4591 node4591Labels := rfl
  simpa [nodeValue4591, Sparse.eval] using hc.symm

theorem sound4592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4592 node4592Labels = Sparse.eval nodeValue4592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4592) = mixedMoment B node4592 node4592Labels := rfl
  simpa [nodeValue4592, Sparse.eval] using hc.symm

theorem sound4593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4593 node4593Labels = Sparse.eval nodeValue4593 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4593) = mixedMoment B node4593 node4593Labels := rfl
  simpa [nodeValue4593, Sparse.eval] using hc.symm

theorem sound4594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4594 node4594Labels = Sparse.eval nodeValue4594 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4594) = mixedMoment B node4594 node4594Labels := rfl
  simpa [nodeValue4594, Sparse.eval] using hc.symm

theorem sound4595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4595 node4595Labels = Sparse.eval nodeValue4595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4595) = mixedMoment B node4595 node4595Labels := rfl
  simpa [nodeValue4595, Sparse.eval] using hc.symm

theorem sound4596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4596 node4596Labels = Sparse.eval nodeValue4596 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4596) = mixedMoment B node4596 node4596Labels := rfl
  simpa [nodeValue4596, Sparse.eval] using hc.symm

theorem sound4597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4597 node4597Labels = Sparse.eval nodeValue4597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4597) = mixedMoment B node4597 node4597Labels := rfl
  simpa [nodeValue4597, Sparse.eval] using hc.symm

theorem sound4598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4598 node4598Labels = Sparse.eval nodeValue4598 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4598) = mixedMoment B node4598 node4598Labels := rfl
  simpa [nodeValue4598, Sparse.eval] using hc.symm

theorem sound4599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4599 node4599Labels = Sparse.eval nodeValue4599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4599) = mixedMoment B node4599 node4599Labels := rfl
  simpa [nodeValue4599, Sparse.eval] using hc.symm

theorem sound4600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4600 node4600Labels = Sparse.eval nodeValue4600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4600) = mixedMoment B node4600 node4600Labels := rfl
  simpa [nodeValue4600, Sparse.eval] using hc.symm

theorem sound4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4601 node4601Labels = Sparse.eval nodeValue4601 (mixedVector B) := by
  have h := singleton4601 B _hB
  rw [sound1235 B _hB _hF, sound3292 B _hB _hF] at h
  norm_num [nodeValue4601, nodeValue1235, nodeValue3292, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4603 node4603Labels = Sparse.eval nodeValue4603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4603) = mixedMoment B node4603 node4603Labels := rfl
  simpa [nodeValue4603, Sparse.eval] using hc.symm

theorem sound4604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4604 node4604Labels = Sparse.eval nodeValue4604 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4604) = mixedMoment B node4604 node4604Labels := rfl
  simpa [nodeValue4604, Sparse.eval] using hc.symm

theorem sound4605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4605 node4605Labels = Sparse.eval nodeValue4605 (mixedVector B) := by
  have h := singleton4605 B _hB
  rw [sound1239 B _hB _hF, sound2226 B _hB _hF] at h
  norm_num [nodeValue4605, nodeValue1239, nodeValue2226, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4606 node4606Labels = Sparse.eval nodeValue4606 (mixedVector B) := by
  have h := singleton4606 B _hB
  rw [sound1240 B _hB _hF, sound3299 B _hB _hF] at h
  norm_num [nodeValue4606, nodeValue1240, nodeValue3299, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4607 node4607Labels = Sparse.eval nodeValue4607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4607) = mixedMoment B node4607 node4607Labels := rfl
  simpa [nodeValue4607, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
