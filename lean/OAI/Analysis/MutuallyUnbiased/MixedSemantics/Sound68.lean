import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons68

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4352 node4352Labels = Sparse.eval nodeValue4352 (mixedVector B) := by
  have h := singleton4352 B _hB
  rw [sound930 B _hB _hF, sound1690 B _hB _hF] at h
  norm_num [nodeValue4352, nodeValue930, nodeValue1690, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4353 node4353Labels = Sparse.eval nodeValue4353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4353) = mixedMoment B node4353 node4353Labels := rfl
  simpa [nodeValue4353, Sparse.eval] using hc.symm

theorem sound4354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4354 node4354Labels = Sparse.eval nodeValue4354 (mixedVector B) := by
  have h := singleton4354 B _hB
  rw [sound932 B _hB _hF, sound1681 B _hB _hF] at h
  norm_num [nodeValue4354, nodeValue932, nodeValue1681, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4355 node4355Labels = Sparse.eval nodeValue4355 (mixedVector B) := by
  have h := singleton4355 B _hB
  rw [sound933 B _hB _hF, sound1691 B _hB _hF] at h
  norm_num [nodeValue4355, nodeValue933, nodeValue1691, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4356 node4356Labels = Sparse.eval nodeValue4356 (mixedVector B) := by
  have h := singleton4356 B _hB
  rw [sound934 B _hB _hF, sound1692 B _hB _hF] at h
  norm_num [nodeValue4356, nodeValue934, nodeValue1692, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4357 node4357Labels = Sparse.eval nodeValue4357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4357) = mixedMoment B node4357 node4357Labels := rfl
  simpa [nodeValue4357, Sparse.eval] using hc.symm

theorem sound4358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4358 node4358Labels = Sparse.eval nodeValue4358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4358) = mixedMoment B node4358 node4358Labels := rfl
  simpa [nodeValue4358, Sparse.eval] using hc.symm

theorem sound4359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4359 node4359Labels = Sparse.eval nodeValue4359 (mixedVector B) := by
  have h := singleton4359 B _hB
  rw [sound937 B _hB _hF, sound1683 B _hB _hF] at h
  norm_num [nodeValue4359, nodeValue937, nodeValue1683, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4360 node4360Labels = Sparse.eval nodeValue4360 (mixedVector B) := by
  have h := singleton4360 B _hB
  rw [sound938 B _hB _hF, sound1693 B _hB _hF] at h
  norm_num [nodeValue4360, nodeValue938, nodeValue1693, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4361 node4361Labels = Sparse.eval nodeValue4361 (mixedVector B) := by
  have h := singleton4361 B _hB
  rw [sound939 B _hB _hF, sound1694 B _hB _hF] at h
  norm_num [nodeValue4361, nodeValue939, nodeValue1694, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4362 node4362Labels = Sparse.eval nodeValue4362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4362) = mixedMoment B node4362 node4362Labels := rfl
  simpa [nodeValue4362, Sparse.eval] using hc.symm

theorem sound4363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4363 node4363Labels = Sparse.eval nodeValue4363 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4363) = mixedMoment B node4363 node4363Labels := rfl
  simpa [nodeValue4363, Sparse.eval] using hc.symm

theorem sound4364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4364 node4364Labels = Sparse.eval nodeValue4364 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4364) = mixedMoment B node4364 node4364Labels := rfl
  simpa [nodeValue4364, Sparse.eval] using hc.symm

theorem sound4365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4365 node4365Labels = Sparse.eval nodeValue4365 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4365) = mixedMoment B node4365 node4365Labels := rfl
  simpa [nodeValue4365, Sparse.eval] using hc.symm

theorem sound4366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4366 node4366Labels = Sparse.eval nodeValue4366 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4366) = mixedMoment B node4366 node4366Labels := rfl
  simpa [nodeValue4366, Sparse.eval] using hc.symm

theorem sound4367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4367 node4367Labels = Sparse.eval nodeValue4367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4367) = mixedMoment B node4367 node4367Labels := rfl
  simpa [nodeValue4367, Sparse.eval] using hc.symm

theorem sound4368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4368 node4368Labels = Sparse.eval nodeValue4368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4368) = mixedMoment B node4368 node4368Labels := rfl
  simpa [nodeValue4368, Sparse.eval] using hc.symm

theorem sound4369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4369 node4369Labels = Sparse.eval nodeValue4369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4369) = mixedMoment B node4369 node4369Labels := rfl
  simpa [nodeValue4369, Sparse.eval] using hc.symm

theorem sound4370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4370 node4370Labels = Sparse.eval nodeValue4370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4370) = mixedMoment B node4370 node4370Labels := rfl
  simpa [nodeValue4370, Sparse.eval] using hc.symm

theorem sound4371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4371 node4371Labels = Sparse.eval nodeValue4371 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4371) = mixedMoment B node4371 node4371Labels := rfl
  simpa [nodeValue4371, Sparse.eval] using hc.symm

theorem sound4372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4372 node4372Labels = Sparse.eval nodeValue4372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4372) = mixedMoment B node4372 node4372Labels := rfl
  simpa [nodeValue4372, Sparse.eval] using hc.symm

theorem sound4373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4373 node4373Labels = Sparse.eval nodeValue4373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4373) = mixedMoment B node4373 node4373Labels := rfl
  simpa [nodeValue4373, Sparse.eval] using hc.symm

theorem sound4374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4374 node4374Labels = Sparse.eval nodeValue4374 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4374) = mixedMoment B node4374 node4374Labels := rfl
  simpa [nodeValue4374, Sparse.eval] using hc.symm

theorem sound4375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4375 node4375Labels = Sparse.eval nodeValue4375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4375) = mixedMoment B node4375 node4375Labels := rfl
  simpa [nodeValue4375, Sparse.eval] using hc.symm

theorem sound4376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4376 node4376Labels = Sparse.eval nodeValue4376 (mixedVector B) := by
  have h := singleton4376 B _hB
  rw [sound955 B _hB _hF, sound1542 B _hB _hF] at h
  norm_num [nodeValue4376, nodeValue955, nodeValue1542, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4377 node4377Labels = Sparse.eval nodeValue4377 (mixedVector B) := by
  have h := singleton4377 B _hB
  rw [sound956 B _hB _hF, sound1543 B _hB _hF] at h
  norm_num [nodeValue4377, nodeValue956, nodeValue1543, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4378 node4378Labels = Sparse.eval nodeValue4378 (mixedVector B) := by
  have h := singleton4378 B _hB
  rw [sound957 B _hB _hF, sound1544 B _hB _hF] at h
  norm_num [nodeValue4378, nodeValue957, nodeValue1544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4379 node4379Labels = Sparse.eval nodeValue4379 (mixedVector B) := by
  have h := singleton4379 B _hB
  rw [sound958 B _hB _hF, sound1545 B _hB _hF] at h
  norm_num [nodeValue4379, nodeValue958, nodeValue1545, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4380 node4380Labels = Sparse.eval nodeValue4380 (mixedVector B) := by
  have h := singleton4380 B _hB
  rw [sound959 B _hB _hF, sound1546 B _hB _hF] at h
  norm_num [nodeValue4380, nodeValue959, nodeValue1546, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4381 node4381Labels = Sparse.eval nodeValue4381 (mixedVector B) := by
  have h := singleton4381 B _hB
  rw [sound960 B _hB _hF, sound1547 B _hB _hF] at h
  norm_num [nodeValue4381, nodeValue960, nodeValue1547, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4382 node4382Labels = Sparse.eval nodeValue4382 (mixedVector B) := by
  have h := singleton4382 B _hB
  rw [sound962 B _hB _hF, sound1548 B _hB _hF] at h
  norm_num [nodeValue4382, nodeValue962, nodeValue1548, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4383 node4383Labels = Sparse.eval nodeValue4383 (mixedVector B) := by
  have h := singleton4383 B _hB
  rw [sound963 B _hB _hF, sound1549 B _hB _hF] at h
  norm_num [nodeValue4383, nodeValue963, nodeValue1549, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4384 node4384Labels = Sparse.eval nodeValue4384 (mixedVector B) := by
  have h := singleton4384 B _hB
  rw [sound964 B _hB _hF, sound1580 B _hB _hF] at h
  norm_num [nodeValue4384, nodeValue964, nodeValue1580, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4385 node4385Labels = Sparse.eval nodeValue4385 (mixedVector B) := by
  have h := singleton4385 B _hB
  rw [sound965 B _hB _hF, sound1581 B _hB _hF] at h
  norm_num [nodeValue4385, nodeValue965, nodeValue1581, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4386 node4386Labels = Sparse.eval nodeValue4386 (mixedVector B) := by
  have h := singleton4386 B _hB
  rw [sound966 B _hB _hF, sound1582 B _hB _hF] at h
  norm_num [nodeValue4386, nodeValue966, nodeValue1582, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4387 node4387Labels = Sparse.eval nodeValue4387 (mixedVector B) := by
  have h := singleton4387 B _hB
  rw [sound967 B _hB _hF, sound1583 B _hB _hF] at h
  norm_num [nodeValue4387, nodeValue967, nodeValue1583, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4388 node4388Labels = Sparse.eval nodeValue4388 (mixedVector B) := by
  have h := singleton4388 B _hB
  rw [sound969 B _hB _hF, sound1584 B _hB _hF] at h
  norm_num [nodeValue4388, nodeValue969, nodeValue1584, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4389 node4389Labels = Sparse.eval nodeValue4389 (mixedVector B) := by
  have h := singleton4389 B _hB
  rw [sound970 B _hB _hF, sound1585 B _hB _hF] at h
  norm_num [nodeValue4389, nodeValue970, nodeValue1585, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4390 node4390Labels = Sparse.eval nodeValue4390 (mixedVector B) := by
  simpa only [nodeValue4390, Sparse.eval_nil] using zero4390 B _hB _hF

theorem sound4391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4391 node4391Labels = Sparse.eval nodeValue4391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4391) = mixedMoment B node4391 node4391Labels := rfl
  simpa [nodeValue4391, Sparse.eval] using hc.symm

theorem sound4392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4392 node4392Labels = Sparse.eval nodeValue4392 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4392) = mixedMoment B node4392 node4392Labels := rfl
  simpa [nodeValue4392, Sparse.eval] using hc.symm

theorem sound4393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4393 node4393Labels = Sparse.eval nodeValue4393 (mixedVector B) := by
  simpa only [nodeValue4393, Sparse.eval_nil] using zero4393 B _hB _hF

theorem sound4394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4394 node4394Labels = Sparse.eval nodeValue4394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4394) = mixedMoment B node4394 node4394Labels := rfl
  simpa [nodeValue4394, Sparse.eval] using hc.symm

theorem sound4395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4395 node4395Labels = Sparse.eval nodeValue4395 (mixedVector B) := by
  simpa only [nodeValue4395, Sparse.eval_nil] using zero4395 B _hB _hF

theorem sound4396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4396 node4396Labels = Sparse.eval nodeValue4396 (mixedVector B) := by
  have h := singleton4396 B _hB
  rw [sound977 B _hB _hF, sound1597 B _hB _hF] at h
  norm_num [nodeValue4396, nodeValue977, nodeValue1597, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4397 node4397Labels = Sparse.eval nodeValue4397 (mixedVector B) := by
  simpa only [nodeValue4397, Sparse.eval_nil] using zero4397 B _hB _hF

theorem sound4398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4398 node4398Labels = Sparse.eval nodeValue4398 (mixedVector B) := by
  have h := singleton4398 B _hB
  rw [sound979 B _hB _hF, sound1599 B _hB _hF] at h
  norm_num [nodeValue4398, nodeValue979, nodeValue1599, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4399 node4399Labels = Sparse.eval nodeValue4399 (mixedVector B) := by
  have h := singleton4399 B _hB
  rw [sound980 B _hB _hF, sound1616 B _hB _hF] at h
  norm_num [nodeValue4399, nodeValue980, nodeValue1616, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4400 node4400Labels = Sparse.eval nodeValue4400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4400) = mixedMoment B node4400 node4400Labels := rfl
  simpa [nodeValue4400, Sparse.eval] using hc.symm

theorem sound4401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4401 node4401Labels = Sparse.eval nodeValue4401 (mixedVector B) := by
  have h := singleton4401 B _hB
  rw [sound982 B _hB _hF, sound1617 B _hB _hF] at h
  norm_num [nodeValue4401, nodeValue982, nodeValue1617, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4402 node4402Labels = Sparse.eval nodeValue4402 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4402) = mixedMoment B node4402 node4402Labels := rfl
  simpa [nodeValue4402, Sparse.eval] using hc.symm

theorem sound4403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4403 node4403Labels = Sparse.eval nodeValue4403 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4403) = mixedMoment B node4403 node4403Labels := rfl
  simpa [nodeValue4403, Sparse.eval] using hc.symm

theorem sound4404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4404 node4404Labels = Sparse.eval nodeValue4404 (mixedVector B) := by
  have h := singleton4404 B _hB
  rw [sound985 B _hB _hF, sound1618 B _hB _hF] at h
  norm_num [nodeValue4404, nodeValue985, nodeValue1618, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4405 node4405Labels = Sparse.eval nodeValue4405 (mixedVector B) := by
  have h := singleton4405 B _hB
  rw [sound986 B _hB _hF, sound1620 B _hB _hF] at h
  norm_num [nodeValue4405, nodeValue986, nodeValue1620, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4406 node4406Labels = Sparse.eval nodeValue4406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4406) = mixedMoment B node4406 node4406Labels := rfl
  simpa [nodeValue4406, Sparse.eval] using hc.symm

theorem sound4407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4407 node4407Labels = Sparse.eval nodeValue4407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4407) = mixedMoment B node4407 node4407Labels := rfl
  simpa [nodeValue4407, Sparse.eval] using hc.symm

theorem sound4408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4408 node4408Labels = Sparse.eval nodeValue4408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4408) = mixedMoment B node4408 node4408Labels := rfl
  simpa [nodeValue4408, Sparse.eval] using hc.symm

theorem sound4409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4409 node4409Labels = Sparse.eval nodeValue4409 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4409) = mixedMoment B node4409 node4409Labels := rfl
  simpa [nodeValue4409, Sparse.eval] using hc.symm

theorem sound4410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4410 node4410Labels = Sparse.eval nodeValue4410 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4410) = mixedMoment B node4410 node4410Labels := rfl
  simpa [nodeValue4410, Sparse.eval] using hc.symm

theorem sound4411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4411 node4411Labels = Sparse.eval nodeValue4411 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4411) = mixedMoment B node4411 node4411Labels := rfl
  simpa [nodeValue4411, Sparse.eval] using hc.symm

theorem sound4412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4412 node4412Labels = Sparse.eval nodeValue4412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4412) = mixedMoment B node4412 node4412Labels := rfl
  simpa [nodeValue4412, Sparse.eval] using hc.symm

theorem sound4413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4413 node4413Labels = Sparse.eval nodeValue4413 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4413) = mixedMoment B node4413 node4413Labels := rfl
  simpa [nodeValue4413, Sparse.eval] using hc.symm

theorem sound4414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4414 node4414Labels = Sparse.eval nodeValue4414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4414) = mixedMoment B node4414 node4414Labels := rfl
  simpa [nodeValue4414, Sparse.eval] using hc.symm

theorem sound4415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4415 node4415Labels = Sparse.eval nodeValue4415 (mixedVector B) := by
  simpa only [nodeValue4415, Sparse.eval_nil] using zero4415 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
