import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4480 node4480Labels = Sparse.eval nodeValue4480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4480) = mixedMoment B node4480 node4480Labels := rfl
  simpa [nodeValue4480, Sparse.eval] using hc.symm

theorem sound4481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4481 node4481Labels = Sparse.eval nodeValue4481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4481) = mixedMoment B node4481 node4481Labels := rfl
  simpa [nodeValue4481, Sparse.eval] using hc.symm

theorem sound4482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4482 node4482Labels = Sparse.eval nodeValue4482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4482) = mixedMoment B node4482 node4482Labels := rfl
  simpa [nodeValue4482, Sparse.eval] using hc.symm

theorem sound4483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4483 node4483Labels = Sparse.eval nodeValue4483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4483) = mixedMoment B node4483 node4483Labels := rfl
  simpa [nodeValue4483, Sparse.eval] using hc.symm

theorem sound4484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4484 node4484Labels = Sparse.eval nodeValue4484 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4484) = mixedMoment B node4484 node4484Labels := rfl
  simpa [nodeValue4484, Sparse.eval] using hc.symm

theorem sound4485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4485 node4485Labels = Sparse.eval nodeValue4485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4485) = mixedMoment B node4485 node4485Labels := rfl
  simpa [nodeValue4485, Sparse.eval] using hc.symm

theorem sound4486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4486 node4486Labels = Sparse.eval nodeValue4486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4486) = mixedMoment B node4486 node4486Labels := rfl
  simpa [nodeValue4486, Sparse.eval] using hc.symm

theorem sound4487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4487 node4487Labels = Sparse.eval nodeValue4487 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4487) = mixedMoment B node4487 node4487Labels := rfl
  simpa [nodeValue4487, Sparse.eval] using hc.symm

theorem sound4488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4488 node4488Labels = Sparse.eval nodeValue4488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4488) = mixedMoment B node4488 node4488Labels := rfl
  simpa [nodeValue4488, Sparse.eval] using hc.symm

theorem sound4489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4489 node4489Labels = Sparse.eval nodeValue4489 (mixedVector B) := by
  have h := singleton4489 B _hB
  rw [sound1073 B _hB _hF, sound1648 B _hB _hF] at h
  norm_num [nodeValue4489, nodeValue1073, nodeValue1648, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4490 node4490Labels = Sparse.eval nodeValue4490 (mixedVector B) := by
  have h := singleton4490 B _hB
  rw [sound1074 B _hB _hF, sound1650 B _hB _hF] at h
  norm_num [nodeValue4490, nodeValue1074, nodeValue1650, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4491 node4491Labels = Sparse.eval nodeValue4491 (mixedVector B) := by
  have h := singleton4491 B _hB
  rw [sound1075 B _hB _hF, sound1653 B _hB _hF] at h
  norm_num [nodeValue4491, nodeValue1075, nodeValue1653, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4492 node4492Labels = Sparse.eval nodeValue4492 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4492) = mixedMoment B node4492 node4492Labels := rfl
  simpa [nodeValue4492, Sparse.eval] using hc.symm

theorem sound4493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4493 node4493Labels = Sparse.eval nodeValue4493 (mixedVector B) := by
  have h := singleton4493 B _hB
  rw [sound1077 B _hB _hF] at h
  norm_num [nodeValue4493, nodeValue1077, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4494 node4494Labels = Sparse.eval nodeValue4494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4494) = mixedMoment B node4494 node4494Labels := rfl
  simpa [nodeValue4494, Sparse.eval] using hc.symm

theorem sound4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4495 node4495Labels = Sparse.eval nodeValue4495 (mixedVector B) := by
  have h := singleton4495 B _hB
  rw [sound1079 B _hB _hF, sound1708 B _hB _hF] at h
  norm_num [nodeValue4495, nodeValue1079, nodeValue1708, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4496 node4496Labels = Sparse.eval nodeValue4496 (mixedVector B) := by
  have h := singleton4496 B _hB
  rw [sound1080 B _hB _hF, sound1710 B _hB _hF] at h
  norm_num [nodeValue4496, nodeValue1080, nodeValue1710, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = Sparse.eval nodeValue4497 (mixedVector B) := by
  simpa only [nodeValue4497, Sparse.eval_nil] using zero4497 B _hB _hF

theorem sound4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = Sparse.eval nodeValue4498 (mixedVector B) := by
  simpa only [nodeValue4498, Sparse.eval_nil] using zero4498 B _hB _hF

theorem sound4499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4499 node4499Labels = Sparse.eval nodeValue4499 (mixedVector B) := by
  have h := singleton4499 B _hB
  rw [sound1083 B _hB _hF, sound1728 B _hB _hF] at h
  norm_num [nodeValue4499, nodeValue1083, nodeValue1728, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4500 node4500Labels = Sparse.eval nodeValue4500 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4500) = mixedMoment B node4500 node4500Labels := rfl
  simpa [nodeValue4500, Sparse.eval] using hc.symm

theorem sound4501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4501 node4501Labels = Sparse.eval nodeValue4501 (mixedVector B) := by
  simpa only [nodeValue4501, Sparse.eval_nil] using zero4501 B _hB _hF

theorem sound4502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = Sparse.eval nodeValue4502 (mixedVector B) := by
  simpa only [nodeValue4502, Sparse.eval_nil] using zero4502 B _hB _hF

theorem sound4503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4503 node4503Labels = Sparse.eval nodeValue4503 (mixedVector B) := by
  have h := singleton4503 B _hB
  rw [sound1087 B _hB _hF, sound1739 B _hB _hF] at h
  norm_num [nodeValue4503, nodeValue1087, nodeValue1739, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4504 node4504Labels = Sparse.eval nodeValue4504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4504) = mixedMoment B node4504 node4504Labels := rfl
  simpa [nodeValue4504, Sparse.eval] using hc.symm

theorem sound4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = Sparse.eval nodeValue4505 (mixedVector B) := by
  simpa only [nodeValue4505, Sparse.eval_nil] using zero4505 B _hB _hF

theorem sound4506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4506 node4506Labels = Sparse.eval nodeValue4506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4506) = mixedMoment B node4506 node4506Labels := rfl
  simpa [nodeValue4506, Sparse.eval] using hc.symm

theorem sound4507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4507 node4507Labels = Sparse.eval nodeValue4507 (mixedVector B) := by
  have h := singleton4507 B _hB
  rw [sound1091 B _hB _hF, sound1756 B _hB _hF] at h
  norm_num [nodeValue4507, nodeValue1091, nodeValue1756, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4508 node4508Labels = Sparse.eval nodeValue4508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4508) = mixedMoment B node4508 node4508Labels := rfl
  simpa [nodeValue4508, Sparse.eval] using hc.symm

theorem sound4509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4509 node4509Labels = Sparse.eval nodeValue4509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4509) = mixedMoment B node4509 node4509Labels := rfl
  simpa [nodeValue4509, Sparse.eval] using hc.symm

theorem sound4510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4510 node4510Labels = Sparse.eval nodeValue4510 (mixedVector B) := by
  have h := singleton4510 B _hB
  rw [sound1094 B _hB _hF, sound1741 B _hB _hF] at h
  norm_num [nodeValue4510, nodeValue1094, nodeValue1741, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = Sparse.eval nodeValue4511 (mixedVector B) := by
  simpa only [nodeValue4511, Sparse.eval_nil] using zero4511 B _hB _hF

theorem sound4512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4512 node4512Labels = Sparse.eval nodeValue4512 (mixedVector B) := by
  simpa only [nodeValue4512, Sparse.eval_nil] using zero4512 B _hB _hF

theorem sound4513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4513 node4513Labels = Sparse.eval nodeValue4513 (mixedVector B) := by
  have h := singleton4513 B _hB
  rw [sound1097 B _hB _hF, sound3232 B _hB _hF] at h
  norm_num [nodeValue4513, nodeValue1097, nodeValue3232, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4514 node4514Labels = Sparse.eval nodeValue4514 (mixedVector B) := by
  have h := singleton4514 B _hB
  rw [sound1098 B _hB _hF, sound1894 B _hB _hF] at h
  norm_num [nodeValue4514, nodeValue1098, nodeValue1894, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4515 node4515Labels = Sparse.eval nodeValue4515 (mixedVector B) := by
  have h := singleton4515 B _hB
  rw [sound1099 B _hB _hF, sound3233 B _hB _hF] at h
  norm_num [nodeValue4515, nodeValue1099, nodeValue3233, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4516 node4516Labels = Sparse.eval nodeValue4516 (mixedVector B) := by
  have h := singleton4516 B _hB
  rw [sound1100 B _hB _hF, sound3234 B _hB _hF] at h
  norm_num [nodeValue4516, nodeValue1100, nodeValue3234, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4517 node4517Labels = Sparse.eval nodeValue4517 (mixedVector B) := by
  have h := singleton4517 B _hB
  rw [sound1101 B _hB _hF, sound3235 B _hB _hF] at h
  norm_num [nodeValue4517, nodeValue1101, nodeValue3235, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4518 node4518Labels = Sparse.eval nodeValue4518 (mixedVector B) := by
  have h := singleton4518 B _hB
  rw [sound1102 B _hB _hF, sound3236 B _hB _hF] at h
  norm_num [nodeValue4518, nodeValue1102, nodeValue3236, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4519 node4519Labels = Sparse.eval nodeValue4519 (mixedVector B) := by
  have h := singleton4519 B _hB
  rw [sound1103 B _hB _hF, sound1858 B _hB _hF] at h
  norm_num [nodeValue4519, nodeValue1103, nodeValue1858, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4520 node4520Labels = Sparse.eval nodeValue4520 (mixedVector B) := by
  have h := singleton4520 B _hB
  rw [sound1104 B _hB _hF, sound3237 B _hB _hF] at h
  norm_num [nodeValue4520, nodeValue1104, nodeValue3237, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4521 node4521Labels = Sparse.eval nodeValue4521 (mixedVector B) := by
  have h := singleton4521 B _hB
  rw [sound1105 B _hB _hF, sound1887 B _hB _hF] at h
  norm_num [nodeValue4521, nodeValue1105, nodeValue1887, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4522 node4522Labels = Sparse.eval nodeValue4522 (mixedVector B) := by
  have h := singleton4522 B _hB
  rw [sound1106 B _hB _hF, sound3249 B _hB _hF] at h
  norm_num [nodeValue4522, nodeValue1106, nodeValue3249, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4523 node4523Labels = Sparse.eval nodeValue4523 (mixedVector B) := by
  have h := singleton4523 B _hB
  rw [sound1107 B _hB _hF, sound3250 B _hB _hF] at h
  norm_num [nodeValue4523, nodeValue1107, nodeValue3250, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4524 node4524Labels = Sparse.eval nodeValue4524 (mixedVector B) := by
  have h := singleton4524 B _hB
  rw [sound1108 B _hB _hF, sound3251 B _hB _hF] at h
  norm_num [nodeValue4524, nodeValue1108, nodeValue3251, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4525 node4525Labels = Sparse.eval nodeValue4525 (mixedVector B) := by
  have h := singleton4525 B _hB
  rw [sound1109 B _hB _hF, sound1849 B _hB _hF] at h
  norm_num [nodeValue4525, nodeValue1109, nodeValue1849, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4526 node4526Labels = Sparse.eval nodeValue4526 (mixedVector B) := by
  have h := singleton4526 B _hB
  rw [sound1110 B _hB _hF, sound3252 B _hB _hF] at h
  norm_num [nodeValue4526, nodeValue1110, nodeValue3252, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4527 node4527Labels = Sparse.eval nodeValue4527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4527) = mixedMoment B node4527 node4527Labels := rfl
  simpa [nodeValue4527, Sparse.eval] using hc.symm

theorem sound4528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4528 node4528Labels = Sparse.eval nodeValue4528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4528) = mixedMoment B node4528 node4528Labels := rfl
  simpa [nodeValue4528, Sparse.eval] using hc.symm

theorem sound4529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4529 node4529Labels = Sparse.eval nodeValue4529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4529) = mixedMoment B node4529 node4529Labels := rfl
  simpa [nodeValue4529, Sparse.eval] using hc.symm

theorem sound4530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4530 node4530Labels = Sparse.eval nodeValue4530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4530) = mixedMoment B node4530 node4530Labels := rfl
  simpa [nodeValue4530, Sparse.eval] using hc.symm

theorem sound4531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4531 node4531Labels = Sparse.eval nodeValue4531 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4531) = mixedMoment B node4531 node4531Labels := rfl
  simpa [nodeValue4531, Sparse.eval] using hc.symm

theorem sound4532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4532 node4532Labels = Sparse.eval nodeValue4532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4532) = mixedMoment B node4532 node4532Labels := rfl
  simpa [nodeValue4532, Sparse.eval] using hc.symm

theorem sound4533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4533 node4533Labels = Sparse.eval nodeValue4533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4533) = mixedMoment B node4533 node4533Labels := rfl
  simpa [nodeValue4533, Sparse.eval] using hc.symm

theorem sound4534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4534 node4534Labels = Sparse.eval nodeValue4534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4534) = mixedMoment B node4534 node4534Labels := rfl
  simpa [nodeValue4534, Sparse.eval] using hc.symm

theorem sound4535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4535 node4535Labels = Sparse.eval nodeValue4535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4535) = mixedMoment B node4535 node4535Labels := rfl
  simpa [nodeValue4535, Sparse.eval] using hc.symm

theorem sound4536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4536 node4536Labels = Sparse.eval nodeValue4536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4536) = mixedMoment B node4536 node4536Labels := rfl
  simpa [nodeValue4536, Sparse.eval] using hc.symm

theorem sound4537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4537 node4537Labels = Sparse.eval nodeValue4537 (mixedVector B) := by
  have h := singleton4537 B _hB
  rw [sound1122 B _hB _hF, sound3253 B _hB _hF] at h
  norm_num [nodeValue4537, nodeValue1122, nodeValue3253, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4538 node4538Labels = Sparse.eval nodeValue4538 (mixedVector B) := by
  have h := singleton4538 B _hB
  rw [sound1123 B _hB _hF, sound1937 B _hB _hF] at h
  norm_num [nodeValue4538, nodeValue1123, nodeValue1937, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4539 node4539Labels = Sparse.eval nodeValue4539 (mixedVector B) := by
  have h := singleton4539 B _hB
  rw [sound1124 B _hB _hF, sound3254 B _hB _hF] at h
  norm_num [nodeValue4539, nodeValue1124, nodeValue3254, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4540 node4540Labels = Sparse.eval nodeValue4540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4540) = mixedMoment B node4540 node4540Labels := rfl
  simpa [nodeValue4540, Sparse.eval] using hc.symm

theorem sound4541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4541 node4541Labels = Sparse.eval nodeValue4541 (mixedVector B) := by
  have h := singleton4541 B _hB
  rw [sound1126 B _hB _hF, sound3256 B _hB _hF] at h
  norm_num [nodeValue4541, nodeValue1126, nodeValue3256, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4542 node4542Labels = Sparse.eval nodeValue4542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4542) = mixedMoment B node4542 node4542Labels := rfl
  simpa [nodeValue4542, Sparse.eval] using hc.symm

theorem sound4543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4543 node4543Labels = Sparse.eval nodeValue4543 (mixedVector B) := by
  have h := singleton4543 B _hB
  rw [sound1128 B _hB _hF, sound2184 B _hB _hF] at h
  norm_num [nodeValue4543, nodeValue1128, nodeValue2184, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
