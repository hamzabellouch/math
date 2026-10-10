import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons69

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4416 node4416Labels = Sparse.eval nodeValue4416 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4416) = mixedMoment B node4416 node4416Labels := rfl
  simpa [nodeValue4416, Sparse.eval] using hc.symm

theorem sound4417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4417 node4417Labels = Sparse.eval nodeValue4417 (mixedVector B) := by
  have h := singleton4417 B _hB
  rw [sound998 B _hB _hF, sound1600 B _hB _hF] at h
  norm_num [nodeValue4417, nodeValue998, nodeValue1600, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4418 node4418Labels = Sparse.eval nodeValue4418 (mixedVector B) := by
  have h := singleton4418 B _hB
  rw [sound999 B _hB _hF, sound1602 B _hB _hF] at h
  norm_num [nodeValue4418, nodeValue999, nodeValue1602, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4419 node4419Labels = Sparse.eval nodeValue4419 (mixedVector B) := by
  have h := singleton4419 B _hB
  rw [sound1000 B _hB _hF, sound1605 B _hB _hF] at h
  norm_num [nodeValue4419, nodeValue1000, nodeValue1605, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4420 node4420Labels = Sparse.eval nodeValue4420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4420) = mixedMoment B node4420 node4420Labels := rfl
  simpa [nodeValue4420, Sparse.eval] using hc.symm

theorem sound4421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4421 node4421Labels = Sparse.eval nodeValue4421 (mixedVector B) := by
  have h := singleton4421 B _hB
  rw [sound1002 B _hB _hF] at h
  norm_num [nodeValue4421, nodeValue1002, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4422 node4422Labels = Sparse.eval nodeValue4422 (mixedVector B) := by
  simpa only [nodeValue4422, Sparse.eval_nil] using zero4422 B _hB _hF

theorem sound4423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4423 node4423Labels = Sparse.eval nodeValue4423 (mixedVector B) := by
  simpa only [nodeValue4423, Sparse.eval_nil] using zero4423 B _hB _hF

theorem sound4424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4424 node4424Labels = Sparse.eval nodeValue4424 (mixedVector B) := by
  have h := singleton4424 B _hB
  rw [sound1005 B _hB _hF, sound1623 B _hB _hF] at h
  norm_num [nodeValue4424, nodeValue1005, nodeValue1623, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4425 node4425Labels = Sparse.eval nodeValue4425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4425) = mixedMoment B node4425 node4425Labels := rfl
  simpa [nodeValue4425, Sparse.eval] using hc.symm

theorem sound4426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4426 node4426Labels = Sparse.eval nodeValue4426 (mixedVector B) := by
  simpa only [nodeValue4426, Sparse.eval_nil] using zero4426 B _hB _hF

theorem sound4427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4427 node4427Labels = Sparse.eval nodeValue4427 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4427) = mixedMoment B node4427 node4427Labels := rfl
  simpa [nodeValue4427, Sparse.eval] using hc.symm

theorem sound4428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4428 node4428Labels = Sparse.eval nodeValue4428 (mixedVector B) := by
  have h := singleton4428 B _hB
  rw [sound1009 B _hB _hF, sound1630 B _hB _hF] at h
  norm_num [nodeValue4428, nodeValue1009, nodeValue1630, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4429 node4429Labels = Sparse.eval nodeValue4429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4429) = mixedMoment B node4429 node4429Labels := rfl
  simpa [nodeValue4429, Sparse.eval] using hc.symm

theorem sound4430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4430 node4430Labels = Sparse.eval nodeValue4430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4430) = mixedMoment B node4430 node4430Labels := rfl
  simpa [nodeValue4430, Sparse.eval] using hc.symm

theorem sound4431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4431 node4431Labels = Sparse.eval nodeValue4431 (mixedVector B) := by
  have h := singleton4431 B _hB
  rw [sound1012 B _hB _hF, sound1627 B _hB _hF] at h
  norm_num [nodeValue4431, nodeValue1012, nodeValue1627, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4432 node4432Labels = Sparse.eval nodeValue4432 (mixedVector B) := by
  simpa only [nodeValue4432, Sparse.eval_nil] using zero4432 B _hB _hF

theorem sound4433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4433 node4433Labels = Sparse.eval nodeValue4433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4433) = mixedMoment B node4433 node4433Labels := rfl
  simpa [nodeValue4433, Sparse.eval] using hc.symm

theorem sound4434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4434 node4434Labels = Sparse.eval nodeValue4434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4434) = mixedMoment B node4434 node4434Labels := rfl
  simpa [nodeValue4434, Sparse.eval] using hc.symm

theorem sound4435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4435 node4435Labels = Sparse.eval nodeValue4435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4435) = mixedMoment B node4435 node4435Labels := rfl
  simpa [nodeValue4435, Sparse.eval] using hc.symm

theorem sound4436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4436 node4436Labels = Sparse.eval nodeValue4436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4436) = mixedMoment B node4436 node4436Labels := rfl
  simpa [nodeValue4436, Sparse.eval] using hc.symm

theorem sound4437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4437 node4437Labels = Sparse.eval nodeValue4437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4437) = mixedMoment B node4437 node4437Labels := rfl
  simpa [nodeValue4437, Sparse.eval] using hc.symm

theorem sound4438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4438 node4438Labels = Sparse.eval nodeValue4438 (mixedVector B) := by
  simpa only [nodeValue4438, Sparse.eval_nil] using zero4438 B _hB _hF

theorem sound4439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4439 node4439Labels = Sparse.eval nodeValue4439 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4439) = mixedMoment B node4439 node4439Labels := rfl
  simpa [nodeValue4439, Sparse.eval] using hc.symm

theorem sound4440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4440 node4440Labels = Sparse.eval nodeValue4440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4440) = mixedMoment B node4440 node4440Labels := rfl
  simpa [nodeValue4440, Sparse.eval] using hc.symm

theorem sound4441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4441 node4441Labels = Sparse.eval nodeValue4441 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4441) = mixedMoment B node4441 node4441Labels := rfl
  simpa [nodeValue4441, Sparse.eval] using hc.symm

theorem sound4442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4442 node4442Labels = Sparse.eval nodeValue4442 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4442) = mixedMoment B node4442 node4442Labels := rfl
  simpa [nodeValue4442, Sparse.eval] using hc.symm

theorem sound4443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4443 node4443Labels = Sparse.eval nodeValue4443 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4443) = mixedMoment B node4443 node4443Labels := rfl
  simpa [nodeValue4443, Sparse.eval] using hc.symm

theorem sound4444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4444 node4444Labels = Sparse.eval nodeValue4444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4444) = mixedMoment B node4444 node4444Labels := rfl
  simpa [nodeValue4444, Sparse.eval] using hc.symm

theorem sound4445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4445 node4445Labels = Sparse.eval nodeValue4445 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4445) = mixedMoment B node4445 node4445Labels := rfl
  simpa [nodeValue4445, Sparse.eval] using hc.symm

theorem sound4446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4446 node4446Labels = Sparse.eval nodeValue4446 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4446) = mixedMoment B node4446 node4446Labels := rfl
  simpa [nodeValue4446, Sparse.eval] using hc.symm

theorem sound4447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4447 node4447Labels = Sparse.eval nodeValue4447 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4447) = mixedMoment B node4447 node4447Labels := rfl
  simpa [nodeValue4447, Sparse.eval] using hc.symm

theorem sound4448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4448 node4448Labels = Sparse.eval nodeValue4448 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4448) = mixedMoment B node4448 node4448Labels := rfl
  simpa [nodeValue4448, Sparse.eval] using hc.symm

theorem sound4449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4449 node4449Labels = Sparse.eval nodeValue4449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4449) = mixedMoment B node4449 node4449Labels := rfl
  simpa [nodeValue4449, Sparse.eval] using hc.symm

theorem sound4450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4450 node4450Labels = Sparse.eval nodeValue4450 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4450) = mixedMoment B node4450 node4450Labels := rfl
  simpa [nodeValue4450, Sparse.eval] using hc.symm

theorem sound4451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4451 node4451Labels = Sparse.eval nodeValue4451 (mixedVector B) := by
  have h := singleton4451 B _hB
  rw [sound1034 B _hB _hF, sound1644 B _hB _hF] at h
  norm_num [nodeValue4451, nodeValue1034, nodeValue1644, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4452 node4452Labels = Sparse.eval nodeValue4452 (mixedVector B) := by
  have h := singleton4452 B _hB
  rw [sound1035 B _hB _hF, sound1645 B _hB _hF] at h
  norm_num [nodeValue4452, nodeValue1035, nodeValue1645, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4453 node4453Labels = Sparse.eval nodeValue4453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4453) = mixedMoment B node4453 node4453Labels := rfl
  simpa [nodeValue4453, Sparse.eval] using hc.symm

theorem sound4454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4454 node4454Labels = Sparse.eval nodeValue4454 (mixedVector B) := by
  have h := singleton4454 B _hB
  rw [sound1037 B _hB _hF, sound1647 B _hB _hF] at h
  norm_num [nodeValue4454, nodeValue1037, nodeValue1647, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4455 node4455Labels = Sparse.eval nodeValue4455 (mixedVector B) := by
  simpa only [nodeValue4455, Sparse.eval_nil] using zero4455 B _hB _hF

theorem sound4456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4456 node4456Labels = Sparse.eval nodeValue4456 (mixedVector B) := by
  have h := singleton4456 B _hB
  rw [sound1039 B _hB _hF, sound1706 B _hB _hF] at h
  norm_num [nodeValue4456, nodeValue1039, nodeValue1706, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4457 node4457Labels = Sparse.eval nodeValue4457 (mixedVector B) := by
  have h := singleton4457 B _hB
  rw [sound1040 B _hB _hF, sound1707 B _hB _hF] at h
  norm_num [nodeValue4457, nodeValue1040, nodeValue1707, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4459 node4459Labels = Sparse.eval nodeValue4459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4459) = mixedMoment B node4459 node4459Labels := rfl
  simpa [nodeValue4459, Sparse.eval] using hc.symm

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4461 node4461Labels = Sparse.eval nodeValue4461 (mixedVector B) := by
  have h := singleton4461 B _hB
  rw [sound1044 B _hB _hF, sound1737 B _hB _hF] at h
  norm_num [nodeValue4461, nodeValue1044, nodeValue1737, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4462 node4462Labels = Sparse.eval nodeValue4462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4462) = mixedMoment B node4462 node4462Labels := rfl
  simpa [nodeValue4462, Sparse.eval] using hc.symm

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4464 node4464Labels = Sparse.eval nodeValue4464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4464) = mixedMoment B node4464 node4464Labels := rfl
  simpa [nodeValue4464, Sparse.eval] using hc.symm

theorem sound4465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4465 node4465Labels = Sparse.eval nodeValue4465 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4465) = mixedMoment B node4465 node4465Labels := rfl
  simpa [nodeValue4465, Sparse.eval] using hc.symm

theorem sound4466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4466 node4466Labels = Sparse.eval nodeValue4466 (mixedVector B) := by
  have h := singleton4466 B _hB
  rw [sound1049 B _hB _hF, sound1738 B _hB _hF] at h
  norm_num [nodeValue4466, nodeValue1049, nodeValue1738, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4467 node4467Labels = Sparse.eval nodeValue4467 (mixedVector B) := by
  have h := singleton4467 B _hB
  rw [sound1050 B _hB _hF, sound1751 B _hB _hF] at h
  norm_num [nodeValue4467, nodeValue1050, nodeValue1751, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4468 node4468Labels = Sparse.eval nodeValue4468 (mixedVector B) := by
  have h := singleton4468 B _hB
  rw [sound1051 B _hB _hF, sound1752 B _hB _hF] at h
  norm_num [nodeValue4468, nodeValue1051, nodeValue1752, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4469 node4469Labels = Sparse.eval nodeValue4469 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4469) = mixedMoment B node4469 node4469Labels := rfl
  simpa [nodeValue4469, Sparse.eval] using hc.symm

theorem sound4470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4470 node4470Labels = Sparse.eval nodeValue4470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4470) = mixedMoment B node4470 node4470Labels := rfl
  simpa [nodeValue4470, Sparse.eval] using hc.symm

theorem sound4471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4471 node4471Labels = Sparse.eval nodeValue4471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4471) = mixedMoment B node4471 node4471Labels := rfl
  simpa [nodeValue4471, Sparse.eval] using hc.symm

theorem sound4472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4472 node4472Labels = Sparse.eval nodeValue4472 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4472) = mixedMoment B node4472 node4472Labels := rfl
  simpa [nodeValue4472, Sparse.eval] using hc.symm

theorem sound4473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4473 node4473Labels = Sparse.eval nodeValue4473 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4473) = mixedMoment B node4473 node4473Labels := rfl
  simpa [nodeValue4473, Sparse.eval] using hc.symm

theorem sound4474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4474 node4474Labels = Sparse.eval nodeValue4474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4474) = mixedMoment B node4474 node4474Labels := rfl
  simpa [nodeValue4474, Sparse.eval] using hc.symm

theorem sound4475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4475 node4475Labels = Sparse.eval nodeValue4475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4475) = mixedMoment B node4475 node4475Labels := rfl
  simpa [nodeValue4475, Sparse.eval] using hc.symm

theorem sound4476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4476 node4476Labels = Sparse.eval nodeValue4476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4476) = mixedMoment B node4476 node4476Labels := rfl
  simpa [nodeValue4476, Sparse.eval] using hc.symm

theorem sound4477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4477 node4477Labels = Sparse.eval nodeValue4477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4477) = mixedMoment B node4477 node4477Labels := rfl
  simpa [nodeValue4477, Sparse.eval] using hc.symm

theorem sound4478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4478 node4478Labels = Sparse.eval nodeValue4478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4478) = mixedMoment B node4478 node4478Labels := rfl
  simpa [nodeValue4478, Sparse.eval] using hc.symm

theorem sound4479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4479 node4479Labels = Sparse.eval nodeValue4479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4479) = mixedMoment B node4479 node4479Labels := rfl
  simpa [nodeValue4479, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
