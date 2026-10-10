import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons83

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5312 node5312Labels = Sparse.eval nodeValue5312 (mixedVector B) := by
  simpa only [nodeValue5312, Sparse.eval_nil] using zero5312 B _hB _hF

theorem sound5313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5313 node5313Labels = Sparse.eval nodeValue5313 (mixedVector B) := by
  simpa only [nodeValue5313, Sparse.eval_nil] using zero5313 B _hB _hF

theorem sound5314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5314 node5314Labels = Sparse.eval nodeValue5314 (mixedVector B) := by
  simpa only [nodeValue5314, Sparse.eval_nil] using zero5314 B _hB _hF

theorem sound5315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5315 node5315Labels = Sparse.eval nodeValue5315 (mixedVector B) := by
  have h := singleton5315 B _hB
  rw [sound3638 B _hB _hF, sound3643 B _hB _hF] at h
  norm_num [nodeValue5315, nodeValue3638, nodeValue3643, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5316 node5316Labels = Sparse.eval nodeValue5316 (mixedVector B) := by
  have h := singleton5316 B _hB
  rw [sound3639 B _hB _hF, sound3645 B _hB _hF] at h
  norm_num [nodeValue5316, nodeValue3639, nodeValue3645, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5317 node5317Labels = Sparse.eval nodeValue5317 (mixedVector B) := by
  have h := singleton5317 B _hB
  rw [sound3640 B _hB _hF, sound3649 B _hB _hF] at h
  norm_num [nodeValue5317, nodeValue3640, nodeValue3649, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5318 node5318Labels = Sparse.eval nodeValue5318 (mixedVector B) := by
  have h := singleton5318 B _hB
  rw [sound3641 B _hB _hF, sound3655 B _hB _hF] at h
  norm_num [nodeValue5318, nodeValue3641, nodeValue3655, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5319 node5319Labels = Sparse.eval nodeValue5319 (mixedVector B) := by
  have h := singleton5319 B _hB
  rw [sound3642 B _hB _hF, sound3662 B _hB _hF] at h
  norm_num [nodeValue5319, nodeValue3642, nodeValue3662, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5320 node5320Labels = Sparse.eval nodeValue5320 (mixedVector B) := by
  have h := singleton5320 B _hB
  rw [sound3646 B _hB _hF, sound3656 B _hB _hF] at h
  norm_num [nodeValue5320, nodeValue3646, nodeValue3656, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5321 node5321Labels = Sparse.eval nodeValue5321 (mixedVector B) := by
  have h := singleton5321 B _hB
  rw [sound3647 B _hB _hF, sound3663 B _hB _hF] at h
  norm_num [nodeValue5321, nodeValue3647, nodeValue3663, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5322 node5322Labels = Sparse.eval nodeValue5322 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5322) = mixedMoment B node5322 node5322Labels := rfl
  simpa [nodeValue5322, Sparse.eval] using hc.symm

theorem sound5323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5323 node5323Labels = Sparse.eval nodeValue5323 (mixedVector B) := by
  simpa only [nodeValue5323, Sparse.eval_nil] using zero5323 B _hB _hF

theorem sound5324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5324 node5324Labels = Sparse.eval nodeValue5324 (mixedVector B) := by
  have h := singleton5324 B _hB
  rw [sound3651 B _hB _hF] at h
  norm_num [nodeValue5324, nodeValue3651, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5325 node5325Labels = Sparse.eval nodeValue5325 (mixedVector B) := by
  simpa only [nodeValue5325, Sparse.eval_nil] using zero5325 B _hB _hF

theorem sound5326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5326 node5326Labels = Sparse.eval nodeValue5326 (mixedVector B) := by
  have h := singleton5326 B _hB
  rw [sound3653 B _hB _hF, sound3657 B _hB _hF] at h
  norm_num [nodeValue5326, nodeValue3653, nodeValue3657, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5327 node5327Labels = Sparse.eval nodeValue5327 (mixedVector B) := by
  simpa only [nodeValue5327, Sparse.eval_nil] using zero5327 B _hB _hF

theorem sound5328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5328 node5328Labels = Sparse.eval nodeValue5328 (mixedVector B) := by
  have h := singleton5328 B _hB
  rw [sound3659 B _hB _hF] at h
  norm_num [nodeValue5328, nodeValue3659, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5329 node5329Labels = Sparse.eval nodeValue5329 (mixedVector B) := by
  have h := singleton5329 B _hB
  rw [sound3660 B _hB _hF] at h
  norm_num [nodeValue5329, nodeValue3660, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5330 node5330Labels = Sparse.eval nodeValue5330 (mixedVector B) := by
  have h := singleton5330 B _hB
  rw [sound3661 B _hB _hF, sound3666 B _hB _hF] at h
  norm_num [nodeValue5330, nodeValue3661, nodeValue3666, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5331 node5331Labels = Sparse.eval nodeValue5331 (mixedVector B) := by
  simpa only [nodeValue5331, Sparse.eval_nil] using zero5331 B _hB _hF

theorem sound5332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5332 node5332Labels = Sparse.eval nodeValue5332 (mixedVector B) := by
  simpa only [nodeValue5332, Sparse.eval_nil] using zero5332 B _hB _hF

theorem sound5333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5333 node5333Labels = Sparse.eval nodeValue5333 (mixedVector B) := by
  have h := singleton5333 B _hB
  rw [sound3668 B _hB _hF, sound3677 B _hB _hF] at h
  norm_num [nodeValue5333, nodeValue3668, nodeValue3677, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5334 node5334Labels = Sparse.eval nodeValue5334 (mixedVector B) := by
  have h := singleton5334 B _hB
  rw [sound3669 B _hB _hF, sound3742 B _hB _hF] at h
  norm_num [nodeValue5334, nodeValue3669, nodeValue3742, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5335 node5335Labels = Sparse.eval nodeValue5335 (mixedVector B) := by
  have h := singleton5335 B _hB
  rw [sound3670 B _hB _hF, sound3753 B _hB _hF] at h
  norm_num [nodeValue5335, nodeValue3670, nodeValue3753, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5336 node5336Labels = Sparse.eval nodeValue5336 (mixedVector B) := by
  have h := singleton5336 B _hB
  rw [sound3671 B _hB _hF, sound3754 B _hB _hF] at h
  norm_num [nodeValue5336, nodeValue3671, nodeValue3754, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5337 node5337Labels = Sparse.eval nodeValue5337 (mixedVector B) := by
  have h := singleton5337 B _hB
  rw [sound3672 B _hB _hF, sound3756 B _hB _hF] at h
  norm_num [nodeValue5337, nodeValue3672, nodeValue3756, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5338 node5338Labels = Sparse.eval nodeValue5338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5338) = mixedMoment B node5338 node5338Labels := rfl
  simpa [nodeValue5338, Sparse.eval] using hc.symm

theorem sound5339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5339 node5339Labels = Sparse.eval nodeValue5339 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5339) = mixedMoment B node5339 node5339Labels := rfl
  simpa [nodeValue5339, Sparse.eval] using hc.symm

theorem sound5340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5340 node5340Labels = Sparse.eval nodeValue5340 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5340) = mixedMoment B node5340 node5340Labels := rfl
  simpa [nodeValue5340, Sparse.eval] using hc.symm

theorem sound5341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5341 node5341Labels = Sparse.eval nodeValue5341 (mixedVector B) := by
  have h := singleton5341 B _hB
  rw [sound3678 B _hB _hF, sound3744 B _hB _hF] at h
  norm_num [nodeValue5341, nodeValue3678, nodeValue3744, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5342 node5342Labels = Sparse.eval nodeValue5342 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5342) = mixedMoment B node5342 node5342Labels := rfl
  simpa [nodeValue5342, Sparse.eval] using hc.symm

theorem sound5343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5343 node5343Labels = Sparse.eval nodeValue5343 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5343) = mixedMoment B node5343 node5343Labels := rfl
  simpa [nodeValue5343, Sparse.eval] using hc.symm

theorem sound5344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5344 node5344Labels = Sparse.eval nodeValue5344 (mixedVector B) := by
  have h := singleton5344 B _hB
  rw [sound3681 B _hB _hF] at h
  norm_num [nodeValue5344, nodeValue3681, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5345 node5345Labels = Sparse.eval nodeValue5345 (mixedVector B) := by
  simpa only [nodeValue5345, Sparse.eval_nil] using zero5345 B _hB _hF

theorem sound5346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5346 node5346Labels = Sparse.eval nodeValue5346 (mixedVector B) := by
  have h := singleton5346 B _hB
  rw [sound3683 B _hB _hF, sound3746 B _hB _hF] at h
  norm_num [nodeValue5346, nodeValue3683, nodeValue3746, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5347 node5347Labels = Sparse.eval nodeValue5347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5347) = mixedMoment B node5347 node5347Labels := rfl
  simpa [nodeValue5347, Sparse.eval] using hc.symm

theorem sound5348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5348 node5348Labels = Sparse.eval nodeValue5348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5348) = mixedMoment B node5348 node5348Labels := rfl
  simpa [nodeValue5348, Sparse.eval] using hc.symm

theorem sound5349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5349 node5349Labels = Sparse.eval nodeValue5349 (mixedVector B) := by
  have h := singleton5349 B _hB
  rw [sound3687 B _hB _hF, sound3749 B _hB _hF] at h
  norm_num [nodeValue5349, nodeValue3687, nodeValue3749, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5350 node5350Labels = Sparse.eval nodeValue5350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5350) = mixedMoment B node5350 node5350Labels := rfl
  simpa [nodeValue5350, Sparse.eval] using hc.symm

theorem sound5351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5351 node5351Labels = Sparse.eval nodeValue5351 (mixedVector B) := by
  have h := singleton5351 B _hB
  rw [sound3689 B _hB _hF, sound3757 B _hB _hF] at h
  norm_num [nodeValue5351, nodeValue3689, nodeValue3757, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5352 node5352Labels = Sparse.eval nodeValue5352 (mixedVector B) := by
  have h := singleton5352 B _hB
  rw [sound3690 B _hB _hF, sound3764 B _hB _hF] at h
  norm_num [nodeValue5352, nodeValue3690, nodeValue3764, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5353 node5353Labels = Sparse.eval nodeValue5353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5353) = mixedMoment B node5353 node5353Labels := rfl
  simpa [nodeValue5353, Sparse.eval] using hc.symm

theorem sound5354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5354 node5354Labels = Sparse.eval nodeValue5354 (mixedVector B) := by
  have h := singleton5354 B _hB
  rw [sound3692 B _hB _hF, sound3769 B _hB _hF] at h
  norm_num [nodeValue5354, nodeValue3692, nodeValue3769, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5355 node5355Labels = Sparse.eval nodeValue5355 (mixedVector B) := by
  have h := singleton5355 B _hB
  rw [sound3693 B _hB _hF, sound3770 B _hB _hF] at h
  norm_num [nodeValue5355, nodeValue3693, nodeValue3770, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5356 node5356Labels = Sparse.eval nodeValue5356 (mixedVector B) := by
  have h := singleton5356 B _hB
  rw [sound3694 B _hB _hF, sound3773 B _hB _hF] at h
  norm_num [nodeValue5356, nodeValue3694, nodeValue3773, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5357 node5357Labels = Sparse.eval nodeValue5357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5357) = mixedMoment B node5357 node5357Labels := rfl
  simpa [nodeValue5357, Sparse.eval] using hc.symm

theorem sound5358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5358 node5358Labels = Sparse.eval nodeValue5358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5358) = mixedMoment B node5358 node5358Labels := rfl
  simpa [nodeValue5358, Sparse.eval] using hc.symm

theorem sound5359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5359 node5359Labels = Sparse.eval nodeValue5359 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5359) = mixedMoment B node5359 node5359Labels := rfl
  simpa [nodeValue5359, Sparse.eval] using hc.symm

theorem sound5360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5360 node5360Labels = Sparse.eval nodeValue5360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5360) = mixedMoment B node5360 node5360Labels := rfl
  simpa [nodeValue5360, Sparse.eval] using hc.symm

theorem sound5361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5361 node5361Labels = Sparse.eval nodeValue5361 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5361) = mixedMoment B node5361 node5361Labels := rfl
  simpa [nodeValue5361, Sparse.eval] using hc.symm

theorem sound5362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5362 node5362Labels = Sparse.eval nodeValue5362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5362) = mixedMoment B node5362 node5362Labels := rfl
  simpa [nodeValue5362, Sparse.eval] using hc.symm

theorem sound5363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5363 node5363Labels = Sparse.eval nodeValue5363 (mixedVector B) := by
  have h := singleton5363 B _hB
  rw [sound3701 B _hB _hF, sound3751 B _hB _hF] at h
  norm_num [nodeValue5363, nodeValue3701, nodeValue3751, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5364 node5364Labels = Sparse.eval nodeValue5364 (mixedVector B) := by
  have h := singleton5364 B _hB
  rw [sound3702 B _hB _hF] at h
  norm_num [nodeValue5364, nodeValue3702, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5365 node5365Labels = Sparse.eval nodeValue5365 (mixedVector B) := by
  have h := singleton5365 B _hB
  rw [sound3703 B _hB _hF, sound3758 B _hB _hF] at h
  norm_num [nodeValue5365, nodeValue3703, nodeValue3758, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5366 node5366Labels = Sparse.eval nodeValue5366 (mixedVector B) := by
  simpa only [nodeValue5366, Sparse.eval_nil] using zero5366 B _hB _hF

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

theorem sound5368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5368 node5368Labels = Sparse.eval nodeValue5368 (mixedVector B) := by
  have h := singleton5368 B _hB
  rw [sound3705 B _hB _hF, sound3767 B _hB _hF] at h
  norm_num [nodeValue5368, nodeValue3705, nodeValue3767, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5369 node5369Labels = Sparse.eval nodeValue5369 (mixedVector B) := by
  simpa only [nodeValue5369, Sparse.eval_nil] using zero5369 B _hB _hF

theorem sound5370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5370 node5370Labels = Sparse.eval nodeValue5370 (mixedVector B) := by
  have h := singleton5370 B _hB
  rw [sound3706 B _hB _hF, sound3771 B _hB _hF] at h
  norm_num [nodeValue5370, nodeValue3706, nodeValue3771, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5371 node5371Labels = Sparse.eval nodeValue5371 (mixedVector B) := by
  simpa only [nodeValue5371, Sparse.eval_nil] using zero5371 B _hB _hF

theorem sound5372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5372 node5372Labels = Sparse.eval nodeValue5372 (mixedVector B) := by
  have h := singleton5372 B _hB
  rw [sound3708 B _hB _hF, sound3791 B _hB _hF] at h
  norm_num [nodeValue5372, nodeValue3708, nodeValue3791, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5373 node5373Labels = Sparse.eval nodeValue5373 (mixedVector B) := by
  have h := singleton5373 B _hB
  rw [sound3709 B _hB _hF, sound3792 B _hB _hF] at h
  norm_num [nodeValue5373, nodeValue3709, nodeValue3792, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5374 node5374Labels = Sparse.eval nodeValue5374 (mixedVector B) := by
  have h := singleton5374 B _hB
  rw [sound3713 B _hB _hF] at h
  norm_num [nodeValue5374, nodeValue3713, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5375 node5375Labels = Sparse.eval nodeValue5375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5375) = mixedMoment B node5375 node5375Labels := rfl
  simpa [nodeValue5375, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
