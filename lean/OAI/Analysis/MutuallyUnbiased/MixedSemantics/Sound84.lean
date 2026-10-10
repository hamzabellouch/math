import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5376 node5376Labels = Sparse.eval nodeValue5376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5376) = mixedMoment B node5376 node5376Labels := rfl
  simpa [nodeValue5376, Sparse.eval] using hc.symm

theorem sound5377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5377 node5377Labels = Sparse.eval nodeValue5377 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5377) = mixedMoment B node5377 node5377Labels := rfl
  simpa [nodeValue5377, Sparse.eval] using hc.symm

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5379 node5379Labels = Sparse.eval nodeValue5379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5379) = mixedMoment B node5379 node5379Labels := rfl
  simpa [nodeValue5379, Sparse.eval] using hc.symm

theorem sound5380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5380 node5380Labels = Sparse.eval nodeValue5380 (mixedVector B) := by
  have h := singleton5380 B _hB
  rw [sound3721 B _hB _hF, sound3836 B _hB _hF] at h
  norm_num [nodeValue5380, nodeValue3721, nodeValue3836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5381 node5381Labels = Sparse.eval nodeValue5381 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5381) = mixedMoment B node5381 node5381Labels := rfl
  simpa [nodeValue5381, Sparse.eval] using hc.symm

theorem sound5382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5382 node5382Labels = Sparse.eval nodeValue5382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5382) = mixedMoment B node5382 node5382Labels := rfl
  simpa [nodeValue5382, Sparse.eval] using hc.symm

theorem sound5383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5383 node5383Labels = Sparse.eval nodeValue5383 (mixedVector B) := by
  have h := singleton5383 B _hB
  rw [sound3731 B _hB _hF, sound3867 B _hB _hF] at h
  norm_num [nodeValue5383, nodeValue3731, nodeValue3867, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5384 node5384Labels = Sparse.eval nodeValue5384 (mixedVector B) := by
  have h := singleton5384 B _hB
  rw [sound3732 B _hB _hF, sound3811 B _hB _hF] at h
  norm_num [nodeValue5384, nodeValue3732, nodeValue3811, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5385 node5385Labels = Sparse.eval nodeValue5385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5385) = mixedMoment B node5385 node5385Labels := rfl
  simpa [nodeValue5385, Sparse.eval] using hc.symm

theorem sound5386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5386 node5386Labels = Sparse.eval nodeValue5386 (mixedVector B) := by
  have h := singleton5386 B _hB
  rw [sound3735 B _hB _hF, sound3890 B _hB _hF] at h
  norm_num [nodeValue5386, nodeValue3735, nodeValue3890, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5387 node5387Labels = Sparse.eval nodeValue5387 (mixedVector B) := by
  have h := singleton5387 B _hB
  rw [sound3736 B _hB _hF, sound3891 B _hB _hF] at h
  norm_num [nodeValue5387, nodeValue3736, nodeValue3891, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5388 node5388Labels = Sparse.eval nodeValue5388 (mixedVector B) := by
  have h := singleton5388 B _hB
  rw [sound3737 B _hB _hF, sound3892 B _hB _hF] at h
  norm_num [nodeValue5388, nodeValue3737, nodeValue3892, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5389 node5389Labels = Sparse.eval nodeValue5389 (mixedVector B) := by
  have h := singleton5389 B _hB
  rw [sound3740 B _hB _hF, sound3893 B _hB _hF] at h
  norm_num [nodeValue5389, nodeValue3740, nodeValue3893, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5390 node5390Labels = Sparse.eval nodeValue5390 (mixedVector B) := by
  have h := singleton5390 B _hB
  rw [sound3741 B _hB _hF, sound3894 B _hB _hF] at h
  norm_num [nodeValue5390, nodeValue3741, nodeValue3894, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5391 node5391Labels = Sparse.eval nodeValue5391 (mixedVector B) := by
  have h := singleton5391 B _hB
  rw [sound3776 B _hB _hF, sound3778 B _hB _hF] at h
  norm_num [nodeValue5391, nodeValue3776, nodeValue3778, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5392 node5392Labels = Sparse.eval nodeValue5392 (mixedVector B) := by
  simpa only [nodeValue5392, Sparse.eval_nil] using zero5392 B _hB _hF

theorem sound5393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5393 node5393Labels = Sparse.eval nodeValue5393 (mixedVector B) := by
  have h := singleton5393 B _hB
  rw [sound3779 B _hB _hF, sound3797 B _hB _hF] at h
  norm_num [nodeValue5393, nodeValue3779, nodeValue3797, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5394 node5394Labels = Sparse.eval nodeValue5394 (mixedVector B) := by
  simpa only [nodeValue5394, Sparse.eval_nil] using zero5394 B _hB _hF

theorem sound5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5395 node5395Labels = Sparse.eval nodeValue5395 (mixedVector B) := by
  have h := singleton5395 B _hB
  rw [sound3781 B _hB _hF, sound3794 B _hB _hF] at h
  norm_num [nodeValue5395, nodeValue3781, nodeValue3794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5396 node5396Labels = Sparse.eval nodeValue5396 (mixedVector B) := by
  simpa only [nodeValue5396, Sparse.eval_nil] using zero5396 B _hB _hF

theorem sound5397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5397 node5397Labels = Sparse.eval nodeValue5397 (mixedVector B) := by
  have h := singleton5397 B _hB
  rw [sound3782 B _hB _hF, sound3796 B _hB _hF] at h
  norm_num [nodeValue5397, nodeValue3782, nodeValue3796, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5398 node5398Labels = Sparse.eval nodeValue5398 (mixedVector B) := by
  have h := singleton5398 B _hB
  rw [sound3784 B _hB _hF] at h
  norm_num [nodeValue5398, nodeValue3784, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5399 node5399Labels = Sparse.eval nodeValue5399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5399) = mixedMoment B node5399 node5399Labels := rfl
  simpa [nodeValue5399, Sparse.eval] using hc.symm

theorem sound5400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5400 node5400Labels = Sparse.eval nodeValue5400 (mixedVector B) := by
  have h := singleton5400 B _hB
  rw [sound3786 B _hB _hF, sound3799 B _hB _hF] at h
  norm_num [nodeValue5400, nodeValue3786, nodeValue3799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5401 node5401Labels = Sparse.eval nodeValue5401 (mixedVector B) := by
  have h := singleton5401 B _hB
  rw [sound3787 B _hB _hF, sound3804 B _hB _hF] at h
  norm_num [nodeValue5401, nodeValue3787, nodeValue3804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5402 node5402Labels = Sparse.eval nodeValue5402 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5402) = mixedMoment B node5402 node5402Labels := rfl
  simpa [nodeValue5402, Sparse.eval] using hc.symm

theorem sound5403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5403 node5403Labels = Sparse.eval nodeValue5403 (mixedVector B) := by
  have h := singleton5403 B _hB
  rw [sound3789 B _hB _hF, sound3810 B _hB _hF] at h
  norm_num [nodeValue5403, nodeValue3789, nodeValue3810, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5404 node5404Labels = Sparse.eval nodeValue5404 (mixedVector B) := by
  have h := singleton5404 B _hB
  rw [sound3790 B _hB _hF, sound3815 B _hB _hF] at h
  norm_num [nodeValue5404, nodeValue3790, nodeValue3815, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5405 node5405Labels = Sparse.eval nodeValue5405 (mixedVector B) := by
  have h := singleton5405 B _hB
  rw [sound3800 B _hB _hF, sound3805 B _hB _hF] at h
  norm_num [nodeValue5405, nodeValue3800, nodeValue3805, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5407 node5407Labels = Sparse.eval nodeValue5407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5407) = mixedMoment B node5407 node5407Labels := rfl
  simpa [nodeValue5407, Sparse.eval] using hc.symm

theorem sound5408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5408 node5408Labels = Sparse.eval nodeValue5408 (mixedVector B) := by
  simpa only [nodeValue5408, Sparse.eval_nil] using zero5408 B _hB _hF

theorem sound5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = Sparse.eval nodeValue5409 (mixedVector B) := by
  simpa only [nodeValue5409, Sparse.eval_nil] using zero5409 B _hB _hF

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

theorem sound5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5411 node5411Labels = Sparse.eval nodeValue5411 (mixedVector B) := by
  have h := singleton5411 B _hB
  rw [sound3809 B _hB _hF, sound3813 B _hB _hF] at h
  norm_num [nodeValue5411, nodeValue3809, nodeValue3813, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5413 node5413Labels = Sparse.eval nodeValue5413 (mixedVector B) := by
  simpa only [nodeValue5413, Sparse.eval_nil] using zero5413 B _hB _hF

theorem sound5414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5414 node5414Labels = Sparse.eval nodeValue5414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5414) = mixedMoment B node5414 node5414Labels := rfl
  simpa [nodeValue5414, Sparse.eval] using hc.symm

theorem sound5415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5415 node5415Labels = Sparse.eval nodeValue5415 (mixedVector B) := by
  have h := singleton5415 B _hB
  rw [sound3820 B _hB _hF, sound3895 B _hB _hF] at h
  norm_num [nodeValue5415, nodeValue3820, nodeValue3895, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5416 node5416Labels = Sparse.eval nodeValue5416 (mixedVector B) := by
  have h := singleton5416 B _hB
  rw [sound3821 B _hB _hF, sound3896 B _hB _hF] at h
  norm_num [nodeValue5416, nodeValue3821, nodeValue3896, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5417 node5417Labels = Sparse.eval nodeValue5417 (mixedVector B) := by
  have h := singleton5417 B _hB
  rw [sound3823 B _hB _hF, sound3897 B _hB _hF] at h
  norm_num [nodeValue5417, nodeValue3823, nodeValue3897, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5418 node5418Labels = Sparse.eval nodeValue5418 (mixedVector B) := by
  have h := singleton5418 B _hB
  rw [sound3824 B _hB _hF, sound3898 B _hB _hF] at h
  norm_num [nodeValue5418, nodeValue3824, nodeValue3898, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5419 node5419Labels = Sparse.eval nodeValue5419 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5419) = mixedMoment B node5419 node5419Labels := rfl
  simpa [nodeValue5419, Sparse.eval] using hc.symm

theorem sound5420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5420 node5420Labels = Sparse.eval nodeValue5420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5420) = mixedMoment B node5420 node5420Labels := rfl
  simpa [nodeValue5420, Sparse.eval] using hc.symm

theorem sound5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5421 node5421Labels = Sparse.eval nodeValue5421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5421) = mixedMoment B node5421 node5421Labels := rfl
  simpa [nodeValue5421, Sparse.eval] using hc.symm

theorem sound5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5422 node5422Labels = Sparse.eval nodeValue5422 (mixedVector B) := by
  have h := singleton5422 B _hB
  rw [sound3900 B _hB _hF, sound3964 B _hB _hF] at h
  norm_num [nodeValue5422, nodeValue3900, nodeValue3964, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5423 node5423Labels = Sparse.eval nodeValue5423 (mixedVector B) := by
  have h := singleton5423 B _hB
  rw [sound3837 B _hB _hF] at h
  norm_num [nodeValue5423, nodeValue3837, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5425 node5425Labels = Sparse.eval nodeValue5425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5425) = mixedMoment B node5425 node5425Labels := rfl
  simpa [nodeValue5425, Sparse.eval] using hc.symm

theorem sound5426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5426 node5426Labels = Sparse.eval nodeValue5426 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5426) = mixedMoment B node5426 node5426Labels := rfl
  simpa [nodeValue5426, Sparse.eval] using hc.symm

theorem sound5427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5427 node5427Labels = Sparse.eval nodeValue5427 (mixedVector B) := by
  simpa only [nodeValue5427, Sparse.eval_nil] using zero5427 B _hB _hF

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5429 node5429Labels = Sparse.eval nodeValue5429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5429) = mixedMoment B node5429 node5429Labels := rfl
  simpa [nodeValue5429, Sparse.eval] using hc.symm

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5432 node5432Labels = Sparse.eval nodeValue5432 (mixedVector B) := by
  have h := singleton5432 B _hB
  rw [sound3850 B _hB _hF] at h
  norm_num [nodeValue5432, nodeValue3850, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5433 node5433Labels = Sparse.eval nodeValue5433 (mixedVector B) := by
  have h := singleton5433 B _hB
  rw [sound3851 B _hB _hF, sound3901 B _hB _hF] at h
  norm_num [nodeValue5433, nodeValue3851, nodeValue3901, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5434 node5434Labels = Sparse.eval nodeValue5434 (mixedVector B) := by
  have h := singleton5434 B _hB
  rw [sound3852 B _hB _hF, sound3903 B _hB _hF] at h
  norm_num [nodeValue5434, nodeValue3852, nodeValue3903, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5435 node5435Labels = Sparse.eval nodeValue5435 (mixedVector B) := by
  have h := singleton5435 B _hB
  rw [sound3853 B _hB _hF, sound3906 B _hB _hF] at h
  norm_num [nodeValue5435, nodeValue3853, nodeValue3906, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5436 node5436Labels = Sparse.eval nodeValue5436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5436) = mixedMoment B node5436 node5436Labels := rfl
  simpa [nodeValue5436, Sparse.eval] using hc.symm

theorem sound5437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5437 node5437Labels = Sparse.eval nodeValue5437 (mixedVector B) := by
  have h := singleton5437 B _hB
  rw [sound3899 B _hB _hF] at h
  norm_num [nodeValue5437, nodeValue3899, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5438 node5438Labels = Sparse.eval nodeValue5438 (mixedVector B) := by
  have h := singleton5438 B _hB
  rw [sound3857 B _hB _hF, sound3876 B _hB _hF] at h
  norm_num [nodeValue5438, nodeValue3857, nodeValue3876, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5439 node5439Labels = Sparse.eval nodeValue5439 (mixedVector B) := by
  have h := singleton5439 B _hB
  rw [sound3858 B _hB _hF, sound3902 B _hB _hF] at h
  norm_num [nodeValue5439, nodeValue3858, nodeValue3902, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
