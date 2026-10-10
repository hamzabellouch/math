import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = Sparse.eval nodeValue5440 (mixedVector B) := by
  simpa only [nodeValue5440, Sparse.eval_nil] using zero5440 B _hB _hF

theorem sound5441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5441 node5441Labels = Sparse.eval nodeValue5441 (mixedVector B) := by
  simpa only [nodeValue5441, Sparse.eval_nil] using zero5441 B _hB _hF

theorem sound5442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5442 node5442Labels = Sparse.eval nodeValue5442 (mixedVector B) := by
  simpa only [nodeValue5442, Sparse.eval_nil] using zero5442 B _hB _hF

theorem sound5444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5444 node5444Labels = Sparse.eval nodeValue5444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5444) = mixedMoment B node5444 node5444Labels := rfl
  simpa [nodeValue5444, Sparse.eval] using hc.symm

theorem sound5445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5445 node5445Labels = Sparse.eval nodeValue5445 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5445) = mixedMoment B node5445 node5445Labels := rfl
  simpa [nodeValue5445, Sparse.eval] using hc.symm

theorem sound5446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5446 node5446Labels = Sparse.eval nodeValue5446 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5446) = mixedMoment B node5446 node5446Labels := rfl
  simpa [nodeValue5446, Sparse.eval] using hc.symm

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5448 node5448Labels = Sparse.eval nodeValue5448 (mixedVector B) := by
  have h := singleton5448 B _hB
  rw [sound3885 B _hB _hF] at h
  norm_num [nodeValue5448, nodeValue3885, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5449 node5449Labels = Sparse.eval nodeValue5449 (mixedVector B) := by
  have h := singleton5449 B _hB
  rw [sound3886 B _hB _hF] at h
  norm_num [nodeValue5449, nodeValue3886, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5450 node5450Labels = Sparse.eval nodeValue5450 (mixedVector B) := by
  have h := singleton5450 B _hB
  rw [sound3887 B _hB _hF, sound3910 B _hB _hF] at h
  norm_num [nodeValue5450, nodeValue3887, nodeValue3910, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5451 node5451Labels = Sparse.eval nodeValue5451 (mixedVector B) := by
  have h := singleton5451 B _hB
  rw [sound3888 B _hB _hF, sound3913 B _hB _hF] at h
  norm_num [nodeValue5451, nodeValue3888, nodeValue3913, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5452 node5452Labels = Sparse.eval nodeValue5452 (mixedVector B) := by
  have h := singleton5452 B _hB
  rw [sound3911 B _hB _hF, sound4039 B _hB _hF] at h
  norm_num [nodeValue5452, nodeValue3911, nodeValue4039, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5454 node5454Labels = Sparse.eval nodeValue5454 (mixedVector B) := by
  simpa only [nodeValue5454, Sparse.eval_nil] using zero5454 B _hB _hF

theorem sound5456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5456 node5456Labels = Sparse.eval nodeValue5456 (mixedVector B) := by
  have h := singleton5456 B _hB
  rw [sound3916 B _hB _hF] at h
  norm_num [nodeValue5456, nodeValue3916, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5457 node5457Labels = Sparse.eval nodeValue5457 (mixedVector B) := by
  simpa only [nodeValue5457, Sparse.eval_nil] using zero5457 B _hB _hF

theorem sound5458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5458 node5458Labels = Sparse.eval nodeValue5458 (mixedVector B) := by
  simpa only [nodeValue5458, Sparse.eval_nil] using zero5458 B _hB _hF

theorem sound5459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5459 node5459Labels = Sparse.eval nodeValue5459 (mixedVector B) := by
  simpa only [nodeValue5459, Sparse.eval_nil] using zero5459 B _hB _hF

theorem sound5460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5460 node5460Labels = Sparse.eval nodeValue5460 (mixedVector B) := by
  simpa only [nodeValue5460, Sparse.eval_nil] using zero5460 B _hB _hF

theorem sound5461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5461 node5461Labels = Sparse.eval nodeValue5461 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5461) = mixedMoment B node5461 node5461Labels := rfl
  simpa [nodeValue5461, Sparse.eval] using hc.symm

theorem sound5462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5462 node5462Labels = Sparse.eval nodeValue5462 (mixedVector B) := by
  simpa only [nodeValue5462, Sparse.eval_nil] using zero5462 B _hB _hF

theorem sound5463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5463 node5463Labels = Sparse.eval nodeValue5463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5463) = mixedMoment B node5463 node5463Labels := rfl
  simpa [nodeValue5463, Sparse.eval] using hc.symm

theorem sound5464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5464 node5464Labels = Sparse.eval nodeValue5464 (mixedVector B) := by
  have h := singleton5464 B _hB
  rw [sound3930 B _hB _hF, sound4041 B _hB _hF] at h
  norm_num [nodeValue5464, nodeValue3930, nodeValue4041, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5465 node5465Labels = Sparse.eval nodeValue5465 (mixedVector B) := by
  have h := singleton5465 B _hB
  rw [sound3931 B _hB _hF, sound4042 B _hB _hF] at h
  norm_num [nodeValue5465, nodeValue3931, nodeValue4042, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5466 node5466Labels = Sparse.eval nodeValue5466 (mixedVector B) := by
  have h := singleton5466 B _hB
  rw [sound3934 B _hB _hF, sound4043 B _hB _hF] at h
  norm_num [nodeValue5466, nodeValue3934, nodeValue4043, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5467 node5467Labels = Sparse.eval nodeValue5467 (mixedVector B) := by
  have h := singleton5467 B _hB
  rw [sound3942 B _hB _hF] at h
  norm_num [nodeValue5467, nodeValue3942, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5468 node5468Labels = Sparse.eval nodeValue5468 (mixedVector B) := by
  simpa only [nodeValue5468, Sparse.eval_nil] using zero5468 B _hB _hF

theorem sound5469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5469 node5469Labels = Sparse.eval nodeValue5469 (mixedVector B) := by
  have h := singleton5469 B _hB
  rw [sound3945 B _hB _hF, sound3952 B _hB _hF] at h
  norm_num [nodeValue5469, nodeValue3945, nodeValue3952, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5470 node5470Labels = Sparse.eval nodeValue5470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5470) = mixedMoment B node5470 node5470Labels := rfl
  simpa [nodeValue5470, Sparse.eval] using hc.symm

theorem sound5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5471 node5471Labels = Sparse.eval nodeValue5471 (mixedVector B) := by
  simpa only [nodeValue5471, Sparse.eval_nil] using zero5471 B _hB _hF

theorem sound5472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5472 node5472Labels = Sparse.eval nodeValue5472 (mixedVector B) := by
  have h := singleton5472 B _hB
  rw [sound3957 B _hB _hF] at h
  norm_num [nodeValue5472, nodeValue3957, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5474 node5474Labels = Sparse.eval nodeValue5474 (mixedVector B) := by
  simpa only [nodeValue5474, Sparse.eval_nil] using zero5474 B _hB _hF

theorem sound5475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5475 node5475Labels = Sparse.eval nodeValue5475 (mixedVector B) := by
  have h := singleton5475 B _hB
  rw [sound3963 B _hB _hF] at h
  norm_num [nodeValue5475, nodeValue3963, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5476 node5476Labels = Sparse.eval nodeValue5476 (mixedVector B) := by
  have h := singleton5476 B _hB
  rw [sound3965 B _hB _hF, sound4045 B _hB _hF] at h
  norm_num [nodeValue5476, nodeValue3965, nodeValue4045, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = Sparse.eval nodeValue5477 (mixedVector B) := by
  simpa only [nodeValue5477, Sparse.eval_nil] using zero5477 B _hB _hF

theorem sound5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5478 node5478Labels = Sparse.eval nodeValue5478 (mixedVector B) := by
  have h := singleton5478 B _hB
  rw [sound3974 B _hB _hF] at h
  norm_num [nodeValue5478, nodeValue3974, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5479 node5479Labels = Sparse.eval nodeValue5479 (mixedVector B) := by
  simpa only [nodeValue5479, Sparse.eval_nil] using zero5479 B _hB _hF

theorem sound5480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5480 node5480Labels = Sparse.eval nodeValue5480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5480) = mixedMoment B node5480 node5480Labels := rfl
  simpa [nodeValue5480, Sparse.eval] using hc.symm

theorem sound5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = Sparse.eval nodeValue5481 (mixedVector B) := by
  simpa only [nodeValue5481, Sparse.eval_nil] using zero5481 B _hB _hF

theorem sound5482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5482 node5482Labels = Sparse.eval nodeValue5482 (mixedVector B) := by
  have h := singleton5482 B _hB
  rw [sound3980 B _hB _hF, sound4046 B _hB _hF] at h
  norm_num [nodeValue5482, nodeValue3980, nodeValue4046, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5483 node5483Labels = Sparse.eval nodeValue5483 (mixedVector B) := by
  have h := singleton5483 B _hB
  rw [sound3981 B _hB _hF, sound4047 B _hB _hF] at h
  norm_num [nodeValue5483, nodeValue3981, nodeValue4047, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5484 node5484Labels = Sparse.eval nodeValue5484 (mixedVector B) := by
  have h := singleton5484 B _hB
  rw [sound3983 B _hB _hF] at h
  norm_num [nodeValue5484, nodeValue3983, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5485 node5485Labels = Sparse.eval nodeValue5485 (mixedVector B) := by
  have h := singleton5485 B _hB
  rw [sound3984 B _hB _hF, sound4010 B _hB _hF] at h
  norm_num [nodeValue5485, nodeValue3984, nodeValue4010, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = Sparse.eval nodeValue5486 (mixedVector B) := by
  simpa only [nodeValue5486, Sparse.eval_nil] using zero5486 B _hB _hF

theorem sound5487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5487 node5487Labels = Sparse.eval nodeValue5487 (mixedVector B) := by
  simpa only [nodeValue5487, Sparse.eval_nil] using zero5487 B _hB _hF

theorem sound5488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5488 node5488Labels = Sparse.eval nodeValue5488 (mixedVector B) := by
  simpa only [nodeValue5488, Sparse.eval_nil] using zero5488 B _hB _hF

theorem sound5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = Sparse.eval nodeValue5489 (mixedVector B) := by
  simpa only [nodeValue5489, Sparse.eval_nil] using zero5489 B _hB _hF

theorem sound5490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5490 node5490Labels = Sparse.eval nodeValue5490 (mixedVector B) := by
  have h := singleton5490 B _hB
  rw [sound4013 B _hB _hF] at h
  norm_num [nodeValue5490, nodeValue4013, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5491 node5491Labels = Sparse.eval nodeValue5491 (mixedVector B) := by
  have h := singleton5491 B _hB
  rw [sound4014 B _hB _hF] at h
  norm_num [nodeValue5491, nodeValue4014, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5492 node5492Labels = Sparse.eval nodeValue5492 (mixedVector B) := by
  have h := singleton5492 B _hB
  rw [sound4015 B _hB _hF, sound4017 B _hB _hF] at h
  norm_num [nodeValue5492, nodeValue4015, nodeValue4017, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5493 node5493Labels = Sparse.eval nodeValue5493 (mixedVector B) := by
  simpa only [nodeValue5493, Sparse.eval_nil] using zero5493 B _hB _hF

theorem sound5494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5494 node5494Labels = Sparse.eval nodeValue5494 (mixedVector B) := by
  have h := singleton5494 B _hB
  rw [sound4020 B _hB _hF] at h
  norm_num [nodeValue5494, nodeValue4020, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5495 node5495Labels = Sparse.eval nodeValue5495 (mixedVector B) := by
  simpa only [nodeValue5495, Sparse.eval_nil] using zero5495 B _hB _hF

theorem sound5496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5496 node5496Labels = Sparse.eval nodeValue5496 (mixedVector B) := by
  simpa only [nodeValue5496, Sparse.eval_nil] using zero5496 B _hB _hF

theorem sound5497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5497 node5497Labels = Sparse.eval nodeValue5497 (mixedVector B) := by
  simpa only [nodeValue5497, Sparse.eval_nil] using zero5497 B _hB _hF

theorem sound5498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5498 node5498Labels = Sparse.eval nodeValue5498 (mixedVector B) := by
  have h := singleton5498 B _hB
  rw [sound4051 B _hB _hF] at h
  norm_num [nodeValue5498, nodeValue4051, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5499 node5499Labels = Sparse.eval nodeValue5499 (mixedVector B) := by
  simpa only [nodeValue5499, Sparse.eval_nil] using zero5499 B _hB _hF

theorem sound5500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5500 node5500Labels = Sparse.eval nodeValue5500 (mixedVector B) := by
  have h := singleton5500 B _hB
  rw [sound4053 B _hB _hF] at h
  norm_num [nodeValue5500, nodeValue4053, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5501 node5501Labels = Sparse.eval nodeValue5501 (mixedVector B) := by
  simpa only [nodeValue5501, Sparse.eval_nil] using zero5501 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
