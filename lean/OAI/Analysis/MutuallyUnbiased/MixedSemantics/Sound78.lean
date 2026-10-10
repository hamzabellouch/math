import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons78

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4992 node4992Labels = Sparse.eval nodeValue4992 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4992) = mixedMoment B node4992 node4992Labels := rfl
  simpa [nodeValue4992, Sparse.eval] using hc.symm

theorem sound4993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4993 node4993Labels = Sparse.eval nodeValue4993 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4993) = mixedMoment B node4993 node4993Labels := rfl
  simpa [nodeValue4993, Sparse.eval] using hc.symm

theorem sound4994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4994 node4994Labels = Sparse.eval nodeValue4994 (mixedVector B) := by
  simpa only [nodeValue4994, Sparse.eval_nil] using zero4994 B _hB _hF

theorem sound4995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4995 node4995Labels = Sparse.eval nodeValue4995 (mixedVector B) := by
  simpa only [nodeValue4995, Sparse.eval_nil] using zero4995 B _hB _hF

theorem sound4996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4996 node4996Labels = Sparse.eval nodeValue4996 (mixedVector B) := by
  have h := singleton4996 B _hB
  rw [sound2382 B _hB _hF, sound3340 B _hB _hF] at h
  norm_num [nodeValue4996, nodeValue2382, nodeValue3340, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4997 node4997Labels = Sparse.eval nodeValue4997 (mixedVector B) := by
  simpa only [nodeValue4997, Sparse.eval_nil] using zero4997 B _hB _hF

theorem sound4998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4998 node4998Labels = Sparse.eval nodeValue4998 (mixedVector B) := by
  have h := singleton4998 B _hB
  rw [sound2383 B _hB _hF, sound3352 B _hB _hF] at h
  norm_num [nodeValue4998, nodeValue2383, nodeValue3352, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4999 node4999Labels = Sparse.eval nodeValue4999 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4999) = mixedMoment B node4999 node4999Labels := rfl
  simpa [nodeValue4999, Sparse.eval] using hc.symm

theorem sound5000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5000 node5000Labels = Sparse.eval nodeValue5000 (mixedVector B) := by
  have h := singleton5000 B _hB
  rw [sound2385 B _hB _hF, sound3353 B _hB _hF] at h
  norm_num [nodeValue5000, nodeValue2385, nodeValue3353, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5001 node5001Labels = Sparse.eval nodeValue5001 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5001) = mixedMoment B node5001 node5001Labels := rfl
  simpa [nodeValue5001, Sparse.eval] using hc.symm

theorem sound5002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5002 node5002Labels = Sparse.eval nodeValue5002 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5002) = mixedMoment B node5002 node5002Labels := rfl
  simpa [nodeValue5002, Sparse.eval] using hc.symm

theorem sound5003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5003 node5003Labels = Sparse.eval nodeValue5003 (mixedVector B) := by
  have h := singleton5003 B _hB
  rw [sound2388 B _hB _hF, sound3354 B _hB _hF] at h
  norm_num [nodeValue5003, nodeValue2388, nodeValue3354, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5004 node5004Labels = Sparse.eval nodeValue5004 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5004) = mixedMoment B node5004 node5004Labels := rfl
  simpa [nodeValue5004, Sparse.eval] using hc.symm

theorem sound5005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5005 node5005Labels = Sparse.eval nodeValue5005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5005) = mixedMoment B node5005 node5005Labels := rfl
  simpa [nodeValue5005, Sparse.eval] using hc.symm

theorem sound5006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5006 node5006Labels = Sparse.eval nodeValue5006 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5006) = mixedMoment B node5006 node5006Labels := rfl
  simpa [nodeValue5006, Sparse.eval] using hc.symm

theorem sound5007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5007 node5007Labels = Sparse.eval nodeValue5007 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5007) = mixedMoment B node5007 node5007Labels := rfl
  simpa [nodeValue5007, Sparse.eval] using hc.symm

theorem sound5008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5008 node5008Labels = Sparse.eval nodeValue5008 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5008) = mixedMoment B node5008 node5008Labels := rfl
  simpa [nodeValue5008, Sparse.eval] using hc.symm

theorem sound5009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5009 node5009Labels = Sparse.eval nodeValue5009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5009) = mixedMoment B node5009 node5009Labels := rfl
  simpa [nodeValue5009, Sparse.eval] using hc.symm

theorem sound5010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5010 node5010Labels = Sparse.eval nodeValue5010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5010) = mixedMoment B node5010 node5010Labels := rfl
  simpa [nodeValue5010, Sparse.eval] using hc.symm

theorem sound5011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5011 node5011Labels = Sparse.eval nodeValue5011 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5011) = mixedMoment B node5011 node5011Labels := rfl
  simpa [nodeValue5011, Sparse.eval] using hc.symm

theorem sound5012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5012 node5012Labels = Sparse.eval nodeValue5012 (mixedVector B) := by
  simpa only [nodeValue5012, Sparse.eval_nil] using zero5012 B _hB _hF

theorem sound5013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5013 node5013Labels = Sparse.eval nodeValue5013 (mixedVector B) := by
  have h := singleton5013 B _hB
  rw [sound2398 B _hB _hF, sound3341 B _hB _hF] at h
  norm_num [nodeValue5013, nodeValue2398, nodeValue3341, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5014 node5014Labels = Sparse.eval nodeValue5014 (mixedVector B) := by
  have h := singleton5014 B _hB
  rw [sound2399 B _hB _hF, sound2467 B _hB _hF] at h
  norm_num [nodeValue5014, nodeValue2399, nodeValue2467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5015 node5015Labels = Sparse.eval nodeValue5015 (mixedVector B) := by
  have h := singleton5015 B _hB
  rw [sound2400 B _hB _hF, sound3344 B _hB _hF] at h
  norm_num [nodeValue5015, nodeValue2400, nodeValue3344, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5016 node5016Labels = Sparse.eval nodeValue5016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5016) = mixedMoment B node5016 node5016Labels := rfl
  simpa [nodeValue5016, Sparse.eval] using hc.symm

theorem sound5017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5017 node5017Labels = Sparse.eval nodeValue5017 (mixedVector B) := by
  simpa only [nodeValue5017, Sparse.eval_nil] using zero5017 B _hB _hF

theorem sound5018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5018 node5018Labels = Sparse.eval nodeValue5018 (mixedVector B) := by
  have h := singleton5018 B _hB
  rw [sound2404 B _hB _hF, sound3357 B _hB _hF] at h
  norm_num [nodeValue5018, nodeValue2404, nodeValue3357, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5019 node5019Labels = Sparse.eval nodeValue5019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5019) = mixedMoment B node5019 node5019Labels := rfl
  simpa [nodeValue5019, Sparse.eval] using hc.symm

theorem sound5020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5020 node5020Labels = Sparse.eval nodeValue5020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5020) = mixedMoment B node5020 node5020Labels := rfl
  simpa [nodeValue5020, Sparse.eval] using hc.symm

theorem sound5021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5021 node5021Labels = Sparse.eval nodeValue5021 (mixedVector B) := by
  have h := singleton5021 B _hB
  rw [sound2407 B _hB _hF, sound3360 B _hB _hF] at h
  norm_num [nodeValue5021, nodeValue2407, nodeValue3360, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5022 node5022Labels = Sparse.eval nodeValue5022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5022) = mixedMoment B node5022 node5022Labels := rfl
  simpa [nodeValue5022, Sparse.eval] using hc.symm

theorem sound5023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5023 node5023Labels = Sparse.eval nodeValue5023 (mixedVector B) := by
  have h := singleton5023 B _hB
  rw [sound2410 B _hB _hF] at h
  norm_num [nodeValue5023, nodeValue2410, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5024 node5024Labels = Sparse.eval nodeValue5024 (mixedVector B) := by
  simpa only [nodeValue5024, Sparse.eval_nil] using zero5024 B _hB _hF

theorem sound5025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5025 node5025Labels = Sparse.eval nodeValue5025 (mixedVector B) := by
  simpa only [nodeValue5025, Sparse.eval_nil] using zero5025 B _hB _hF

theorem sound5026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5026 node5026Labels = Sparse.eval nodeValue5026 (mixedVector B) := by
  simpa only [nodeValue5026, Sparse.eval_nil] using zero5026 B _hB _hF

theorem sound5027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5027 node5027Labels = Sparse.eval nodeValue5027 (mixedVector B) := by
  have h := singleton5027 B _hB
  rw [sound2416 B _hB _hF, sound3427 B _hB _hF] at h
  norm_num [nodeValue5027, nodeValue2416, nodeValue3427, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5028 node5028Labels = Sparse.eval nodeValue5028 (mixedVector B) := by
  have h := singleton5028 B _hB
  rw [sound2417 B _hB _hF, sound2445 B _hB _hF] at h
  norm_num [nodeValue5028, nodeValue2417, nodeValue2445, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5029 node5029Labels = Sparse.eval nodeValue5029 (mixedVector B) := by
  simpa only [nodeValue5029, Sparse.eval_nil] using zero5029 B _hB _hF

theorem sound5030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5030 node5030Labels = Sparse.eval nodeValue5030 (mixedVector B) := by
  have h := singleton5030 B _hB
  rw [sound2419 B _hB _hF, sound3425 B _hB _hF] at h
  norm_num [nodeValue5030, nodeValue2419, nodeValue3425, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5031 node5031Labels = Sparse.eval nodeValue5031 (mixedVector B) := by
  have h := singleton5031 B _hB
  rw [sound2420 B _hB _hF, sound3428 B _hB _hF] at h
  norm_num [nodeValue5031, nodeValue2420, nodeValue3428, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5032 node5032Labels = Sparse.eval nodeValue5032 (mixedVector B) := by
  have h := singleton5032 B _hB
  rw [sound2424 B _hB _hF, sound3440 B _hB _hF] at h
  norm_num [nodeValue5032, nodeValue2424, nodeValue3440, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5033 node5033Labels = Sparse.eval nodeValue5033 (mixedVector B) := by
  have h := singleton5033 B _hB
  rw [sound2425 B _hB _hF, sound3449 B _hB _hF] at h
  norm_num [nodeValue5033, nodeValue2425, nodeValue3449, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5034 node5034Labels = Sparse.eval nodeValue5034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5034) = mixedMoment B node5034 node5034Labels := rfl
  simpa [nodeValue5034, Sparse.eval] using hc.symm

theorem sound5035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5035 node5035Labels = Sparse.eval nodeValue5035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5035) = mixedMoment B node5035 node5035Labels := rfl
  simpa [nodeValue5035, Sparse.eval] using hc.symm

theorem sound5036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5036 node5036Labels = Sparse.eval nodeValue5036 (mixedVector B) := by
  have h := singleton5036 B _hB
  rw [sound2428 B _hB _hF, sound3450 B _hB _hF] at h
  norm_num [nodeValue5036, nodeValue2428, nodeValue3450, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5037 node5037Labels = Sparse.eval nodeValue5037 (mixedVector B) := by
  have h := singleton5037 B _hB
  rw [sound2429 B _hB _hF, sound3455 B _hB _hF] at h
  norm_num [nodeValue5037, nodeValue2429, nodeValue3455, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5038 node5038Labels = Sparse.eval nodeValue5038 (mixedVector B) := by
  have h := singleton5038 B _hB
  rw [sound2431 B _hB _hF, sound3453 B _hB _hF] at h
  norm_num [nodeValue5038, nodeValue2431, nodeValue3453, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5039 node5039Labels = Sparse.eval nodeValue5039 (mixedVector B) := by
  have h := singleton5039 B _hB
  rw [sound2432 B _hB _hF, sound3456 B _hB _hF] at h
  norm_num [nodeValue5039, nodeValue2432, nodeValue3456, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5040 node5040Labels = Sparse.eval nodeValue5040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5040) = mixedMoment B node5040 node5040Labels := rfl
  simpa [nodeValue5040, Sparse.eval] using hc.symm

theorem sound5041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5041 node5041Labels = Sparse.eval nodeValue5041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5041) = mixedMoment B node5041 node5041Labels := rfl
  simpa [nodeValue5041, Sparse.eval] using hc.symm

theorem sound5042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5042 node5042Labels = Sparse.eval nodeValue5042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5042) = mixedMoment B node5042 node5042Labels := rfl
  simpa [nodeValue5042, Sparse.eval] using hc.symm

theorem sound5043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5043 node5043Labels = Sparse.eval nodeValue5043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5043) = mixedMoment B node5043 node5043Labels := rfl
  simpa [nodeValue5043, Sparse.eval] using hc.symm

theorem sound5044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5044 node5044Labels = Sparse.eval nodeValue5044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5044) = mixedMoment B node5044 node5044Labels := rfl
  simpa [nodeValue5044, Sparse.eval] using hc.symm

theorem sound5045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5045 node5045Labels = Sparse.eval nodeValue5045 (mixedVector B) := by
  have h := singleton5045 B _hB
  rw [sound2444 B _hB _hF, sound3362 B _hB _hF] at h
  norm_num [nodeValue5045, nodeValue2444, nodeValue3362, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5046 node5046Labels = Sparse.eval nodeValue5046 (mixedVector B) := by
  have h := singleton5046 B _hB
  rw [sound2446 B _hB _hF, sound3363 B _hB _hF] at h
  norm_num [nodeValue5046, nodeValue2446, nodeValue3363, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5047 node5047Labels = Sparse.eval nodeValue5047 (mixedVector B) := by
  have h := singleton5047 B _hB
  rw [sound2449 B _hB _hF, sound3432 B _hB _hF] at h
  norm_num [nodeValue5047, nodeValue2449, nodeValue3432, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5048 node5048Labels = Sparse.eval nodeValue5048 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5048) = mixedMoment B node5048 node5048Labels := rfl
  simpa [nodeValue5048, Sparse.eval] using hc.symm

theorem sound5049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5049 node5049Labels = Sparse.eval nodeValue5049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5049) = mixedMoment B node5049 node5049Labels := rfl
  simpa [nodeValue5049, Sparse.eval] using hc.symm

theorem sound5050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5050 node5050Labels = Sparse.eval nodeValue5050 (mixedVector B) := by
  have h := singleton5050 B _hB
  rw [sound2452 B _hB _hF, sound3433 B _hB _hF] at h
  norm_num [nodeValue5050, nodeValue2452, nodeValue3433, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5051 node5051Labels = Sparse.eval nodeValue5051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5051) = mixedMoment B node5051 node5051Labels := rfl
  simpa [nodeValue5051, Sparse.eval] using hc.symm

theorem sound5052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5052 node5052Labels = Sparse.eval nodeValue5052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5052) = mixedMoment B node5052 node5052Labels := rfl
  simpa [nodeValue5052, Sparse.eval] using hc.symm

theorem sound5053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5053 node5053Labels = Sparse.eval nodeValue5053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5053) = mixedMoment B node5053 node5053Labels := rfl
  simpa [nodeValue5053, Sparse.eval] using hc.symm

theorem sound5054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5054 node5054Labels = Sparse.eval nodeValue5054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5054) = mixedMoment B node5054 node5054Labels := rfl
  simpa [nodeValue5054, Sparse.eval] using hc.symm

theorem sound5055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5055 node5055Labels = Sparse.eval nodeValue5055 (mixedVector B) := by
  have h := singleton5055 B _hB
  rw [sound2458 B _hB _hF] at h
  norm_num [nodeValue5055, nodeValue2458, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
