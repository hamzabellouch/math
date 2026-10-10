import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons79

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5056 node5056Labels = Sparse.eval nodeValue5056 (mixedVector B) := by
  have h := singleton5056 B _hB
  rw [sound2459 B _hB _hF, sound3429 B _hB _hF] at h
  norm_num [nodeValue5056, nodeValue2459, nodeValue3429, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5057 node5057Labels = Sparse.eval nodeValue5057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5057) = mixedMoment B node5057 node5057Labels := rfl
  simpa [nodeValue5057, Sparse.eval] using hc.symm

theorem sound5058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5058 node5058Labels = Sparse.eval nodeValue5058 (mixedVector B) := by
  simpa only [nodeValue5058, Sparse.eval_nil] using zero5058 B _hB _hF

theorem sound5059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5059 node5059Labels = Sparse.eval nodeValue5059 (mixedVector B) := by
  have h := singleton5059 B _hB
  rw [sound2462 B _hB _hF, sound3436 B _hB _hF] at h
  norm_num [nodeValue5059, nodeValue2462, nodeValue3436, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5060 node5060Labels = Sparse.eval nodeValue5060 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5060) = mixedMoment B node5060 node5060Labels := rfl
  simpa [nodeValue5060, Sparse.eval] using hc.symm

theorem sound5061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5061 node5061Labels = Sparse.eval nodeValue5061 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5061) = mixedMoment B node5061 node5061Labels := rfl
  simpa [nodeValue5061, Sparse.eval] using hc.symm

theorem sound5062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5062 node5062Labels = Sparse.eval nodeValue5062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5062) = mixedMoment B node5062 node5062Labels := rfl
  simpa [nodeValue5062, Sparse.eval] using hc.symm

theorem sound5063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5063 node5063Labels = Sparse.eval nodeValue5063 (mixedVector B) := by
  simpa only [nodeValue5063, Sparse.eval_nil] using zero5063 B _hB _hF

theorem sound5064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5064 node5064Labels = Sparse.eval nodeValue5064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5064) = mixedMoment B node5064 node5064Labels := rfl
  simpa [nodeValue5064, Sparse.eval] using hc.symm

theorem sound5065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5065 node5065Labels = Sparse.eval nodeValue5065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5065) = mixedMoment B node5065 node5065Labels := rfl
  simpa [nodeValue5065, Sparse.eval] using hc.symm

theorem sound5066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5066 node5066Labels = Sparse.eval nodeValue5066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5066) = mixedMoment B node5066 node5066Labels := rfl
  simpa [nodeValue5066, Sparse.eval] using hc.symm

theorem sound5067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5067 node5067Labels = Sparse.eval nodeValue5067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5067) = mixedMoment B node5067 node5067Labels := rfl
  simpa [nodeValue5067, Sparse.eval] using hc.symm

theorem sound5068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5068 node5068Labels = Sparse.eval nodeValue5068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5068) = mixedMoment B node5068 node5068Labels := rfl
  simpa [nodeValue5068, Sparse.eval] using hc.symm

theorem sound5069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5069 node5069Labels = Sparse.eval nodeValue5069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5069) = mixedMoment B node5069 node5069Labels := rfl
  simpa [nodeValue5069, Sparse.eval] using hc.symm

theorem sound5070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5070 node5070Labels = Sparse.eval nodeValue5070 (mixedVector B) := by
  have h := singleton5070 B _hB
  rw [sound2477 B _hB _hF, sound3444 B _hB _hF] at h
  norm_num [nodeValue5070, nodeValue2477, nodeValue3444, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5071 node5071Labels = Sparse.eval nodeValue5071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5071) = mixedMoment B node5071 node5071Labels := rfl
  simpa [nodeValue5071, Sparse.eval] using hc.symm

theorem sound5072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5072 node5072Labels = Sparse.eval nodeValue5072 (mixedVector B) := by
  have h := singleton5072 B _hB
  rw [sound2479 B _hB _hF, sound3459 B _hB _hF] at h
  norm_num [nodeValue5072, nodeValue2479, nodeValue3459, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5073 node5073Labels = Sparse.eval nodeValue5073 (mixedVector B) := by
  have h := singleton5073 B _hB
  rw [sound2480 B _hB _hF, sound3467 B _hB _hF] at h
  norm_num [nodeValue5073, nodeValue2480, nodeValue3467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5074 node5074Labels = Sparse.eval nodeValue5074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5074) = mixedMoment B node5074 node5074Labels := rfl
  simpa [nodeValue5074, Sparse.eval] using hc.symm

theorem sound5075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5075 node5075Labels = Sparse.eval nodeValue5075 (mixedVector B) := by
  have h := singleton5075 B _hB
  rw [sound2482 B _hB _hF, sound3468 B _hB _hF] at h
  norm_num [nodeValue5075, nodeValue2482, nodeValue3468, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5076 node5076Labels = Sparse.eval nodeValue5076 (mixedVector B) := by
  have h := singleton5076 B _hB
  rw [sound2483 B _hB _hF, sound3477 B _hB _hF] at h
  norm_num [nodeValue5076, nodeValue2483, nodeValue3477, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5077 node5077Labels = Sparse.eval nodeValue5077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5077) = mixedMoment B node5077 node5077Labels := rfl
  simpa [nodeValue5077, Sparse.eval] using hc.symm

theorem sound5078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5078 node5078Labels = Sparse.eval nodeValue5078 (mixedVector B) := by
  have h := singleton5078 B _hB
  rw [sound2485 B _hB _hF, sound3481 B _hB _hF] at h
  norm_num [nodeValue5078, nodeValue2485, nodeValue3481, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5079 node5079Labels = Sparse.eval nodeValue5079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5079) = mixedMoment B node5079 node5079Labels := rfl
  simpa [nodeValue5079, Sparse.eval] using hc.symm

theorem sound5080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5080 node5080Labels = Sparse.eval nodeValue5080 (mixedVector B) := by
  have h := singleton5080 B _hB
  rw [sound2488 B _hB _hF, sound3478 B _hB _hF] at h
  norm_num [nodeValue5080, nodeValue2488, nodeValue3478, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5081 node5081Labels = Sparse.eval nodeValue5081 (mixedVector B) := by
  have h := singleton5081 B _hB
  rw [sound2489 B _hB _hF, sound3482 B _hB _hF] at h
  norm_num [nodeValue5081, nodeValue2489, nodeValue3482, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5082 node5082Labels = Sparse.eval nodeValue5082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5082) = mixedMoment B node5082 node5082Labels := rfl
  simpa [nodeValue5082, Sparse.eval] using hc.symm

theorem sound5083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5083 node5083Labels = Sparse.eval nodeValue5083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5083) = mixedMoment B node5083 node5083Labels := rfl
  simpa [nodeValue5083, Sparse.eval] using hc.symm

theorem sound5084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5084 node5084Labels = Sparse.eval nodeValue5084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5084) = mixedMoment B node5084 node5084Labels := rfl
  simpa [nodeValue5084, Sparse.eval] using hc.symm

theorem sound5085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5085 node5085Labels = Sparse.eval nodeValue5085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5085) = mixedMoment B node5085 node5085Labels := rfl
  simpa [nodeValue5085, Sparse.eval] using hc.symm

theorem sound5086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5086 node5086Labels = Sparse.eval nodeValue5086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5086) = mixedMoment B node5086 node5086Labels := rfl
  simpa [nodeValue5086, Sparse.eval] using hc.symm

theorem sound5087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5087 node5087Labels = Sparse.eval nodeValue5087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5087) = mixedMoment B node5087 node5087Labels := rfl
  simpa [nodeValue5087, Sparse.eval] using hc.symm

theorem sound5088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5088 node5088Labels = Sparse.eval nodeValue5088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5088) = mixedMoment B node5088 node5088Labels := rfl
  simpa [nodeValue5088, Sparse.eval] using hc.symm

theorem sound5089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5089 node5089Labels = Sparse.eval nodeValue5089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5089) = mixedMoment B node5089 node5089Labels := rfl
  simpa [nodeValue5089, Sparse.eval] using hc.symm

theorem sound5090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5090 node5090Labels = Sparse.eval nodeValue5090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5090) = mixedMoment B node5090 node5090Labels := rfl
  simpa [nodeValue5090, Sparse.eval] using hc.symm

theorem sound5091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5091 node5091Labels = Sparse.eval nodeValue5091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5091) = mixedMoment B node5091 node5091Labels := rfl
  simpa [nodeValue5091, Sparse.eval] using hc.symm

theorem sound5092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5092 node5092Labels = Sparse.eval nodeValue5092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5092) = mixedMoment B node5092 node5092Labels := rfl
  simpa [nodeValue5092, Sparse.eval] using hc.symm

theorem sound5093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5093 node5093Labels = Sparse.eval nodeValue5093 (mixedVector B) := by
  have h := singleton5093 B _hB
  rw [sound2503 B _hB _hF, sound3446 B _hB _hF] at h
  norm_num [nodeValue5093, nodeValue2503, nodeValue3446, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5094 node5094Labels = Sparse.eval nodeValue5094 (mixedVector B) := by
  have h := singleton5094 B _hB
  rw [sound2504 B _hB _hF] at h
  norm_num [nodeValue5094, nodeValue2504, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5095 node5095Labels = Sparse.eval nodeValue5095 (mixedVector B) := by
  have h := singleton5095 B _hB
  rw [sound2505 B _hB _hF, sound3448 B _hB _hF] at h
  norm_num [nodeValue5095, nodeValue2505, nodeValue3448, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5096 node5096Labels = Sparse.eval nodeValue5096 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5096) = mixedMoment B node5096 node5096Labels := rfl
  simpa [nodeValue5096, Sparse.eval] using hc.symm

theorem sound5097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5097 node5097Labels = Sparse.eval nodeValue5097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5097) = mixedMoment B node5097 node5097Labels := rfl
  simpa [nodeValue5097, Sparse.eval] using hc.symm

theorem sound5098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5098 node5098Labels = Sparse.eval nodeValue5098 (mixedVector B) := by
  have h := singleton5098 B _hB
  rw [sound2508 B _hB _hF, sound3460 B _hB _hF] at h
  norm_num [nodeValue5098, nodeValue2508, nodeValue3460, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5099 node5099Labels = Sparse.eval nodeValue5099 (mixedVector B) := by
  have h := singleton5099 B _hB
  rw [sound2509 B _hB _hF, sound2704 B _hB _hF] at h
  norm_num [nodeValue5099, nodeValue2509, nodeValue2704, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5100 node5100Labels = Sparse.eval nodeValue5100 (mixedVector B) := by
  simpa only [nodeValue5100, Sparse.eval_nil] using zero5100 B _hB _hF

theorem sound5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = Sparse.eval nodeValue5101 (mixedVector B) := by
  simpa only [nodeValue5101, Sparse.eval_nil] using zero5101 B _hB _hF

theorem sound5102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5102 node5102Labels = Sparse.eval nodeValue5102 (mixedVector B) := by
  have h := singleton5102 B _hB
  rw [sound2512 B _hB _hF, sound3471 B _hB _hF] at h
  norm_num [nodeValue5102, nodeValue2512, nodeValue3471, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5103 node5103Labels = Sparse.eval nodeValue5103 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5103) = mixedMoment B node5103 node5103Labels := rfl
  simpa [nodeValue5103, Sparse.eval] using hc.symm

theorem sound5104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = Sparse.eval nodeValue5104 (mixedVector B) := by
  simpa only [nodeValue5104, Sparse.eval_nil] using zero5104 B _hB _hF

theorem sound5105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5105 node5105Labels = Sparse.eval nodeValue5105 (mixedVector B) := by
  have h := singleton5105 B _hB
  rw [sound2515 B _hB _hF, sound3479 B _hB _hF] at h
  norm_num [nodeValue5105, nodeValue2515, nodeValue3479, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5106 node5106Labels = Sparse.eval nodeValue5106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5106) = mixedMoment B node5106 node5106Labels := rfl
  simpa [nodeValue5106, Sparse.eval] using hc.symm

theorem sound5107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5107 node5107Labels = Sparse.eval nodeValue5107 (mixedVector B) := by
  simpa only [nodeValue5107, Sparse.eval_nil] using zero5107 B _hB _hF

theorem sound5108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5108 node5108Labels = Sparse.eval nodeValue5108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5108) = mixedMoment B node5108 node5108Labels := rfl
  simpa [nodeValue5108, Sparse.eval] using hc.symm

theorem sound5109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5109 node5109Labels = Sparse.eval nodeValue5109 (mixedVector B) := by
  have h := singleton5109 B _hB
  rw [sound2519 B _hB _hF, sound3486 B _hB _hF] at h
  norm_num [nodeValue5109, nodeValue2519, nodeValue3486, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5110 node5110Labels = Sparse.eval nodeValue5110 (mixedVector B) := by
  have h := singleton5110 B _hB
  rw [sound2522 B _hB _hF, sound2685 B _hB _hF] at h
  norm_num [nodeValue5110, nodeValue2522, nodeValue2685, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = Sparse.eval nodeValue5111 (mixedVector B) := by
  simpa only [nodeValue5111, Sparse.eval_nil] using zero5111 B _hB _hF

theorem sound5112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5112 node5112Labels = Sparse.eval nodeValue5112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5112) = mixedMoment B node5112 node5112Labels := rfl
  simpa [nodeValue5112, Sparse.eval] using hc.symm

theorem sound5113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5113 node5113Labels = Sparse.eval nodeValue5113 (mixedVector B) := by
  simpa only [nodeValue5113, Sparse.eval_nil] using zero5113 B _hB _hF

theorem sound5114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5114 node5114Labels = Sparse.eval nodeValue5114 (mixedVector B) := by
  have h := singleton5114 B _hB
  rw [sound2896 B _hB _hF, sound3597 B _hB _hF] at h
  norm_num [nodeValue5114, nodeValue2896, nodeValue3597, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5115 node5115Labels = Sparse.eval nodeValue5115 (mixedVector B) := by
  simpa only [nodeValue5115, Sparse.eval_nil] using zero5115 B _hB _hF

theorem sound5116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5116 node5116Labels = Sparse.eval nodeValue5116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5116) = mixedMoment B node5116 node5116Labels := rfl
  simpa [nodeValue5116, Sparse.eval] using hc.symm

theorem sound5117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5117 node5117Labels = Sparse.eval nodeValue5117 (mixedVector B) := by
  have h := singleton5117 B _hB
  rw [sound2893 B _hB _hF, sound3599 B _hB _hF] at h
  norm_num [nodeValue5117, nodeValue2893, nodeValue3599, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5118 node5118Labels = Sparse.eval nodeValue5118 (mixedVector B) := by
  have h := singleton5118 B _hB
  rw [sound2891 B _hB _hF, sound3598 B _hB _hF] at h
  norm_num [nodeValue5118, nodeValue2891, nodeValue3598, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5119 node5119Labels = Sparse.eval nodeValue5119 (mixedVector B) := by
  have h := singleton5119 B _hB
  rw [sound2845 B _hB _hF, sound3604 B _hB _hF] at h
  norm_num [nodeValue5119, nodeValue2845, nodeValue3604, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
