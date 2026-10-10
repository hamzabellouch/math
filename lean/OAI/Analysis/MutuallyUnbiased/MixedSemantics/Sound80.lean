import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons80

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5120 node5120Labels = Sparse.eval nodeValue5120 (mixedVector B) := by
  have h := singleton5120 B _hB
  rw [sound2844 B _hB _hF, sound3609 B _hB _hF] at h
  norm_num [nodeValue5120, nodeValue2844, nodeValue3609, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5121 node5121Labels = Sparse.eval nodeValue5121 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5121) = mixedMoment B node5121 node5121Labels := rfl
  simpa [nodeValue5121, Sparse.eval] using hc.symm

theorem sound5122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5122 node5122Labels = Sparse.eval nodeValue5122 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5122) = mixedMoment B node5122 node5122Labels := rfl
  simpa [nodeValue5122, Sparse.eval] using hc.symm

theorem sound5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5123 node5123Labels = Sparse.eval nodeValue5123 (mixedVector B) := by
  have h := singleton5123 B _hB
  rw [sound2536 B _hB _hF, sound3370 B _hB _hF] at h
  norm_num [nodeValue5123, nodeValue2536, nodeValue3370, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5124 node5124Labels = Sparse.eval nodeValue5124 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5124) = mixedMoment B node5124 node5124Labels := rfl
  simpa [nodeValue5124, Sparse.eval] using hc.symm

theorem sound5125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5125 node5125Labels = Sparse.eval nodeValue5125 (mixedVector B) := by
  have h := singleton5125 B _hB
  rw [sound2539 B _hB _hF, sound3372 B _hB _hF] at h
  norm_num [nodeValue5125, nodeValue2539, nodeValue3372, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5126 node5126Labels = Sparse.eval nodeValue5126 (mixedVector B) := by
  have h := singleton5126 B _hB
  rw [sound2541 B _hB _hF, sound3487 B _hB _hF] at h
  norm_num [nodeValue5126, nodeValue2541, nodeValue3487, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5127 node5127Labels = Sparse.eval nodeValue5127 (mixedVector B) := by
  simpa only [nodeValue5127, Sparse.eval_nil] using zero5127 B _hB _hF

theorem sound5128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5128 node5128Labels = Sparse.eval nodeValue5128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5128) = mixedMoment B node5128 node5128Labels := rfl
  simpa [nodeValue5128, Sparse.eval] using hc.symm

theorem sound5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5129 node5129Labels = Sparse.eval nodeValue5129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5129) = mixedMoment B node5129 node5129Labels := rfl
  simpa [nodeValue5129, Sparse.eval] using hc.symm

theorem sound5130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5130 node5130Labels = Sparse.eval nodeValue5130 (mixedVector B) := by
  simpa only [nodeValue5130, Sparse.eval_nil] using zero5130 B _hB _hF

theorem sound5131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5131 node5131Labels = Sparse.eval nodeValue5131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5131) = mixedMoment B node5131 node5131Labels := rfl
  simpa [nodeValue5131, Sparse.eval] using hc.symm

theorem sound5132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5132 node5132Labels = Sparse.eval nodeValue5132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5132) = mixedMoment B node5132 node5132Labels := rfl
  simpa [nodeValue5132, Sparse.eval] using hc.symm

theorem sound5133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5133 node5133Labels = Sparse.eval nodeValue5133 (mixedVector B) := by
  simpa only [nodeValue5133, Sparse.eval_nil] using zero5133 B _hB _hF

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5135 node5135Labels = Sparse.eval nodeValue5135 (mixedVector B) := by
  simpa only [nodeValue5135, Sparse.eval_nil] using zero5135 B _hB _hF

theorem sound5136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5136 node5136Labels = Sparse.eval nodeValue5136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5136) = mixedMoment B node5136 node5136Labels := rfl
  simpa [nodeValue5136, Sparse.eval] using hc.symm

theorem sound5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5137 node5137Labels = Sparse.eval nodeValue5137 (mixedVector B) := by
  have h := singleton5137 B _hB
  rw [sound2556 B _hB _hF, sound3521 B _hB _hF] at h
  norm_num [nodeValue5137, nodeValue2556, nodeValue3521, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5138 node5138Labels = Sparse.eval nodeValue5138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5138) = mixedMoment B node5138 node5138Labels := rfl
  simpa [nodeValue5138, Sparse.eval] using hc.symm

theorem sound5139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5139 node5139Labels = Sparse.eval nodeValue5139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5139) = mixedMoment B node5139 node5139Labels := rfl
  simpa [nodeValue5139, Sparse.eval] using hc.symm

theorem sound5140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5140 node5140Labels = Sparse.eval nodeValue5140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5140) = mixedMoment B node5140 node5140Labels := rfl
  simpa [nodeValue5140, Sparse.eval] using hc.symm

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5142 node5142Labels = Sparse.eval nodeValue5142 (mixedVector B) := by
  have h := singleton5142 B _hB
  rw [sound2913 B _hB _hF, sound3610 B _hB _hF] at h
  norm_num [nodeValue5142, nodeValue2913, nodeValue3610, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5143 node5143Labels = Sparse.eval nodeValue5143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5143) = mixedMoment B node5143 node5143Labels := rfl
  simpa [nodeValue5143, Sparse.eval] using hc.symm

theorem sound5144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5144 node5144Labels = Sparse.eval nodeValue5144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5144) = mixedMoment B node5144 node5144Labels := rfl
  simpa [nodeValue5144, Sparse.eval] using hc.symm

theorem sound5145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5145 node5145Labels = Sparse.eval nodeValue5145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5145) = mixedMoment B node5145 node5145Labels := rfl
  simpa [nodeValue5145, Sparse.eval] using hc.symm

theorem sound5146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5146 node5146Labels = Sparse.eval nodeValue5146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5146) = mixedMoment B node5146 node5146Labels := rfl
  simpa [nodeValue5146, Sparse.eval] using hc.symm

theorem sound5147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5147 node5147Labels = Sparse.eval nodeValue5147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5147) = mixedMoment B node5147 node5147Labels := rfl
  simpa [nodeValue5147, Sparse.eval] using hc.symm

theorem sound5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5148 node5148Labels = Sparse.eval nodeValue5148 (mixedVector B) := by
  simpa only [nodeValue5148, Sparse.eval_nil] using zero5148 B _hB _hF

theorem sound5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5149 node5149Labels = Sparse.eval nodeValue5149 (mixedVector B) := by
  have h := singleton5149 B _hB
  rw [sound2924 B _hB _hF, sound3605 B _hB _hF] at h
  norm_num [nodeValue5149, nodeValue2924, nodeValue3605, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5150 node5150Labels = Sparse.eval nodeValue5150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5150) = mixedMoment B node5150 node5150Labels := rfl
  simpa [nodeValue5150, Sparse.eval] using hc.symm

theorem sound5151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5151 node5151Labels = Sparse.eval nodeValue5151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5151) = mixedMoment B node5151 node5151Labels := rfl
  simpa [nodeValue5151, Sparse.eval] using hc.symm

theorem sound5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5152 node5152Labels = Sparse.eval nodeValue5152 (mixedVector B) := by
  have h := singleton5152 B _hB
  rw [sound2931 B _hB _hF, sound3612 B _hB _hF] at h
  norm_num [nodeValue5152, nodeValue2931, nodeValue3612, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5153 node5153Labels = Sparse.eval nodeValue5153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5153) = mixedMoment B node5153 node5153Labels := rfl
  simpa [nodeValue5153, Sparse.eval] using hc.symm

theorem sound5154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5154 node5154Labels = Sparse.eval nodeValue5154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5154) = mixedMoment B node5154 node5154Labels := rfl
  simpa [nodeValue5154, Sparse.eval] using hc.symm

theorem sound5155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5155 node5155Labels = Sparse.eval nodeValue5155 (mixedVector B) := by
  have h := singleton5155 B _hB
  rw [sound2908 B _hB _hF, sound3600 B _hB _hF] at h
  norm_num [nodeValue5155, nodeValue2908, nodeValue3600, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5156 node5156Labels = Sparse.eval nodeValue5156 (mixedVector B) := by
  have h := singleton5156 B _hB
  rw [sound2911 B _hB _hF, sound3611 B _hB _hF] at h
  norm_num [nodeValue5156, nodeValue2911, nodeValue3611, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5157 node5157Labels = Sparse.eval nodeValue5157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5157) = mixedMoment B node5157 node5157Labels := rfl
  simpa [nodeValue5157, Sparse.eval] using hc.symm

theorem sound5158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5158 node5158Labels = Sparse.eval nodeValue5158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5158) = mixedMoment B node5158 node5158Labels := rfl
  simpa [nodeValue5158, Sparse.eval] using hc.symm

theorem sound5159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5159 node5159Labels = Sparse.eval nodeValue5159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5159) = mixedMoment B node5159 node5159Labels := rfl
  simpa [nodeValue5159, Sparse.eval] using hc.symm

theorem sound5160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5160 node5160Labels = Sparse.eval nodeValue5160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5160) = mixedMoment B node5160 node5160Labels := rfl
  simpa [nodeValue5160, Sparse.eval] using hc.symm

theorem sound5161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5161 node5161Labels = Sparse.eval nodeValue5161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5161) = mixedMoment B node5161 node5161Labels := rfl
  simpa [nodeValue5161, Sparse.eval] using hc.symm

theorem sound5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5162 node5162Labels = Sparse.eval nodeValue5162 (mixedVector B) := by
  have h := singleton5162 B _hB
  rw [sound2589 B _hB _hF, sound3563 B _hB _hF] at h
  norm_num [nodeValue5162, nodeValue2589, nodeValue3563, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5163 node5163Labels = Sparse.eval nodeValue5163 (mixedVector B) := by
  have h := singleton5163 B _hB
  rw [sound2590 B _hB _hF, sound3564 B _hB _hF] at h
  norm_num [nodeValue5163, nodeValue2590, nodeValue3564, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5164 node5164Labels = Sparse.eval nodeValue5164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5164) = mixedMoment B node5164 node5164Labels := rfl
  simpa [nodeValue5164, Sparse.eval] using hc.symm

theorem sound5165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5165 node5165Labels = Sparse.eval nodeValue5165 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5165) = mixedMoment B node5165 node5165Labels := rfl
  simpa [nodeValue5165, Sparse.eval] using hc.symm

theorem sound5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5166 node5166Labels = Sparse.eval nodeValue5166 (mixedVector B) := by
  simpa only [nodeValue5166, Sparse.eval_nil] using zero5166 B _hB _hF

theorem sound5167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5167 node5167Labels = Sparse.eval nodeValue5167 (mixedVector B) := by
  have h := singleton5167 B _hB
  rw [sound2593 B _hB _hF, sound3602 B _hB _hF] at h
  norm_num [nodeValue5167, nodeValue2593, nodeValue3602, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5168 node5168Labels = Sparse.eval nodeValue5168 (mixedVector B) := by
  have h := singleton5168 B _hB
  rw [sound2594 B _hB _hF, sound3603 B _hB _hF] at h
  norm_num [nodeValue5168, nodeValue2594, nodeValue3603, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5169 node5169Labels = Sparse.eval nodeValue5169 (mixedVector B) := by
  have h := singleton5169 B _hB
  rw [sound2595 B _hB _hF, sound3607 B _hB _hF] at h
  norm_num [nodeValue5169, nodeValue2595, nodeValue3607, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5170 node5170Labels = Sparse.eval nodeValue5170 (mixedVector B) := by
  have h := singleton5170 B _hB
  rw [sound2954 B _hB _hF, sound3606 B _hB _hF] at h
  norm_num [nodeValue5170, nodeValue2954, nodeValue3606, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5171 node5171Labels = Sparse.eval nodeValue5171 (mixedVector B) := by
  have h := singleton5171 B _hB
  rw [sound2598 B _hB _hF, sound3608 B _hB _hF] at h
  norm_num [nodeValue5171, nodeValue2598, nodeValue3608, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5172 node5172Labels = Sparse.eval nodeValue5172 (mixedVector B) := by
  have h := singleton5172 B _hB
  rw [sound2599 B _hB _hF, sound3613 B _hB _hF] at h
  norm_num [nodeValue5172, nodeValue2599, nodeValue3613, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5173 node5173Labels = Sparse.eval nodeValue5173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5173) = mixedMoment B node5173 node5173Labels := rfl
  simpa [nodeValue5173, Sparse.eval] using hc.symm

theorem sound5174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5174 node5174Labels = Sparse.eval nodeValue5174 (mixedVector B) := by
  have h := singleton5174 B _hB
  rw [sound2601 B _hB _hF, sound3615 B _hB _hF] at h
  norm_num [nodeValue5174, nodeValue2601, nodeValue3615, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5175 node5175Labels = Sparse.eval nodeValue5175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5175) = mixedMoment B node5175 node5175Labels := rfl
  simpa [nodeValue5175, Sparse.eval] using hc.symm

theorem sound5176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5176 node5176Labels = Sparse.eval nodeValue5176 (mixedVector B) := by
  have h := singleton5176 B _hB
  rw [sound2604 B _hB _hF, sound3614 B _hB _hF] at h
  norm_num [nodeValue5176, nodeValue2604, nodeValue3614, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5177 node5177Labels = Sparse.eval nodeValue5177 (mixedVector B) := by
  have h := singleton5177 B _hB
  rw [sound2605 B _hB _hF, sound3616 B _hB _hF] at h
  norm_num [nodeValue5177, nodeValue2605, nodeValue3616, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5178 node5178Labels = Sparse.eval nodeValue5178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5178) = mixedMoment B node5178 node5178Labels := rfl
  simpa [nodeValue5178, Sparse.eval] using hc.symm

theorem sound5179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5179 node5179Labels = Sparse.eval nodeValue5179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5179) = mixedMoment B node5179 node5179Labels := rfl
  simpa [nodeValue5179, Sparse.eval] using hc.symm

theorem sound5180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5180 node5180Labels = Sparse.eval nodeValue5180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5180) = mixedMoment B node5180 node5180Labels := rfl
  simpa [nodeValue5180, Sparse.eval] using hc.symm

theorem sound5181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5181 node5181Labels = Sparse.eval nodeValue5181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5181) = mixedMoment B node5181 node5181Labels := rfl
  simpa [nodeValue5181, Sparse.eval] using hc.symm

theorem sound5182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5182 node5182Labels = Sparse.eval nodeValue5182 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5182) = mixedMoment B node5182 node5182Labels := rfl
  simpa [nodeValue5182, Sparse.eval] using hc.symm

theorem sound5183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5183 node5183Labels = Sparse.eval nodeValue5183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5183) = mixedMoment B node5183 node5183Labels := rfl
  simpa [nodeValue5183, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
