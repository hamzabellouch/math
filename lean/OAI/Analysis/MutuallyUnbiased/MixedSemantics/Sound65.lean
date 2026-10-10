import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons65

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4160 node4160Labels = Sparse.eval nodeValue4160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4160) = mixedMoment B node4160 node4160Labels := rfl
  simpa [nodeValue4160, Sparse.eval] using hc.symm

theorem sound4161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4161 node4161Labels = Sparse.eval nodeValue4161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4161) = mixedMoment B node4161 node4161Labels := rfl
  simpa [nodeValue4161, Sparse.eval] using hc.symm

theorem sound4162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4162 node4162Labels = Sparse.eval nodeValue4162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4162) = mixedMoment B node4162 node4162Labels := rfl
  simpa [nodeValue4162, Sparse.eval] using hc.symm

theorem sound4163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4163 node4163Labels = Sparse.eval nodeValue4163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4163) = mixedMoment B node4163 node4163Labels := rfl
  simpa [nodeValue4163, Sparse.eval] using hc.symm

theorem sound4164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4164 node4164Labels = Sparse.eval nodeValue4164 (mixedVector B) := by
  have h := singleton4164 B _hB
  rw [sound592 B _hB _hF, sound1497 B _hB _hF] at h
  norm_num [nodeValue4164, nodeValue592, nodeValue1497, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4165 node4165Labels = Sparse.eval nodeValue4165 (mixedVector B) := by
  have h := singleton4165 B _hB
  rw [sound593 B _hB _hF, sound1498 B _hB _hF] at h
  norm_num [nodeValue4165, nodeValue593, nodeValue1498, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4166 node4166Labels = Sparse.eval nodeValue4166 (mixedVector B) := by
  have h := singleton4166 B _hB
  rw [sound594 B _hB _hF, sound1499 B _hB _hF] at h
  norm_num [nodeValue4166, nodeValue594, nodeValue1499, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4167 node4167Labels = Sparse.eval nodeValue4167 (mixedVector B) := by
  have h := singleton4167 B _hB
  rw [sound595 B _hB _hF, sound1500 B _hB _hF] at h
  norm_num [nodeValue4167, nodeValue595, nodeValue1500, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4168 node4168Labels = Sparse.eval nodeValue4168 (mixedVector B) := by
  have h := singleton4168 B _hB
  rw [sound596 B _hB _hF, sound845 B _hB _hF] at h
  norm_num [nodeValue4168, nodeValue596, nodeValue845, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4169 node4169Labels = Sparse.eval nodeValue4169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4169) = mixedMoment B node4169 node4169Labels := rfl
  simpa [nodeValue4169, Sparse.eval] using hc.symm

theorem sound4170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4170 node4170Labels = Sparse.eval nodeValue4170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4170) = mixedMoment B node4170 node4170Labels := rfl
  simpa [nodeValue4170, Sparse.eval] using hc.symm

theorem sound4171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4171 node4171Labels = Sparse.eval nodeValue4171 (mixedVector B) := by
  have h := singleton4171 B _hB
  rw [sound599 B _hB _hF, sound1506 B _hB _hF] at h
  norm_num [nodeValue4171, nodeValue599, nodeValue1506, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4172 node4172Labels = Sparse.eval nodeValue4172 (mixedVector B) := by
  have h := singleton4172 B _hB
  rw [sound600 B _hB _hF, sound1507 B _hB _hF] at h
  norm_num [nodeValue4172, nodeValue600, nodeValue1507, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4173 node4173Labels = Sparse.eval nodeValue4173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4173) = mixedMoment B node4173 node4173Labels := rfl
  simpa [nodeValue4173, Sparse.eval] using hc.symm

theorem sound4174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4174 node4174Labels = Sparse.eval nodeValue4174 (mixedVector B) := by
  have h := singleton4174 B _hB
  rw [sound602 B _hB _hF, sound1509 B _hB _hF] at h
  norm_num [nodeValue4174, nodeValue602, nodeValue1509, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4175 node4175Labels = Sparse.eval nodeValue4175 (mixedVector B) := by
  have h := singleton4175 B _hB
  rw [sound603 B _hB _hF, sound1517 B _hB _hF] at h
  norm_num [nodeValue4175, nodeValue603, nodeValue1517, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4176 node4176Labels = Sparse.eval nodeValue4176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4176) = mixedMoment B node4176 node4176Labels := rfl
  simpa [nodeValue4176, Sparse.eval] using hc.symm

theorem sound4177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4177 node4177Labels = Sparse.eval nodeValue4177 (mixedVector B) := by
  have h := singleton4177 B _hB
  rw [sound605 B _hB _hF, sound1518 B _hB _hF] at h
  norm_num [nodeValue4177, nodeValue605, nodeValue1518, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4178 node4178Labels = Sparse.eval nodeValue4178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4178) = mixedMoment B node4178 node4178Labels := rfl
  simpa [nodeValue4178, Sparse.eval] using hc.symm

theorem sound4179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4179 node4179Labels = Sparse.eval nodeValue4179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4179) = mixedMoment B node4179 node4179Labels := rfl
  simpa [nodeValue4179, Sparse.eval] using hc.symm

theorem sound4180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4180 node4180Labels = Sparse.eval nodeValue4180 (mixedVector B) := by
  have h := singleton4180 B _hB
  rw [sound608 B _hB _hF, sound1519 B _hB _hF] at h
  norm_num [nodeValue4180, nodeValue608, nodeValue1519, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4181 node4181Labels = Sparse.eval nodeValue4181 (mixedVector B) := by
  have h := singleton4181 B _hB
  rw [sound609 B _hB _hF, sound1521 B _hB _hF] at h
  norm_num [nodeValue4181, nodeValue609, nodeValue1521, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4182 node4182Labels = Sparse.eval nodeValue4182 (mixedVector B) := by
  have h := singleton4182 B _hB
  rw [sound610 B _hB _hF, sound1524 B _hB _hF] at h
  norm_num [nodeValue4182, nodeValue610, nodeValue1524, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4183 node4183Labels = Sparse.eval nodeValue4183 (mixedVector B) := by
  have h := singleton4183 B _hB
  rw [sound611 B _hB _hF, sound1535 B _hB _hF] at h
  norm_num [nodeValue4183, nodeValue611, nodeValue1535, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4184 node4184Labels = Sparse.eval nodeValue4184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4184) = mixedMoment B node4184 node4184Labels := rfl
  simpa [nodeValue4184, Sparse.eval] using hc.symm

theorem sound4185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4185 node4185Labels = Sparse.eval nodeValue4185 (mixedVector B) := by
  have h := singleton4185 B _hB
  rw [sound613 B _hB _hF, sound1525 B _hB _hF] at h
  norm_num [nodeValue4185, nodeValue613, nodeValue1525, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4186 node4186Labels = Sparse.eval nodeValue4186 (mixedVector B) := by
  have h := singleton4186 B _hB
  rw [sound614 B _hB _hF, sound1536 B _hB _hF] at h
  norm_num [nodeValue4186, nodeValue614, nodeValue1536, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4187 node4187Labels = Sparse.eval nodeValue4187 (mixedVector B) := by
  have h := singleton4187 B _hB
  rw [sound615 B _hB _hF, sound1537 B _hB _hF] at h
  norm_num [nodeValue4187, nodeValue615, nodeValue1537, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4188 node4188Labels = Sparse.eval nodeValue4188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4188) = mixedMoment B node4188 node4188Labels := rfl
  simpa [nodeValue4188, Sparse.eval] using hc.symm

theorem sound4189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4189 node4189Labels = Sparse.eval nodeValue4189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4189) = mixedMoment B node4189 node4189Labels := rfl
  simpa [nodeValue4189, Sparse.eval] using hc.symm

theorem sound4190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4190 node4190Labels = Sparse.eval nodeValue4190 (mixedVector B) := by
  have h := singleton4190 B _hB
  rw [sound618 B _hB _hF, sound1527 B _hB _hF] at h
  norm_num [nodeValue4190, nodeValue618, nodeValue1527, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4191 node4191Labels = Sparse.eval nodeValue4191 (mixedVector B) := by
  have h := singleton4191 B _hB
  rw [sound619 B _hB _hF, sound1538 B _hB _hF] at h
  norm_num [nodeValue4191, nodeValue619, nodeValue1538, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4192 node4192Labels = Sparse.eval nodeValue4192 (mixedVector B) := by
  have h := singleton4192 B _hB
  rw [sound620 B _hB _hF, sound1539 B _hB _hF] at h
  norm_num [nodeValue4192, nodeValue620, nodeValue1539, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4193 node4193Labels = Sparse.eval nodeValue4193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4193) = mixedMoment B node4193 node4193Labels := rfl
  simpa [nodeValue4193, Sparse.eval] using hc.symm

theorem sound4194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4194 node4194Labels = Sparse.eval nodeValue4194 (mixedVector B) := by
  have h := singleton4194 B _hB
  rw [sound622 B _hB _hF, sound1541 B _hB _hF] at h
  norm_num [nodeValue4194, nodeValue622, nodeValue1541, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4195 node4195Labels = Sparse.eval nodeValue4195 (mixedVector B) := by
  have h := singleton4195 B _hB
  rw [sound698 B _hB _hF, sound744 B _hB _hF] at h
  norm_num [nodeValue4195, nodeValue698, nodeValue744, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4196 node4196Labels = Sparse.eval nodeValue4196 (mixedVector B) := by
  have h := singleton4196 B _hB
  rw [sound699 B _hB _hF, sound748 B _hB _hF] at h
  norm_num [nodeValue4196, nodeValue699, nodeValue748, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4197 node4197Labels = Sparse.eval nodeValue4197 (mixedVector B) := by
  have h := singleton4197 B _hB
  rw [sound700 B _hB _hF, sound749 B _hB _hF] at h
  norm_num [nodeValue4197, nodeValue700, nodeValue749, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4198 node4198Labels = Sparse.eval nodeValue4198 (mixedVector B) := by
  have h := singleton4198 B _hB
  rw [sound701 B _hB _hF, sound750 B _hB _hF] at h
  norm_num [nodeValue4198, nodeValue701, nodeValue750, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4199 node4199Labels = Sparse.eval nodeValue4199 (mixedVector B) := by
  have h := singleton4199 B _hB
  rw [sound702 B _hB _hF, sound760 B _hB _hF] at h
  norm_num [nodeValue4199, nodeValue702, nodeValue760, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4200 node4200Labels = Sparse.eval nodeValue4200 (mixedVector B) := by
  have h := singleton4200 B _hB
  rw [sound703 B _hB _hF, sound754 B _hB _hF] at h
  norm_num [nodeValue4200, nodeValue703, nodeValue754, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4201 node4201Labels = Sparse.eval nodeValue4201 (mixedVector B) := by
  have h := singleton4201 B _hB
  rw [sound704 B _hB _hF, sound761 B _hB _hF] at h
  norm_num [nodeValue4201, nodeValue704, nodeValue761, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4202 node4202Labels = Sparse.eval nodeValue4202 (mixedVector B) := by
  have h := singleton4202 B _hB
  rw [sound705 B _hB _hF, sound762 B _hB _hF] at h
  norm_num [nodeValue4202, nodeValue705, nodeValue762, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4203 node4203Labels = Sparse.eval nodeValue4203 (mixedVector B) := by
  have h := singleton4203 B _hB
  rw [sound706 B _hB _hF, sound755 B _hB _hF] at h
  norm_num [nodeValue4203, nodeValue706, nodeValue755, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4204 node4204Labels = Sparse.eval nodeValue4204 (mixedVector B) := by
  have h := singleton4204 B _hB
  rw [sound707 B _hB _hF, sound763 B _hB _hF] at h
  norm_num [nodeValue4204, nodeValue707, nodeValue763, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4205 node4205Labels = Sparse.eval nodeValue4205 (mixedVector B) := by
  have h := singleton4205 B _hB
  rw [sound708 B _hB _hF, sound764 B _hB _hF] at h
  norm_num [nodeValue4205, nodeValue708, nodeValue764, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4206 node4206Labels = Sparse.eval nodeValue4206 (mixedVector B) := by
  have h := singleton4206 B _hB
  rw [sound709 B _hB _hF, sound745 B _hB _hF] at h
  norm_num [nodeValue4206, nodeValue709, nodeValue745, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4207 node4207Labels = Sparse.eval nodeValue4207 (mixedVector B) := by
  have h := singleton4207 B _hB
  rw [sound710 B _hB _hF, sound746 B _hB _hF] at h
  norm_num [nodeValue4207, nodeValue710, nodeValue746, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4208 node4208Labels = Sparse.eval nodeValue4208 (mixedVector B) := by
  have h := singleton4208 B _hB
  rw [sound711 B _hB _hF, sound747 B _hB _hF] at h
  norm_num [nodeValue4208, nodeValue711, nodeValue747, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4209 node4209Labels = Sparse.eval nodeValue4209 (mixedVector B) := by
  simpa only [nodeValue4209, Sparse.eval_nil] using zero4209 B _hB _hF

theorem sound4210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4210 node4210Labels = Sparse.eval nodeValue4210 (mixedVector B) := by
  have h := singleton4210 B _hB
  rw [sound713 B _hB _hF, sound751 B _hB _hF] at h
  norm_num [nodeValue4210, nodeValue713, nodeValue751, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4211 node4211Labels = Sparse.eval nodeValue4211 (mixedVector B) := by
  simpa only [nodeValue4211, Sparse.eval_nil] using zero4211 B _hB _hF

theorem sound4212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4212 node4212Labels = Sparse.eval nodeValue4212 (mixedVector B) := by
  have h := singleton4212 B _hB
  rw [sound715 B _hB _hF, sound753 B _hB _hF] at h
  norm_num [nodeValue4212, nodeValue715, nodeValue753, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4213 node4213Labels = Sparse.eval nodeValue4213 (mixedVector B) := by
  have h := singleton4213 B _hB
  rw [sound716 B _hB _hF, sound752 B _hB _hF] at h
  norm_num [nodeValue4213, nodeValue716, nodeValue752, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4214 node4214Labels = Sparse.eval nodeValue4214 (mixedVector B) := by
  simpa only [nodeValue4214, Sparse.eval_nil] using zero4214 B _hB _hF

theorem sound4215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4215 node4215Labels = Sparse.eval nodeValue4215 (mixedVector B) := by
  simpa only [nodeValue4215, Sparse.eval_nil] using zero4215 B _hB _hF

theorem sound4216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4216 node4216Labels = Sparse.eval nodeValue4216 (mixedVector B) := by
  simpa only [nodeValue4216, Sparse.eval_nil] using zero4216 B _hB _hF

theorem sound4217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4217 node4217Labels = Sparse.eval nodeValue4217 (mixedVector B) := by
  have h := singleton4217 B _hB
  rw [sound719 B _hB _hF, sound756 B _hB _hF] at h
  norm_num [nodeValue4217, nodeValue719, nodeValue756, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4218 node4218Labels = Sparse.eval nodeValue4218 (mixedVector B) := by
  simpa only [nodeValue4218, Sparse.eval_nil] using zero4218 B _hB _hF

theorem sound4219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4219 node4219Labels = Sparse.eval nodeValue4219 (mixedVector B) := by
  have h := singleton4219 B _hB
  rw [sound720 B _hB _hF, sound769 B _hB _hF] at h
  norm_num [nodeValue4219, nodeValue720, nodeValue769, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4220 node4220Labels = Sparse.eval nodeValue4220 (mixedVector B) := by
  have h := singleton4220 B _hB
  rw [sound721 B _hB _hF, sound757 B _hB _hF] at h
  norm_num [nodeValue4220, nodeValue721, nodeValue757, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4221 node4221Labels = Sparse.eval nodeValue4221 (mixedVector B) := by
  simpa only [nodeValue4221, Sparse.eval_nil] using zero4221 B _hB _hF

theorem sound4222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4222 node4222Labels = Sparse.eval nodeValue4222 (mixedVector B) := by
  simpa only [nodeValue4222, Sparse.eval_nil] using zero4222 B _hB _hF

theorem sound4223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4223 node4223Labels = Sparse.eval nodeValue4223 (mixedVector B) := by
  have h := singleton4223 B _hB
  rw [sound724 B _hB _hF, sound758 B _hB _hF] at h
  norm_num [nodeValue4223, nodeValue724, nodeValue758, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
