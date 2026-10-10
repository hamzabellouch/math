import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons66

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4224 node4224Labels = Sparse.eval nodeValue4224 (mixedVector B) := by
  have h := singleton4224 B _hB
  rw [sound725 B _hB _hF, sound771 B _hB _hF] at h
  norm_num [nodeValue4224, nodeValue725, nodeValue771, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4225 node4225Labels = Sparse.eval nodeValue4225 (mixedVector B) := by
  have h := singleton4225 B _hB
  rw [sound726 B _hB _hF, sound774 B _hB _hF] at h
  norm_num [nodeValue4225, nodeValue726, nodeValue774, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4226 node4226Labels = Sparse.eval nodeValue4226 (mixedVector B) := by
  have h := singleton4226 B _hB
  rw [sound727 B _hB _hF, sound759 B _hB _hF] at h
  norm_num [nodeValue4226, nodeValue727, nodeValue759, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4227 node4227Labels = Sparse.eval nodeValue4227 (mixedVector B) := by
  simpa only [nodeValue4227, Sparse.eval_nil] using zero4227 B _hB _hF

theorem sound4228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4228 node4228Labels = Sparse.eval nodeValue4228 (mixedVector B) := by
  simpa only [nodeValue4228, Sparse.eval_nil] using zero4228 B _hB _hF

theorem sound4229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4229 node4229Labels = Sparse.eval nodeValue4229 (mixedVector B) := by
  have h := singleton4229 B _hB
  rw [sound729 B _hB _hF, sound773 B _hB _hF] at h
  norm_num [nodeValue4229, nodeValue729, nodeValue773, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4230 node4230Labels = Sparse.eval nodeValue4230 (mixedVector B) := by
  have h := singleton4230 B _hB
  rw [sound730 B _hB _hF, sound780 B _hB _hF] at h
  norm_num [nodeValue4230, nodeValue730, nodeValue780, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4231 node4231Labels = Sparse.eval nodeValue4231 (mixedVector B) := by
  have h := singleton4231 B _hB
  rw [sound731 B _hB _hF, sound781 B _hB _hF] at h
  norm_num [nodeValue4231, nodeValue731, nodeValue781, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4232 node4232Labels = Sparse.eval nodeValue4232 (mixedVector B) := by
  have h := singleton4232 B _hB
  rw [sound732 B _hB _hF, sound798 B _hB _hF] at h
  norm_num [nodeValue4232, nodeValue732, nodeValue798, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4233 node4233Labels = Sparse.eval nodeValue4233 (mixedVector B) := by
  have h := singleton4233 B _hB
  rw [sound733 B _hB _hF, sound799 B _hB _hF] at h
  norm_num [nodeValue4233, nodeValue733, nodeValue799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4234 node4234Labels = Sparse.eval nodeValue4234 (mixedVector B) := by
  have h := singleton4234 B _hB
  rw [sound734 B _hB _hF, sound800 B _hB _hF] at h
  norm_num [nodeValue4234, nodeValue734, nodeValue800, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4235 node4235Labels = Sparse.eval nodeValue4235 (mixedVector B) := by
  have h := singleton4235 B _hB
  rw [sound735 B _hB _hF, sound801 B _hB _hF] at h
  norm_num [nodeValue4235, nodeValue735, nodeValue801, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4236 node4236Labels = Sparse.eval nodeValue4236 (mixedVector B) := by
  have h := singleton4236 B _hB
  rw [sound736 B _hB _hF, sound818 B _hB _hF] at h
  norm_num [nodeValue4236, nodeValue736, nodeValue818, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4237 node4237Labels = Sparse.eval nodeValue4237 (mixedVector B) := by
  have h := singleton4237 B _hB
  rw [sound737 B _hB _hF, sound840 B _hB _hF] at h
  norm_num [nodeValue4237, nodeValue737, nodeValue840, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4238 node4238Labels = Sparse.eval nodeValue4238 (mixedVector B) := by
  have h := singleton4238 B _hB
  rw [sound738 B _hB _hF, sound819 B _hB _hF] at h
  norm_num [nodeValue4238, nodeValue738, nodeValue819, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4239 node4239Labels = Sparse.eval nodeValue4239 (mixedVector B) := by
  have h := singleton4239 B _hB
  rw [sound739 B _hB _hF, sound841 B _hB _hF] at h
  norm_num [nodeValue4239, nodeValue739, nodeValue841, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4240 node4240Labels = Sparse.eval nodeValue4240 (mixedVector B) := by
  have h := singleton4240 B _hB
  rw [sound740 B _hB _hF, sound842 B _hB _hF] at h
  norm_num [nodeValue4240, nodeValue740, nodeValue842, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4241 node4241Labels = Sparse.eval nodeValue4241 (mixedVector B) := by
  have h := singleton4241 B _hB
  rw [sound741 B _hB _hF, sound820 B _hB _hF] at h
  norm_num [nodeValue4241, nodeValue741, nodeValue820, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4242 node4242Labels = Sparse.eval nodeValue4242 (mixedVector B) := by
  have h := singleton4242 B _hB
  rw [sound742 B _hB _hF, sound843 B _hB _hF] at h
  norm_num [nodeValue4242, nodeValue742, nodeValue843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4243 node4243Labels = Sparse.eval nodeValue4243 (mixedVector B) := by
  have h := singleton4243 B _hB
  rw [sound743 B _hB _hF, sound844 B _hB _hF] at h
  norm_num [nodeValue4243, nodeValue743, nodeValue844, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4244 node4244Labels = Sparse.eval nodeValue4244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4244) = mixedMoment B node4244 node4244Labels := rfl
  simpa [nodeValue4244, Sparse.eval] using hc.symm

theorem sound4245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4245 node4245Labels = Sparse.eval nodeValue4245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4245) = mixedMoment B node4245 node4245Labels := rfl
  simpa [nodeValue4245, Sparse.eval] using hc.symm

theorem sound4246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4246 node4246Labels = Sparse.eval nodeValue4246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4246) = mixedMoment B node4246 node4246Labels := rfl
  simpa [nodeValue4246, Sparse.eval] using hc.symm

theorem sound4247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4247 node4247Labels = Sparse.eval nodeValue4247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4247) = mixedMoment B node4247 node4247Labels := rfl
  simpa [nodeValue4247, Sparse.eval] using hc.symm

theorem sound4248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4248 node4248Labels = Sparse.eval nodeValue4248 (mixedVector B) := by
  have h := singleton4248 B _hB
  rw [sound782 B _hB _hF] at h
  norm_num [nodeValue4248, nodeValue782, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4249 node4249Labels = Sparse.eval nodeValue4249 (mixedVector B) := by
  have h := singleton4249 B _hB
  rw [sound783 B _hB _hF, sound803 B _hB _hF] at h
  norm_num [nodeValue4249, nodeValue783, nodeValue803, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4250 node4250Labels = Sparse.eval nodeValue4250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4250) = mixedMoment B node4250 node4250Labels := rfl
  simpa [nodeValue4250, Sparse.eval] using hc.symm

theorem sound4251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4251 node4251Labels = Sparse.eval nodeValue4251 (mixedVector B) := by
  have h := singleton4251 B _hB
  rw [sound785 B _hB _hF, sound804 B _hB _hF] at h
  norm_num [nodeValue4251, nodeValue785, nodeValue804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4252 node4252Labels = Sparse.eval nodeValue4252 (mixedVector B) := by
  have h := singleton4252 B _hB
  rw [sound786 B _hB _hF, sound822 B _hB _hF] at h
  norm_num [nodeValue4252, nodeValue786, nodeValue822, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4253 node4253Labels = Sparse.eval nodeValue4253 (mixedVector B) := by
  have h := singleton4253 B _hB
  rw [sound787 B _hB _hF, sound847 B _hB _hF] at h
  norm_num [nodeValue4253, nodeValue787, nodeValue847, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4254 node4254Labels = Sparse.eval nodeValue4254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4254) = mixedMoment B node4254 node4254Labels := rfl
  simpa [nodeValue4254, Sparse.eval] using hc.symm

theorem sound4255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4255 node4255Labels = Sparse.eval nodeValue4255 (mixedVector B) := by
  have h := singleton4255 B _hB
  rw [sound789 B _hB _hF, sound823 B _hB _hF] at h
  norm_num [nodeValue4255, nodeValue789, nodeValue823, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4256 node4256Labels = Sparse.eval nodeValue4256 (mixedVector B) := by
  have h := singleton4256 B _hB
  rw [sound790 B _hB _hF, sound848 B _hB _hF] at h
  norm_num [nodeValue4256, nodeValue790, nodeValue848, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4257 node4257Labels = Sparse.eval nodeValue4257 (mixedVector B) := by
  have h := singleton4257 B _hB
  rw [sound791 B _hB _hF, sound849 B _hB _hF] at h
  norm_num [nodeValue4257, nodeValue791, nodeValue849, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4258 node4258Labels = Sparse.eval nodeValue4258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4258) = mixedMoment B node4258 node4258Labels := rfl
  simpa [nodeValue4258, Sparse.eval] using hc.symm

theorem sound4259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4259 node4259Labels = Sparse.eval nodeValue4259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4259) = mixedMoment B node4259 node4259Labels := rfl
  simpa [nodeValue4259, Sparse.eval] using hc.symm

theorem sound4260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4260 node4260Labels = Sparse.eval nodeValue4260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4260) = mixedMoment B node4260 node4260Labels := rfl
  simpa [nodeValue4260, Sparse.eval] using hc.symm

theorem sound4261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4261 node4261Labels = Sparse.eval nodeValue4261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4261) = mixedMoment B node4261 node4261Labels := rfl
  simpa [nodeValue4261, Sparse.eval] using hc.symm

theorem sound4262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4262 node4262Labels = Sparse.eval nodeValue4262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4262) = mixedMoment B node4262 node4262Labels := rfl
  simpa [nodeValue4262, Sparse.eval] using hc.symm

theorem sound4263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4263 node4263Labels = Sparse.eval nodeValue4263 (mixedVector B) := by
  simpa only [nodeValue4263, Sparse.eval_nil] using zero4263 B _hB _hF

theorem sound4264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4264 node4264Labels = Sparse.eval nodeValue4264 (mixedVector B) := by
  simpa only [nodeValue4264, Sparse.eval_nil] using zero4264 B _hB _hF

theorem sound4265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4265 node4265Labels = Sparse.eval nodeValue4265 (mixedVector B) := by
  have h := singleton4265 B _hB
  rw [sound807 B _hB _hF] at h
  norm_num [nodeValue4265, nodeValue807, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4266 node4266Labels = Sparse.eval nodeValue4266 (mixedVector B) := by
  simpa only [nodeValue4266, Sparse.eval_nil] using zero4266 B _hB _hF

theorem sound4267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4267 node4267Labels = Sparse.eval nodeValue4267 (mixedVector B) := by
  simpa only [nodeValue4267, Sparse.eval_nil] using zero4267 B _hB _hF

theorem sound4268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4268 node4268Labels = Sparse.eval nodeValue4268 (mixedVector B) := by
  have h := singleton4268 B _hB
  rw [sound811 B _hB _hF, sound824 B _hB _hF] at h
  norm_num [nodeValue4268, nodeValue811, nodeValue824, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4269 node4269Labels = Sparse.eval nodeValue4269 (mixedVector B) := by
  simpa only [nodeValue4269, Sparse.eval_nil] using zero4269 B _hB _hF

theorem sound4270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4270 node4270Labels = Sparse.eval nodeValue4270 (mixedVector B) := by
  have h := singleton4270 B _hB
  rw [sound813 B _hB _hF, sound853 B _hB _hF] at h
  norm_num [nodeValue4270, nodeValue813, nodeValue853, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4271 node4271Labels = Sparse.eval nodeValue4271 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4271) = mixedMoment B node4271 node4271Labels := rfl
  simpa [nodeValue4271, Sparse.eval] using hc.symm

theorem sound4272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4272 node4272Labels = Sparse.eval nodeValue4272 (mixedVector B) := by
  have h := singleton4272 B _hB
  rw [sound815 B _hB _hF, sound826 B _hB _hF] at h
  norm_num [nodeValue4272, nodeValue815, nodeValue826, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4273 node4273Labels = Sparse.eval nodeValue4273 (mixedVector B) := by
  simpa only [nodeValue4273, Sparse.eval_nil] using zero4273 B _hB _hF

theorem sound4274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4274 node4274Labels = Sparse.eval nodeValue4274 (mixedVector B) := by
  simpa only [nodeValue4274, Sparse.eval_nil] using zero4274 B _hB _hF

theorem sound4275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4275 node4275Labels = Sparse.eval nodeValue4275 (mixedVector B) := by
  have h := singleton4275 B _hB
  rw [sound827 B _hB _hF] at h
  norm_num [nodeValue4275, nodeValue827, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4276 node4276Labels = Sparse.eval nodeValue4276 (mixedVector B) := by
  have h := singleton4276 B _hB
  rw [sound828 B _hB _hF, sound857 B _hB _hF] at h
  norm_num [nodeValue4276, nodeValue828, nodeValue857, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4277 node4277Labels = Sparse.eval nodeValue4277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4277) = mixedMoment B node4277 node4277Labels := rfl
  simpa [nodeValue4277, Sparse.eval] using hc.symm

theorem sound4278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4278 node4278Labels = Sparse.eval nodeValue4278 (mixedVector B) := by
  have h := singleton4278 B _hB
  rw [sound830 B _hB _hF] at h
  norm_num [nodeValue4278, nodeValue830, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4279 node4279Labels = Sparse.eval nodeValue4279 (mixedVector B) := by
  have h := singleton4279 B _hB
  rw [sound831 B _hB _hF, sound858 B _hB _hF] at h
  norm_num [nodeValue4279, nodeValue831, nodeValue858, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4280 node4280Labels = Sparse.eval nodeValue4280 (mixedVector B) := by
  have h := singleton4280 B _hB
  rw [sound832 B _hB _hF, sound862 B _hB _hF] at h
  norm_num [nodeValue4280, nodeValue832, nodeValue862, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4281 node4281Labels = Sparse.eval nodeValue4281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4281) = mixedMoment B node4281 node4281Labels := rfl
  simpa [nodeValue4281, Sparse.eval] using hc.symm

theorem sound4282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4282 node4282Labels = Sparse.eval nodeValue4282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4282) = mixedMoment B node4282 node4282Labels := rfl
  simpa [nodeValue4282, Sparse.eval] using hc.symm

theorem sound4283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4283 node4283Labels = Sparse.eval nodeValue4283 (mixedVector B) := by
  simpa only [nodeValue4283, Sparse.eval_nil] using zero4283 B _hB _hF

theorem sound4284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4284 node4284Labels = Sparse.eval nodeValue4284 (mixedVector B) := by
  simpa only [nodeValue4284, Sparse.eval_nil] using zero4284 B _hB _hF

theorem sound4285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4285 node4285Labels = Sparse.eval nodeValue4285 (mixedVector B) := by
  have h := singleton4285 B _hB
  rw [sound860 B _hB _hF] at h
  norm_num [nodeValue4285, nodeValue860, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4286 node4286Labels = Sparse.eval nodeValue4286 (mixedVector B) := by
  have h := singleton4286 B _hB
  rw [sound864 B _hB _hF, sound1550 B _hB _hF] at h
  norm_num [nodeValue4286, nodeValue864, nodeValue1550, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4287 node4287Labels = Sparse.eval nodeValue4287 (mixedVector B) := by
  have h := singleton4287 B _hB
  rw [sound865 B _hB _hF, sound1553 B _hB _hF] at h
  norm_num [nodeValue4287, nodeValue865, nodeValue1553, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
