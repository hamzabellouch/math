import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4864 node4864Labels = Sparse.eval nodeValue4864 (mixedVector B) := by
  have h := singleton4864 B _hB
  rw [sound2105 B _hB _hF, sound2241 B _hB _hF] at h
  norm_num [nodeValue4864, nodeValue2105, nodeValue2241, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4865 node4865Labels = Sparse.eval nodeValue4865 (mixedVector B) := by
  have h := singleton4865 B _hB
  rw [sound2106 B _hB _hF, sound2242 B _hB _hF] at h
  norm_num [nodeValue4865, nodeValue2106, nodeValue2242, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4866 node4866Labels = Sparse.eval nodeValue4866 (mixedVector B) := by
  have h := singleton4866 B _hB
  rw [sound2107 B _hB _hF, sound2260 B _hB _hF] at h
  norm_num [nodeValue4866, nodeValue2107, nodeValue2260, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4867 node4867Labels = Sparse.eval nodeValue4867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4867) = mixedMoment B node4867 node4867Labels := rfl
  simpa [nodeValue4867, Sparse.eval] using hc.symm

theorem sound4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4868 node4868Labels = Sparse.eval nodeValue4868 (mixedVector B) := by
  have h := singleton4868 B _hB
  rw [sound2109 B _hB _hF, sound2261 B _hB _hF] at h
  norm_num [nodeValue4868, nodeValue2109, nodeValue2261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4869 node4869Labels = Sparse.eval nodeValue4869 (mixedVector B) := by
  have h := singleton4869 B _hB
  rw [sound2110 B _hB _hF, sound2275 B _hB _hF] at h
  norm_num [nodeValue4869, nodeValue2110, nodeValue2275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4870 node4870Labels = Sparse.eval nodeValue4870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4870) = mixedMoment B node4870 node4870Labels := rfl
  simpa [nodeValue4870, Sparse.eval] using hc.symm

theorem sound4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4871 node4871Labels = Sparse.eval nodeValue4871 (mixedVector B) := by
  have h := singleton4871 B _hB
  rw [sound2112 B _hB _hF, sound2287 B _hB _hF] at h
  norm_num [nodeValue4871, nodeValue2112, nodeValue2287, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4872 node4872Labels = Sparse.eval nodeValue4872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4872) = mixedMoment B node4872 node4872Labels := rfl
  simpa [nodeValue4872, Sparse.eval] using hc.symm

theorem sound4873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4873 node4873Labels = Sparse.eval nodeValue4873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4873) = mixedMoment B node4873 node4873Labels := rfl
  simpa [nodeValue4873, Sparse.eval] using hc.symm

theorem sound4874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4874 node4874Labels = Sparse.eval nodeValue4874 (mixedVector B) := by
  have h := singleton4874 B _hB
  rw [sound2115 B _hB _hF, sound2276 B _hB _hF] at h
  norm_num [nodeValue4874, nodeValue2115, nodeValue2276, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4875 node4875Labels = Sparse.eval nodeValue4875 (mixedVector B) := by
  have h := singleton4875 B _hB
  rw [sound2116 B _hB _hF, sound2288 B _hB _hF] at h
  norm_num [nodeValue4875, nodeValue2116, nodeValue2288, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4876 node4876Labels = Sparse.eval nodeValue4876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4876) = mixedMoment B node4876 node4876Labels := rfl
  simpa [nodeValue4876, Sparse.eval] using hc.symm

theorem sound4877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4877 node4877Labels = Sparse.eval nodeValue4877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4877) = mixedMoment B node4877 node4877Labels := rfl
  simpa [nodeValue4877, Sparse.eval] using hc.symm

theorem sound4878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4878 node4878Labels = Sparse.eval nodeValue4878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4878) = mixedMoment B node4878 node4878Labels := rfl
  simpa [nodeValue4878, Sparse.eval] using hc.symm

theorem sound4879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4879 node4879Labels = Sparse.eval nodeValue4879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4879) = mixedMoment B node4879 node4879Labels := rfl
  simpa [nodeValue4879, Sparse.eval] using hc.symm

theorem sound4880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4880 node4880Labels = Sparse.eval nodeValue4880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4880) = mixedMoment B node4880 node4880Labels := rfl
  simpa [nodeValue4880, Sparse.eval] using hc.symm

theorem sound4881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4881 node4881Labels = Sparse.eval nodeValue4881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4881) = mixedMoment B node4881 node4881Labels := rfl
  simpa [nodeValue4881, Sparse.eval] using hc.symm

theorem sound4882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4882 node4882Labels = Sparse.eval nodeValue4882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4882) = mixedMoment B node4882 node4882Labels := rfl
  simpa [nodeValue4882, Sparse.eval] using hc.symm

theorem sound4883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4883 node4883Labels = Sparse.eval nodeValue4883 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4883) = mixedMoment B node4883 node4883Labels := rfl
  simpa [nodeValue4883, Sparse.eval] using hc.symm

theorem sound4884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4884 node4884Labels = Sparse.eval nodeValue4884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4884) = mixedMoment B node4884 node4884Labels := rfl
  simpa [nodeValue4884, Sparse.eval] using hc.symm

theorem sound4885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4885 node4885Labels = Sparse.eval nodeValue4885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4885) = mixedMoment B node4885 node4885Labels := rfl
  simpa [nodeValue4885, Sparse.eval] using hc.symm

theorem sound4886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4886 node4886Labels = Sparse.eval nodeValue4886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4886) = mixedMoment B node4886 node4886Labels := rfl
  simpa [nodeValue4886, Sparse.eval] using hc.symm

theorem sound4887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4887 node4887Labels = Sparse.eval nodeValue4887 (mixedVector B) := by
  have h := singleton4887 B _hB
  rw [sound2243 B _hB _hF] at h
  norm_num [nodeValue4887, nodeValue2243, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4891 node4891Labels = Sparse.eval nodeValue4891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4891) = mixedMoment B node4891 node4891Labels := rfl
  simpa [nodeValue4891, Sparse.eval] using hc.symm

theorem sound4892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4892 node4892Labels = Sparse.eval nodeValue4892 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4892) = mixedMoment B node4892 node4892Labels := rfl
  simpa [nodeValue4892, Sparse.eval] using hc.symm

theorem sound4893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = Sparse.eval nodeValue4893 (mixedVector B) := by
  simpa only [nodeValue4893, Sparse.eval_nil] using zero4893 B _hB _hF

theorem sound4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = Sparse.eval nodeValue4894 (mixedVector B) := by
  simpa only [nodeValue4894, Sparse.eval_nil] using zero4894 B _hB _hF

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

theorem sound4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4896 node4896Labels = Sparse.eval nodeValue4896 (mixedVector B) := by
  have h := singleton4896 B _hB
  rw [sound2266 B _hB _hF, sound2278 B _hB _hF] at h
  norm_num [nodeValue4896, nodeValue2266, nodeValue2278, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

theorem sound4900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4900 node4900Labels = Sparse.eval nodeValue4900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4900) = mixedMoment B node4900 node4900Labels := rfl
  simpa [nodeValue4900, Sparse.eval] using hc.symm

theorem sound4901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4901 node4901Labels = Sparse.eval nodeValue4901 (mixedVector B) := by
  simpa only [nodeValue4901, Sparse.eval_nil] using zero4901 B _hB _hF

theorem sound4902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4902 node4902Labels = Sparse.eval nodeValue4902 (mixedVector B) := by
  have h := singleton4902 B _hB
  rw [sound2295 B _hB _hF, sound3315 B _hB _hF] at h
  norm_num [nodeValue4902, nodeValue2295, nodeValue3315, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4903 node4903Labels = Sparse.eval nodeValue4903 (mixedVector B) := by
  have h := singleton4903 B _hB
  rw [sound2296 B _hB _hF, sound3316 B _hB _hF] at h
  norm_num [nodeValue4903, nodeValue2296, nodeValue3316, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4904 node4904Labels = Sparse.eval nodeValue4904 (mixedVector B) := by
  have h := singleton4904 B _hB
  rw [sound2297 B _hB _hF, sound3323 B _hB _hF] at h
  norm_num [nodeValue4904, nodeValue2297, nodeValue3323, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4905 node4905Labels = Sparse.eval nodeValue4905 (mixedVector B) := by
  have h := singleton4905 B _hB
  rw [sound2298 B _hB _hF, sound3320 B _hB _hF] at h
  norm_num [nodeValue4905, nodeValue2298, nodeValue3320, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4906 node4906Labels = Sparse.eval nodeValue4906 (mixedVector B) := by
  have h := singleton4906 B _hB
  rw [sound2299 B _hB _hF, sound3324 B _hB _hF] at h
  norm_num [nodeValue4906, nodeValue2299, nodeValue3324, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4907 node4907Labels = Sparse.eval nodeValue4907 (mixedVector B) := by
  have h := singleton4907 B _hB
  rw [sound2300 B _hB _hF, sound3325 B _hB _hF] at h
  norm_num [nodeValue4907, nodeValue2300, nodeValue3325, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4908 node4908Labels = Sparse.eval nodeValue4908 (mixedVector B) := by
  have h := singleton4908 B _hB
  rw [sound2301 B _hB _hF, sound3326 B _hB _hF] at h
  norm_num [nodeValue4908, nodeValue2301, nodeValue3326, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4909 node4909Labels = Sparse.eval nodeValue4909 (mixedVector B) := by
  have h := singleton4909 B _hB
  rw [sound2302 B _hB _hF, sound2448 B _hB _hF] at h
  norm_num [nodeValue4909, nodeValue2302, nodeValue2448, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4910 node4910Labels = Sparse.eval nodeValue4910 (mixedVector B) := by
  have h := singleton4910 B _hB
  rw [sound2303 B _hB _hF, sound3314 B _hB _hF] at h
  norm_num [nodeValue4910, nodeValue2303, nodeValue3314, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4911 node4911Labels = Sparse.eval nodeValue4911 (mixedVector B) := by
  simpa only [nodeValue4911, Sparse.eval_nil] using zero4911 B _hB _hF

theorem sound4912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4912 node4912Labels = Sparse.eval nodeValue4912 (mixedVector B) := by
  have h := singleton4912 B _hB
  rw [sound2305 B _hB _hF, sound3317 B _hB _hF] at h
  norm_num [nodeValue4912, nodeValue2305, nodeValue3317, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4913 node4913Labels = Sparse.eval nodeValue4913 (mixedVector B) := by
  have h := singleton4913 B _hB
  rw [sound2306 B _hB _hF, sound3318 B _hB _hF] at h
  norm_num [nodeValue4913, nodeValue2306, nodeValue3318, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4914 node4914Labels = Sparse.eval nodeValue4914 (mixedVector B) := by
  have h := singleton4914 B _hB
  rw [sound2307 B _hB _hF, sound2376 B _hB _hF] at h
  norm_num [nodeValue4914, nodeValue2307, nodeValue2376, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4915 node4915Labels = Sparse.eval nodeValue4915 (mixedVector B) := by
  simpa only [nodeValue4915, Sparse.eval_nil] using zero4915 B _hB _hF

theorem sound4916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4916 node4916Labels = Sparse.eval nodeValue4916 (mixedVector B) := by
  simpa only [nodeValue4916, Sparse.eval_nil] using zero4916 B _hB _hF

theorem sound4917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4917 node4917Labels = Sparse.eval nodeValue4917 (mixedVector B) := by
  have h := singleton4917 B _hB
  rw [sound2308 B _hB _hF, sound3321 B _hB _hF] at h
  norm_num [nodeValue4917, nodeValue2308, nodeValue3321, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4918 node4918Labels = Sparse.eval nodeValue4918 (mixedVector B) := by
  simpa only [nodeValue4918, Sparse.eval_nil] using zero4918 B _hB _hF

theorem sound4919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4919 node4919Labels = Sparse.eval nodeValue4919 (mixedVector B) := by
  have h := singleton4919 B _hB
  rw [sound2310 B _hB _hF, sound3329 B _hB _hF] at h
  norm_num [nodeValue4919, nodeValue2310, nodeValue3329, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4920 node4920Labels = Sparse.eval nodeValue4920 (mixedVector B) := by
  have h := singleton4920 B _hB
  rw [sound2311 B _hB _hF, sound2447 B _hB _hF] at h
  norm_num [nodeValue4920, nodeValue2311, nodeValue2447, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4921 node4921Labels = Sparse.eval nodeValue4921 (mixedVector B) := by
  simpa only [nodeValue4921, Sparse.eval_nil] using zero4921 B _hB _hF

theorem sound4922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4922 node4922Labels = Sparse.eval nodeValue4922 (mixedVector B) := by
  have h := singleton4922 B _hB
  rw [sound2313 B _hB _hF, sound3322 B _hB _hF] at h
  norm_num [nodeValue4922, nodeValue2313, nodeValue3322, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4923 node4923Labels = Sparse.eval nodeValue4923 (mixedVector B) := by
  have h := singleton4923 B _hB
  rw [sound2314 B _hB _hF, sound3330 B _hB _hF] at h
  norm_num [nodeValue4923, nodeValue2314, nodeValue3330, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4924 node4924Labels = Sparse.eval nodeValue4924 (mixedVector B) := by
  simpa only [nodeValue4924, Sparse.eval_nil] using zero4924 B _hB _hF

theorem sound4925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4925 node4925Labels = Sparse.eval nodeValue4925 (mixedVector B) := by
  have h := singleton4925 B _hB
  rw [sound2315 B _hB _hF, sound2369 B _hB _hF] at h
  norm_num [nodeValue4925, nodeValue2315, nodeValue2369, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4926 node4926Labels = Sparse.eval nodeValue4926 (mixedVector B) := by
  have h := singleton4926 B _hB
  rw [sound2316 B _hB _hF, sound3398 B _hB _hF] at h
  norm_num [nodeValue4926, nodeValue2316, nodeValue3398, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4927 node4927Labels = Sparse.eval nodeValue4927 (mixedVector B) := by
  have h := singleton4927 B _hB
  rw [sound2317 B _hB _hF, sound3399 B _hB _hF] at h
  norm_num [nodeValue4927, nodeValue2317, nodeValue3399, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
