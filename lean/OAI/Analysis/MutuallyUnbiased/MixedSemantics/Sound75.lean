import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons75

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4800 node4800Labels = Sparse.eval nodeValue4800 (mixedVector B) := by
  have h := singleton4800 B _hB
  rw [sound2018 B _hB _hF] at h
  norm_num [nodeValue4800, nodeValue2018, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4801 node4801Labels = Sparse.eval nodeValue4801 (mixedVector B) := by
  have h := singleton4801 B _hB
  rw [sound2019 B _hB _hF, sound2190 B _hB _hF] at h
  norm_num [nodeValue4801, nodeValue2019, nodeValue2190, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4802 node4802Labels = Sparse.eval nodeValue4802 (mixedVector B) := by
  have h := singleton4802 B _hB
  rw [sound2020 B _hB _hF, sound2202 B _hB _hF] at h
  norm_num [nodeValue4802, nodeValue2020, nodeValue2202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4803 node4803Labels = Sparse.eval nodeValue4803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4803) = mixedMoment B node4803 node4803Labels := rfl
  simpa [nodeValue4803, Sparse.eval] using hc.symm

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4806 node4806Labels = Sparse.eval nodeValue4806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4806) = mixedMoment B node4806 node4806Labels := rfl
  simpa [nodeValue4806, Sparse.eval] using hc.symm

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4808 node4808Labels = Sparse.eval nodeValue4808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4808) = mixedMoment B node4808 node4808Labels := rfl
  simpa [nodeValue4808, Sparse.eval] using hc.symm

theorem sound4809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4809 node4809Labels = Sparse.eval nodeValue4809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4809) = mixedMoment B node4809 node4809Labels := rfl
  simpa [nodeValue4809, Sparse.eval] using hc.symm

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4811 node4811Labels = Sparse.eval nodeValue4811 (mixedVector B) := by
  have h := singleton4811 B _hB
  rw [sound2029 B _hB _hF, sound2225 B _hB _hF] at h
  norm_num [nodeValue4811, nodeValue2029, nodeValue2225, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4812 node4812Labels = Sparse.eval nodeValue4812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4812) = mixedMoment B node4812 node4812Labels := rfl
  simpa [nodeValue4812, Sparse.eval] using hc.symm

theorem sound4813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4813 node4813Labels = Sparse.eval nodeValue4813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4813) = mixedMoment B node4813 node4813Labels := rfl
  simpa [nodeValue4813, Sparse.eval] using hc.symm

theorem sound4814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4814 node4814Labels = Sparse.eval nodeValue4814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4814) = mixedMoment B node4814 node4814Labels := rfl
  simpa [nodeValue4814, Sparse.eval] using hc.symm

theorem sound4815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4815 node4815Labels = Sparse.eval nodeValue4815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4815) = mixedMoment B node4815 node4815Labels := rfl
  simpa [nodeValue4815, Sparse.eval] using hc.symm

theorem sound4816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4816 node4816Labels = Sparse.eval nodeValue4816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4816) = mixedMoment B node4816 node4816Labels := rfl
  simpa [nodeValue4816, Sparse.eval] using hc.symm

theorem sound4817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4817 node4817Labels = Sparse.eval nodeValue4817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4817) = mixedMoment B node4817 node4817Labels := rfl
  simpa [nodeValue4817, Sparse.eval] using hc.symm

theorem sound4818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4818 node4818Labels = Sparse.eval nodeValue4818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4818) = mixedMoment B node4818 node4818Labels := rfl
  simpa [nodeValue4818, Sparse.eval] using hc.symm

theorem sound4819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4819 node4819Labels = Sparse.eval nodeValue4819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4819) = mixedMoment B node4819 node4819Labels := rfl
  simpa [nodeValue4819, Sparse.eval] using hc.symm

theorem sound4820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4820 node4820Labels = Sparse.eval nodeValue4820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4820) = mixedMoment B node4820 node4820Labels := rfl
  simpa [nodeValue4820, Sparse.eval] using hc.symm

theorem sound4821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4821 node4821Labels = Sparse.eval nodeValue4821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4821) = mixedMoment B node4821 node4821Labels := rfl
  simpa [nodeValue4821, Sparse.eval] using hc.symm

theorem sound4822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4822 node4822Labels = Sparse.eval nodeValue4822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4822) = mixedMoment B node4822 node4822Labels := rfl
  simpa [nodeValue4822, Sparse.eval] using hc.symm

theorem sound4823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4823 node4823Labels = Sparse.eval nodeValue4823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4823) = mixedMoment B node4823 node4823Labels := rfl
  simpa [nodeValue4823, Sparse.eval] using hc.symm

theorem sound4824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4824 node4824Labels = Sparse.eval nodeValue4824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4824) = mixedMoment B node4824 node4824Labels := rfl
  simpa [nodeValue4824, Sparse.eval] using hc.symm

theorem sound4825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4825 node4825Labels = Sparse.eval nodeValue4825 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4825) = mixedMoment B node4825 node4825Labels := rfl
  simpa [nodeValue4825, Sparse.eval] using hc.symm

theorem sound4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4826 node4826Labels = Sparse.eval nodeValue4826 (mixedVector B) := by
  have h := singleton4826 B _hB
  rw [sound2046 B _hB _hF, sound2077 B _hB _hF] at h
  norm_num [nodeValue4826, nodeValue2046, nodeValue2077, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4827 node4827Labels = Sparse.eval nodeValue4827 (mixedVector B) := by
  have h := singleton4827 B _hB
  rw [sound2047 B _hB _hF, sound2079 B _hB _hF] at h
  norm_num [nodeValue4827, nodeValue2047, nodeValue2079, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4828 node4828Labels = Sparse.eval nodeValue4828 (mixedVector B) := by
  have h := singleton4828 B _hB
  rw [sound2048 B _hB _hF, sound2082 B _hB _hF] at h
  norm_num [nodeValue4828, nodeValue2048, nodeValue2082, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4829 node4829Labels = Sparse.eval nodeValue4829 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4829) = mixedMoment B node4829 node4829Labels := rfl
  simpa [nodeValue4829, Sparse.eval] using hc.symm

theorem sound4830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4830 node4830Labels = Sparse.eval nodeValue4830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4830) = mixedMoment B node4830 node4830Labels := rfl
  simpa [nodeValue4830, Sparse.eval] using hc.symm

theorem sound4831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4831 node4831Labels = Sparse.eval nodeValue4831 (mixedVector B) := by
  have h := singleton4831 B _hB
  rw [sound2051 B _hB _hF, sound2191 B _hB _hF] at h
  norm_num [nodeValue4831, nodeValue2051, nodeValue2191, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4832 node4832Labels = Sparse.eval nodeValue4832 (mixedVector B) := by
  have h := singleton4832 B _hB
  rw [sound2052 B _hB _hF, sound2193 B _hB _hF] at h
  norm_num [nodeValue4832, nodeValue2052, nodeValue2193, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4833 node4833Labels = Sparse.eval nodeValue4833 (mixedVector B) := by
  simpa only [nodeValue4833, Sparse.eval_nil] using zero4833 B _hB _hF

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4836 node4836Labels = Sparse.eval nodeValue4836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4836) = mixedMoment B node4836 node4836Labels := rfl
  simpa [nodeValue4836, Sparse.eval] using hc.symm

theorem sound4837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4837 node4837Labels = Sparse.eval nodeValue4837 (mixedVector B) := by
  simpa only [nodeValue4837, Sparse.eval_nil] using zero4837 B _hB _hF

theorem sound4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = Sparse.eval nodeValue4838 (mixedVector B) := by
  simpa only [nodeValue4838, Sparse.eval_nil] using zero4838 B _hB _hF

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4840 node4840Labels = Sparse.eval nodeValue4840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4840) = mixedMoment B node4840 node4840Labels := rfl
  simpa [nodeValue4840, Sparse.eval] using hc.symm

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

theorem sound4842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4842 node4842Labels = Sparse.eval nodeValue4842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4842) = mixedMoment B node4842 node4842Labels := rfl
  simpa [nodeValue4842, Sparse.eval] using hc.symm

theorem sound4843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4843 node4843Labels = Sparse.eval nodeValue4843 (mixedVector B) := by
  have h := singleton4843 B _hB
  rw [sound2062 B _hB _hF, sound2230 B _hB _hF] at h
  norm_num [nodeValue4843, nodeValue2062, nodeValue2230, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4844 node4844Labels = Sparse.eval nodeValue4844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4844) = mixedMoment B node4844 node4844Labels := rfl
  simpa [nodeValue4844, Sparse.eval] using hc.symm

theorem sound4845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4845 node4845Labels = Sparse.eval nodeValue4845 (mixedVector B) := by
  have h := singleton4845 B _hB
  rw [sound2065 B _hB _hF, sound2218 B _hB _hF] at h
  norm_num [nodeValue4845, nodeValue2065, nodeValue2218, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = Sparse.eval nodeValue4846 (mixedVector B) := by
  simpa only [nodeValue4846, Sparse.eval_nil] using zero4846 B _hB _hF

theorem sound4847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4847 node4847Labels = Sparse.eval nodeValue4847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4847) = mixedMoment B node4847 node4847Labels := rfl
  simpa [nodeValue4847, Sparse.eval] using hc.symm

theorem sound4848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4848 node4848Labels = Sparse.eval nodeValue4848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4848) = mixedMoment B node4848 node4848Labels := rfl
  simpa [nodeValue4848, Sparse.eval] using hc.symm

theorem sound4849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4849 node4849Labels = Sparse.eval nodeValue4849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4849) = mixedMoment B node4849 node4849Labels := rfl
  simpa [nodeValue4849, Sparse.eval] using hc.symm

theorem sound4850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4850 node4850Labels = Sparse.eval nodeValue4850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4850) = mixedMoment B node4850 node4850Labels := rfl
  simpa [nodeValue4850, Sparse.eval] using hc.symm

theorem sound4851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4851 node4851Labels = Sparse.eval nodeValue4851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4851) = mixedMoment B node4851 node4851Labels := rfl
  simpa [nodeValue4851, Sparse.eval] using hc.symm

theorem sound4852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4852 node4852Labels = Sparse.eval nodeValue4852 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4852) = mixedMoment B node4852 node4852Labels := rfl
  simpa [nodeValue4852, Sparse.eval] using hc.symm

theorem sound4853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4853 node4853Labels = Sparse.eval nodeValue4853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4853) = mixedMoment B node4853 node4853Labels := rfl
  simpa [nodeValue4853, Sparse.eval] using hc.symm

theorem sound4854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4854 node4854Labels = Sparse.eval nodeValue4854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4854) = mixedMoment B node4854 node4854Labels := rfl
  simpa [nodeValue4854, Sparse.eval] using hc.symm

theorem sound4855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4855 node4855Labels = Sparse.eval nodeValue4855 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4855) = mixedMoment B node4855 node4855Labels := rfl
  simpa [nodeValue4855, Sparse.eval] using hc.symm

theorem sound4856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4856 node4856Labels = Sparse.eval nodeValue4856 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4856) = mixedMoment B node4856 node4856Labels := rfl
  simpa [nodeValue4856, Sparse.eval] using hc.symm

theorem sound4857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4857 node4857Labels = Sparse.eval nodeValue4857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4857) = mixedMoment B node4857 node4857Labels := rfl
  simpa [nodeValue4857, Sparse.eval] using hc.symm

theorem sound4858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4858 node4858Labels = Sparse.eval nodeValue4858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4858) = mixedMoment B node4858 node4858Labels := rfl
  simpa [nodeValue4858, Sparse.eval] using hc.symm

theorem sound4859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4859 node4859Labels = Sparse.eval nodeValue4859 (mixedVector B) := by
  have h := singleton4859 B _hB
  rw [sound2100 B _hB _hF] at h
  norm_num [nodeValue4859, nodeValue2100, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4860 node4860Labels = Sparse.eval nodeValue4860 (mixedVector B) := by
  have h := singleton4860 B _hB
  rw [sound2101 B _hB _hF] at h
  norm_num [nodeValue4860, nodeValue2101, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4861 node4861Labels = Sparse.eval nodeValue4861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4861) = mixedMoment B node4861 node4861Labels := rfl
  simpa [nodeValue4861, Sparse.eval] using hc.symm

theorem sound4862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4862 node4862Labels = Sparse.eval nodeValue4862 (mixedVector B) := by
  have h := singleton4862 B _hB
  rw [sound2103 B _hB _hF] at h
  norm_num [nodeValue4862, nodeValue2103, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4863 node4863Labels = Sparse.eval nodeValue4863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4863) = mixedMoment B node4863 node4863Labels := rfl
  simpa [nodeValue4863, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
