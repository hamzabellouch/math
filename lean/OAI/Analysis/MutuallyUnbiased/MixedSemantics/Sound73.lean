import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons73

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4672 node4672Labels = Sparse.eval nodeValue4672 (mixedVector B) := by
  have h := singleton4672 B _hB
  rw [sound1798 B _hB _hF, sound2067 B _hB _hF] at h
  norm_num [nodeValue4672, nodeValue1798, nodeValue2067, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4673 node4673Labels = Sparse.eval nodeValue4673 (mixedVector B) := by
  have h := singleton4673 B _hB
  rw [sound1799 B _hB _hF, sound1920 B _hB _hF] at h
  norm_num [nodeValue4673, nodeValue1799, nodeValue1920, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4674 node4674Labels = Sparse.eval nodeValue4674 (mixedVector B) := by
  have h := singleton4674 B _hB
  rw [sound1800 B _hB _hF, sound2068 B _hB _hF] at h
  norm_num [nodeValue4674, nodeValue1800, nodeValue2068, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4675 node4675Labels = Sparse.eval nodeValue4675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4675) = mixedMoment B node4675 node4675Labels := rfl
  simpa [nodeValue4675, Sparse.eval] using hc.symm

theorem sound4676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4676 node4676Labels = Sparse.eval nodeValue4676 (mixedVector B) := by
  have h := singleton4676 B _hB
  rw [sound1802 B _hB _hF, sound2141 B _hB _hF] at h
  norm_num [nodeValue4676, nodeValue1802, nodeValue2141, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4677 node4677Labels = Sparse.eval nodeValue4677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4677) = mixedMoment B node4677 node4677Labels := rfl
  simpa [nodeValue4677, Sparse.eval] using hc.symm

theorem sound4678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4678 node4678Labels = Sparse.eval nodeValue4678 (mixedVector B) := by
  have h := singleton4678 B _hB
  rw [sound1804 B _hB _hF, sound2143 B _hB _hF] at h
  norm_num [nodeValue4678, nodeValue1804, nodeValue2143, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4679 node4679Labels = Sparse.eval nodeValue4679 (mixedVector B) := by
  have h := singleton4679 B _hB
  rw [sound1805 B _hB _hF, sound2150 B _hB _hF] at h
  norm_num [nodeValue4679, nodeValue1805, nodeValue2150, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4680 node4680Labels = Sparse.eval nodeValue4680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4680) = mixedMoment B node4680 node4680Labels := rfl
  simpa [nodeValue4680, Sparse.eval] using hc.symm

theorem sound4681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4681 node4681Labels = Sparse.eval nodeValue4681 (mixedVector B) := by
  have h := singleton4681 B _hB
  rw [sound1807 B _hB _hF, sound2151 B _hB _hF] at h
  norm_num [nodeValue4681, nodeValue1807, nodeValue2151, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4682 node4682Labels = Sparse.eval nodeValue4682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4682) = mixedMoment B node4682 node4682Labels := rfl
  simpa [nodeValue4682, Sparse.eval] using hc.symm

theorem sound4683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4683 node4683Labels = Sparse.eval nodeValue4683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4683) = mixedMoment B node4683 node4683Labels := rfl
  simpa [nodeValue4683, Sparse.eval] using hc.symm

theorem sound4684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4684 node4684Labels = Sparse.eval nodeValue4684 (mixedVector B) := by
  have h := singleton4684 B _hB
  rw [sound1810 B _hB _hF, sound2152 B _hB _hF] at h
  norm_num [nodeValue4684, nodeValue1810, nodeValue2152, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4685 node4685Labels = Sparse.eval nodeValue4685 (mixedVector B) := by
  have h := singleton4685 B _hB
  rw [sound1811 B _hB _hF, sound2156 B _hB _hF] at h
  norm_num [nodeValue4685, nodeValue1811, nodeValue2156, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4686 node4686Labels = Sparse.eval nodeValue4686 (mixedVector B) := by
  have h := singleton4686 B _hB
  rw [sound1812 B _hB _hF, sound2165 B _hB _hF] at h
  norm_num [nodeValue4686, nodeValue1812, nodeValue2165, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4687 node4687Labels = Sparse.eval nodeValue4687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4687) = mixedMoment B node4687 node4687Labels := rfl
  simpa [nodeValue4687, Sparse.eval] using hc.symm

theorem sound4688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4688 node4688Labels = Sparse.eval nodeValue4688 (mixedVector B) := by
  have h := singleton4688 B _hB
  rw [sound1814 B _hB _hF, sound2157 B _hB _hF] at h
  norm_num [nodeValue4688, nodeValue1814, nodeValue2157, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4689 node4689Labels = Sparse.eval nodeValue4689 (mixedVector B) := by
  have h := singleton4689 B _hB
  rw [sound1815 B _hB _hF, sound2166 B _hB _hF] at h
  norm_num [nodeValue4689, nodeValue1815, nodeValue2166, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4690 node4690Labels = Sparse.eval nodeValue4690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4690) = mixedMoment B node4690 node4690Labels := rfl
  simpa [nodeValue4690, Sparse.eval] using hc.symm

theorem sound4691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4691 node4691Labels = Sparse.eval nodeValue4691 (mixedVector B) := by
  have h := singleton4691 B _hB
  rw [sound1817 B _hB _hF, sound2159 B _hB _hF] at h
  norm_num [nodeValue4691, nodeValue1817, nodeValue2159, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4692 node4692Labels = Sparse.eval nodeValue4692 (mixedVector B) := by
  have h := singleton4692 B _hB
  rw [sound1818 B _hB _hF, sound2168 B _hB _hF] at h
  norm_num [nodeValue4692, nodeValue1818, nodeValue2168, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4693 node4693Labels = Sparse.eval nodeValue4693 (mixedVector B) := by
  have h := singleton4693 B _hB
  rw [sound1819 B _hB _hF, sound2169 B _hB _hF] at h
  norm_num [nodeValue4693, nodeValue1819, nodeValue2169, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4694 node4694Labels = Sparse.eval nodeValue4694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4694) = mixedMoment B node4694 node4694Labels := rfl
  simpa [nodeValue4694, Sparse.eval] using hc.symm

theorem sound4695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4695 node4695Labels = Sparse.eval nodeValue4695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4695) = mixedMoment B node4695 node4695Labels := rfl
  simpa [nodeValue4695, Sparse.eval] using hc.symm

theorem sound4696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4696 node4696Labels = Sparse.eval nodeValue4696 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4696) = mixedMoment B node4696 node4696Labels := rfl
  simpa [nodeValue4696, Sparse.eval] using hc.symm

theorem sound4697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4697 node4697Labels = Sparse.eval nodeValue4697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4697) = mixedMoment B node4697 node4697Labels := rfl
  simpa [nodeValue4697, Sparse.eval] using hc.symm

theorem sound4698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4698 node4698Labels = Sparse.eval nodeValue4698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4698) = mixedMoment B node4698 node4698Labels := rfl
  simpa [nodeValue4698, Sparse.eval] using hc.symm

theorem sound4699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4699 node4699Labels = Sparse.eval nodeValue4699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4699) = mixedMoment B node4699 node4699Labels := rfl
  simpa [nodeValue4699, Sparse.eval] using hc.symm

theorem sound4700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4700 node4700Labels = Sparse.eval nodeValue4700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4700) = mixedMoment B node4700 node4700Labels := rfl
  simpa [nodeValue4700, Sparse.eval] using hc.symm

theorem sound4701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4701 node4701Labels = Sparse.eval nodeValue4701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4701) = mixedMoment B node4701 node4701Labels := rfl
  simpa [nodeValue4701, Sparse.eval] using hc.symm

theorem sound4702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4702 node4702Labels = Sparse.eval nodeValue4702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4702) = mixedMoment B node4702 node4702Labels := rfl
  simpa [nodeValue4702, Sparse.eval] using hc.symm

theorem sound4703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4703 node4703Labels = Sparse.eval nodeValue4703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4703) = mixedMoment B node4703 node4703Labels := rfl
  simpa [nodeValue4703, Sparse.eval] using hc.symm

theorem sound4704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4704 node4704Labels = Sparse.eval nodeValue4704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4704) = mixedMoment B node4704 node4704Labels := rfl
  simpa [nodeValue4704, Sparse.eval] using hc.symm

theorem sound4705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4705 node4705Labels = Sparse.eval nodeValue4705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4705) = mixedMoment B node4705 node4705Labels := rfl
  simpa [nodeValue4705, Sparse.eval] using hc.symm

theorem sound4706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4706 node4706Labels = Sparse.eval nodeValue4706 (mixedVector B) := by
  have h := singleton4706 B _hB
  rw [sound1860 B _hB _hF, sound1888 B _hB _hF] at h
  norm_num [nodeValue4706, nodeValue1860, nodeValue1888, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4707 node4707Labels = Sparse.eval nodeValue4707 (mixedVector B) := by
  have h := singleton4707 B _hB
  rw [sound1861 B _hB _hF, sound1889 B _hB _hF] at h
  norm_num [nodeValue4707, nodeValue1861, nodeValue1889, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4708 node4708Labels = Sparse.eval nodeValue4708 (mixedVector B) := by
  simpa only [nodeValue4708, Sparse.eval_nil] using zero4708 B _hB _hF

theorem sound4709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4709 node4709Labels = Sparse.eval nodeValue4709 (mixedVector B) := by
  have h := singleton4709 B _hB
  rw [sound1863 B _hB _hF, sound1883 B _hB _hF] at h
  norm_num [nodeValue4709, nodeValue1863, nodeValue1883, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4710 node4710Labels = Sparse.eval nodeValue4710 (mixedVector B) := by
  have h := singleton4710 B _hB
  rw [sound1864 B _hB _hF, sound1882 B _hB _hF] at h
  norm_num [nodeValue4710, nodeValue1864, nodeValue1882, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4711 node4711Labels = Sparse.eval nodeValue4711 (mixedVector B) := by
  simpa only [nodeValue4711, Sparse.eval_nil] using zero4711 B _hB _hF

theorem sound4712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4712 node4712Labels = Sparse.eval nodeValue4712 (mixedVector B) := by
  simpa only [nodeValue4712, Sparse.eval_nil] using zero4712 B _hB _hF

theorem sound4713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4713 node4713Labels = Sparse.eval nodeValue4713 (mixedVector B) := by
  have h := singleton4713 B _hB
  rw [sound1867 B _hB _hF, sound1891 B _hB _hF] at h
  norm_num [nodeValue4713, nodeValue1867, nodeValue1891, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4714 node4714Labels = Sparse.eval nodeValue4714 (mixedVector B) := by
  have h := singleton4714 B _hB
  rw [sound1868 B _hB _hF, sound1885 B _hB _hF] at h
  norm_num [nodeValue4714, nodeValue1868, nodeValue1885, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4715 node4715Labels = Sparse.eval nodeValue4715 (mixedVector B) := by
  simpa only [nodeValue4715, Sparse.eval_nil] using zero4715 B _hB _hF

theorem sound4716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4716 node4716Labels = Sparse.eval nodeValue4716 (mixedVector B) := by
  have h := singleton4716 B _hB
  rw [sound1870 B _hB _hF, sound1886 B _hB _hF] at h
  norm_num [nodeValue4716, nodeValue1870, nodeValue1886, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4717 node4717Labels = Sparse.eval nodeValue4717 (mixedVector B) := by
  have h := singleton4717 B _hB
  rw [sound1871 B _hB _hF, sound1892 B _hB _hF] at h
  norm_num [nodeValue4717, nodeValue1871, nodeValue1892, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4718 node4718Labels = Sparse.eval nodeValue4718 (mixedVector B) := by
  simpa only [nodeValue4718, Sparse.eval_nil] using zero4718 B _hB _hF

theorem sound4719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4719 node4719Labels = Sparse.eval nodeValue4719 (mixedVector B) := by
  have h := singleton4719 B _hB
  rw [sound1873 B _hB _hF, sound1893 B _hB _hF] at h
  norm_num [nodeValue4719, nodeValue1873, nodeValue1893, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4720 node4720Labels = Sparse.eval nodeValue4720 (mixedVector B) := by
  have h := singleton4720 B _hB
  rw [sound1874 B _hB _hF, sound1896 B _hB _hF] at h
  norm_num [nodeValue4720, nodeValue1874, nodeValue1896, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4721 node4721Labels = Sparse.eval nodeValue4721 (mixedVector B) := by
  have h := singleton4721 B _hB
  rw [sound1875 B _hB _hF, sound1905 B _hB _hF] at h
  norm_num [nodeValue4721, nodeValue1875, nodeValue1905, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4722 node4722Labels = Sparse.eval nodeValue4722 (mixedVector B) := by
  have h := singleton4722 B _hB
  rw [sound1876 B _hB _hF, sound1906 B _hB _hF] at h
  norm_num [nodeValue4722, nodeValue1876, nodeValue1906, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4723 node4723Labels = Sparse.eval nodeValue4723 (mixedVector B) := by
  have h := singleton4723 B _hB
  rw [sound1877 B _hB _hF, sound1935 B _hB _hF] at h
  norm_num [nodeValue4723, nodeValue1877, nodeValue1935, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4724 node4724Labels = Sparse.eval nodeValue4724 (mixedVector B) := by
  have h := singleton4724 B _hB
  rw [sound1878 B _hB _hF, sound1919 B _hB _hF] at h
  norm_num [nodeValue4724, nodeValue1878, nodeValue1919, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4725 node4725Labels = Sparse.eval nodeValue4725 (mixedVector B) := by
  have h := singleton4725 B _hB
  rw [sound1879 B _hB _hF, sound1936 B _hB _hF] at h
  norm_num [nodeValue4725, nodeValue1879, nodeValue1936, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4726 node4726Labels = Sparse.eval nodeValue4726 (mixedVector B) := by
  have h := singleton4726 B _hB
  rw [sound1880 B _hB _hF, sound1938 B _hB _hF] at h
  norm_num [nodeValue4726, nodeValue1880, nodeValue1938, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4727 node4727Labels = Sparse.eval nodeValue4727 (mixedVector B) := by
  have h := singleton4727 B _hB
  rw [sound1881 B _hB _hF, sound1939 B _hB _hF] at h
  norm_num [nodeValue4727, nodeValue1881, nodeValue1939, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4728 node4728Labels = Sparse.eval nodeValue4728 (mixedVector B) := by
  have h := singleton4728 B _hB
  rw [sound1897 B _hB _hF, sound1907 B _hB _hF] at h
  norm_num [nodeValue4728, nodeValue1897, nodeValue1907, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4729 node4729Labels = Sparse.eval nodeValue4729 (mixedVector B) := by
  have h := singleton4729 B _hB
  rw [sound1898 B _hB _hF, sound1940 B _hB _hF] at h
  norm_num [nodeValue4729, nodeValue1898, nodeValue1940, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4730 node4730Labels = Sparse.eval nodeValue4730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4730) = mixedMoment B node4730 node4730Labels := rfl
  simpa [nodeValue4730, Sparse.eval] using hc.symm

theorem sound4731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4731 node4731Labels = Sparse.eval nodeValue4731 (mixedVector B) := by
  have h := singleton4731 B _hB
  rw [sound1900 B _hB _hF, sound1921 B _hB _hF] at h
  norm_num [nodeValue4731, nodeValue1900, nodeValue1921, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4732 node4732Labels = Sparse.eval nodeValue4732 (mixedVector B) := by
  have h := singleton4732 B _hB
  rw [sound1901 B _hB _hF, sound1941 B _hB _hF] at h
  norm_num [nodeValue4732, nodeValue1901, nodeValue1941, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4733 node4733Labels = Sparse.eval nodeValue4733 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4733) = mixedMoment B node4733 node4733Labels := rfl
  simpa [nodeValue4733, Sparse.eval] using hc.symm

theorem sound4734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4734 node4734Labels = Sparse.eval nodeValue4734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4734) = mixedMoment B node4734 node4734Labels := rfl
  simpa [nodeValue4734, Sparse.eval] using hc.symm

theorem sound4735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4735 node4735Labels = Sparse.eval nodeValue4735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4735) = mixedMoment B node4735 node4735Labels := rfl
  simpa [nodeValue4735, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
