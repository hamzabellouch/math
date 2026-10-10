import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons74

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4736 node4736Labels = Sparse.eval nodeValue4736 (mixedVector B) := by
  simpa only [nodeValue4736, Sparse.eval_nil] using zero4736 B _hB _hF

theorem sound4737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4737 node4737Labels = Sparse.eval nodeValue4737 (mixedVector B) := by
  have h := singleton4737 B _hB
  rw [sound1909 B _hB _hF] at h
  norm_num [nodeValue4737, nodeValue1909, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4738 node4738Labels = Sparse.eval nodeValue4738 (mixedVector B) := by
  simpa only [nodeValue4738, Sparse.eval_nil] using zero4738 B _hB _hF

theorem sound4739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4739 node4739Labels = Sparse.eval nodeValue4739 (mixedVector B) := by
  simpa only [nodeValue4739, Sparse.eval_nil] using zero4739 B _hB _hF

theorem sound4740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4740 node4740Labels = Sparse.eval nodeValue4740 (mixedVector B) := by
  have h := singleton4740 B _hB
  rw [sound1913 B _hB _hF, sound1922 B _hB _hF] at h
  norm_num [nodeValue4740, nodeValue1913, nodeValue1922, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4741 node4741Labels = Sparse.eval nodeValue4741 (mixedVector B) := by
  simpa only [nodeValue4741, Sparse.eval_nil] using zero4741 B _hB _hF

theorem sound4742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4742 node4742Labels = Sparse.eval nodeValue4742 (mixedVector B) := by
  have h := singleton4742 B _hB
  rw [sound1915 B _hB _hF, sound1946 B _hB _hF] at h
  norm_num [nodeValue4742, nodeValue1915, nodeValue1946, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4743 node4743Labels = Sparse.eval nodeValue4743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4743) = mixedMoment B node4743 node4743Labels := rfl
  simpa [nodeValue4743, Sparse.eval] using hc.symm

theorem sound4744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4744 node4744Labels = Sparse.eval nodeValue4744 (mixedVector B) := by
  have h := singleton4744 B _hB
  rw [sound1917 B _hB _hF, sound1924 B _hB _hF] at h
  norm_num [nodeValue4744, nodeValue1917, nodeValue1924, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4745 node4745Labels = Sparse.eval nodeValue4745 (mixedVector B) := by
  simpa only [nodeValue4745, Sparse.eval_nil] using zero4745 B _hB _hF

theorem sound4746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4746 node4746Labels = Sparse.eval nodeValue4746 (mixedVector B) := by
  have h := singleton4746 B _hB
  rw [sound1925 B _hB _hF] at h
  norm_num [nodeValue4746, nodeValue1925, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4747 node4747Labels = Sparse.eval nodeValue4747 (mixedVector B) := by
  have h := singleton4747 B _hB
  rw [sound1926 B _hB _hF, sound1948 B _hB _hF] at h
  norm_num [nodeValue4747, nodeValue1926, nodeValue1948, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4748 node4748Labels = Sparse.eval nodeValue4748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4748) = mixedMoment B node4748 node4748Labels := rfl
  simpa [nodeValue4748, Sparse.eval] using hc.symm

theorem sound4749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4749 node4749Labels = Sparse.eval nodeValue4749 (mixedVector B) := by
  have h := singleton4749 B _hB
  rw [sound1928 B _hB _hF] at h
  norm_num [nodeValue4749, nodeValue1928, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4750 node4750Labels = Sparse.eval nodeValue4750 (mixedVector B) := by
  have h := singleton4750 B _hB
  rw [sound1929 B _hB _hF, sound1949 B _hB _hF] at h
  norm_num [nodeValue4750, nodeValue1929, nodeValue1949, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4751 node4751Labels = Sparse.eval nodeValue4751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4751) = mixedMoment B node4751 node4751Labels := rfl
  simpa [nodeValue4751, Sparse.eval] using hc.symm

theorem sound4752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4752 node4752Labels = Sparse.eval nodeValue4752 (mixedVector B) := by
  simpa only [nodeValue4752, Sparse.eval_nil] using zero4752 B _hB _hF

theorem sound4753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4753 node4753Labels = Sparse.eval nodeValue4753 (mixedVector B) := by
  simpa only [nodeValue4753, Sparse.eval_nil] using zero4753 B _hB _hF

theorem sound4754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4754 node4754Labels = Sparse.eval nodeValue4754 (mixedVector B) := by
  have h := singleton4754 B _hB
  rw [sound1951 B _hB _hF] at h
  norm_num [nodeValue4754, nodeValue1951, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4755 node4755Labels = Sparse.eval nodeValue4755 (mixedVector B) := by
  have h := singleton4755 B _hB
  rw [sound1954 B _hB _hF, sound1985 B _hB _hF] at h
  norm_num [nodeValue4755, nodeValue1954, nodeValue1985, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4756 node4756Labels = Sparse.eval nodeValue4756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4756) = mixedMoment B node4756 node4756Labels := rfl
  simpa [nodeValue4756, Sparse.eval] using hc.symm

theorem sound4757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4757 node4757Labels = Sparse.eval nodeValue4757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4757) = mixedMoment B node4757 node4757Labels := rfl
  simpa [nodeValue4757, Sparse.eval] using hc.symm

theorem sound4758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4758 node4758Labels = Sparse.eval nodeValue4758 (mixedVector B) := by
  have h := singleton4758 B _hB
  rw [sound1958 B _hB _hF, sound2069 B _hB _hF] at h
  norm_num [nodeValue4758, nodeValue1958, nodeValue2069, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4759 node4759Labels = Sparse.eval nodeValue4759 (mixedVector B) := by
  have h := singleton4759 B _hB
  rw [sound1959 B _hB _hF, sound2170 B _hB _hF] at h
  norm_num [nodeValue4759, nodeValue1959, nodeValue2170, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4760 node4760Labels = Sparse.eval nodeValue4760 (mixedVector B) := by
  have h := singleton4760 B _hB
  rw [sound1960 B _hB _hF, sound2173 B _hB _hF] at h
  norm_num [nodeValue4760, nodeValue1960, nodeValue2173, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4761 node4761Labels = Sparse.eval nodeValue4761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4761) = mixedMoment B node4761 node4761Labels := rfl
  simpa [nodeValue4761, Sparse.eval] using hc.symm

theorem sound4762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4762 node4762Labels = Sparse.eval nodeValue4762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4762) = mixedMoment B node4762 node4762Labels := rfl
  simpa [nodeValue4762, Sparse.eval] using hc.symm

theorem sound4763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4763 node4763Labels = Sparse.eval nodeValue4763 (mixedVector B) := by
  have h := singleton4763 B _hB
  rw [sound1963 B _hB _hF, sound2174 B _hB _hF] at h
  norm_num [nodeValue4763, nodeValue1963, nodeValue2174, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4764 node4764Labels = Sparse.eval nodeValue4764 (mixedVector B) := by
  have h := singleton4764 B _hB
  rw [sound1964 B _hB _hF, sound2182 B _hB _hF] at h
  norm_num [nodeValue4764, nodeValue1964, nodeValue2182, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4765 node4765Labels = Sparse.eval nodeValue4765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4765) = mixedMoment B node4765 node4765Labels := rfl
  simpa [nodeValue4765, Sparse.eval] using hc.symm

theorem sound4766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4766 node4766Labels = Sparse.eval nodeValue4766 (mixedVector B) := by
  have h := singleton4766 B _hB
  rw [sound1966 B _hB _hF, sound2177 B _hB _hF] at h
  norm_num [nodeValue4766, nodeValue1966, nodeValue2177, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4767 node4767Labels = Sparse.eval nodeValue4767 (mixedVector B) := by
  have h := singleton4767 B _hB
  rw [sound1967 B _hB _hF, sound2183 B _hB _hF] at h
  norm_num [nodeValue4767, nodeValue1967, nodeValue2183, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4768 node4768Labels = Sparse.eval nodeValue4768 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4768) = mixedMoment B node4768 node4768Labels := rfl
  simpa [nodeValue4768, Sparse.eval] using hc.symm

theorem sound4769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4769 node4769Labels = Sparse.eval nodeValue4769 (mixedVector B) := by
  have h := singleton4769 B _hB
  rw [sound1969 B _hB _hF, sound2185 B _hB _hF] at h
  norm_num [nodeValue4769, nodeValue1969, nodeValue2185, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4770 node4770Labels = Sparse.eval nodeValue4770 (mixedVector B) := by
  have h := singleton4770 B _hB
  rw [sound1970 B _hB _hF, sound2186 B _hB _hF] at h
  norm_num [nodeValue4770, nodeValue1970, nodeValue2186, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4771 node4771Labels = Sparse.eval nodeValue4771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4771) = mixedMoment B node4771 node4771Labels := rfl
  simpa [nodeValue4771, Sparse.eval] using hc.symm

theorem sound4772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4772 node4772Labels = Sparse.eval nodeValue4772 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4772) = mixedMoment B node4772 node4772Labels := rfl
  simpa [nodeValue4772, Sparse.eval] using hc.symm

theorem sound4773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4773 node4773Labels = Sparse.eval nodeValue4773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4773) = mixedMoment B node4773 node4773Labels := rfl
  simpa [nodeValue4773, Sparse.eval] using hc.symm

theorem sound4774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4774 node4774Labels = Sparse.eval nodeValue4774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4774) = mixedMoment B node4774 node4774Labels := rfl
  simpa [nodeValue4774, Sparse.eval] using hc.symm

theorem sound4775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4775 node4775Labels = Sparse.eval nodeValue4775 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4775) = mixedMoment B node4775 node4775Labels := rfl
  simpa [nodeValue4775, Sparse.eval] using hc.symm

theorem sound4776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4776 node4776Labels = Sparse.eval nodeValue4776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4776) = mixedMoment B node4776 node4776Labels := rfl
  simpa [nodeValue4776, Sparse.eval] using hc.symm

theorem sound4777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4777 node4777Labels = Sparse.eval nodeValue4777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4777) = mixedMoment B node4777 node4777Labels := rfl
  simpa [nodeValue4777, Sparse.eval] using hc.symm

theorem sound4778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4778 node4778Labels = Sparse.eval nodeValue4778 (mixedVector B) := by
  have h := singleton4778 B _hB
  rw [sound1986 B _hB _hF] at h
  norm_num [nodeValue4778, nodeValue1986, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4779 node4779Labels = Sparse.eval nodeValue4779 (mixedVector B) := by
  have h := singleton4779 B _hB
  rw [sound1987 B _hB _hF, sound1996 B _hB _hF] at h
  norm_num [nodeValue4779, nodeValue1987, nodeValue1996, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4780 node4780Labels = Sparse.eval nodeValue4780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4780) = mixedMoment B node4780 node4780Labels := rfl
  simpa [nodeValue4780, Sparse.eval] using hc.symm

theorem sound4781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4781 node4781Labels = Sparse.eval nodeValue4781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4781) = mixedMoment B node4781 node4781Labels := rfl
  simpa [nodeValue4781, Sparse.eval] using hc.symm

theorem sound4782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4782 node4782Labels = Sparse.eval nodeValue4782 (mixedVector B) := by
  have h := singleton4782 B _hB
  rw [sound1990 B _hB _hF, sound1997 B _hB _hF] at h
  norm_num [nodeValue4782, nodeValue1990, nodeValue1997, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4783 node4783Labels = Sparse.eval nodeValue4783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4783) = mixedMoment B node4783 node4783Labels := rfl
  simpa [nodeValue4783, Sparse.eval] using hc.symm

theorem sound4784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4784 node4784Labels = Sparse.eval nodeValue4784 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4784) = mixedMoment B node4784 node4784Labels := rfl
  simpa [nodeValue4784, Sparse.eval] using hc.symm

theorem sound4785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4785 node4785Labels = Sparse.eval nodeValue4785 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4785) = mixedMoment B node4785 node4785Labels := rfl
  simpa [nodeValue4785, Sparse.eval] using hc.symm

theorem sound4786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4786 node4786Labels = Sparse.eval nodeValue4786 (mixedVector B) := by
  simpa only [nodeValue4786, Sparse.eval_nil] using zero4786 B _hB _hF

theorem sound4787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4787 node4787Labels = Sparse.eval nodeValue4787 (mixedVector B) := by
  have h := singleton4787 B _hB
  rw [sound2000 B _hB _hF] at h
  norm_num [nodeValue4787, nodeValue2000, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4788 node4788Labels = Sparse.eval nodeValue4788 (mixedVector B) := by
  have h := singleton4788 B _hB
  rw [sound2003 B _hB _hF, sound2006 B _hB _hF] at h
  norm_num [nodeValue4788, nodeValue2003, nodeValue2006, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4789 node4789Labels = Sparse.eval nodeValue4789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4789) = mixedMoment B node4789 node4789Labels := rfl
  simpa [nodeValue4789, Sparse.eval] using hc.symm

theorem sound4790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4790 node4790Labels = Sparse.eval nodeValue4790 (mixedVector B) := by
  simpa only [nodeValue4790, Sparse.eval_nil] using zero4790 B _hB _hF

theorem sound4791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4791 node4791Labels = Sparse.eval nodeValue4791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4791) = mixedMoment B node4791 node4791Labels := rfl
  simpa [nodeValue4791, Sparse.eval] using hc.symm

theorem sound4792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4792 node4792Labels = Sparse.eval nodeValue4792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4792) = mixedMoment B node4792 node4792Labels := rfl
  simpa [nodeValue4792, Sparse.eval] using hc.symm

theorem sound4793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4793 node4793Labels = Sparse.eval nodeValue4793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4793) = mixedMoment B node4793 node4793Labels := rfl
  simpa [nodeValue4793, Sparse.eval] using hc.symm

theorem sound4794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4794 node4794Labels = Sparse.eval nodeValue4794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4794) = mixedMoment B node4794 node4794Labels := rfl
  simpa [nodeValue4794, Sparse.eval] using hc.symm

theorem sound4795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4795 node4795Labels = Sparse.eval nodeValue4795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4795) = mixedMoment B node4795 node4795Labels := rfl
  simpa [nodeValue4795, Sparse.eval] using hc.symm

theorem sound4796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4796 node4796Labels = Sparse.eval nodeValue4796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4796) = mixedMoment B node4796 node4796Labels := rfl
  simpa [nodeValue4796, Sparse.eval] using hc.symm

theorem sound4797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4797 node4797Labels = Sparse.eval nodeValue4797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4797) = mixedMoment B node4797 node4797Labels := rfl
  simpa [nodeValue4797, Sparse.eval] using hc.symm

theorem sound4798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4798 node4798Labels = Sparse.eval nodeValue4798 (mixedVector B) := by
  have h := singleton4798 B _hB
  rw [sound2016 B _hB _hF, sound2075 B _hB _hF] at h
  norm_num [nodeValue4798, nodeValue2016, nodeValue2075, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4799 node4799Labels = Sparse.eval nodeValue4799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4799) = mixedMoment B node4799 node4799Labels := rfl
  simpa [nodeValue4799, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
