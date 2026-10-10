import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4608 node4608Labels = Sparse.eval nodeValue4608 (mixedVector B) := by
  have h := singleton4608 B _hB
  rw [sound1242 B _hB _hF, sound3300 B _hB _hF] at h
  norm_num [nodeValue4608, nodeValue1242, nodeValue3300, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4609 node4609Labels = Sparse.eval nodeValue4609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4609) = mixedMoment B node4609 node4609Labels := rfl
  simpa [nodeValue4609, Sparse.eval] using hc.symm

theorem sound4610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4610 node4610Labels = Sparse.eval nodeValue4610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4610) = mixedMoment B node4610 node4610Labels := rfl
  simpa [nodeValue4610, Sparse.eval] using hc.symm

theorem sound4611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4611 node4611Labels = Sparse.eval nodeValue4611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4611) = mixedMoment B node4611 node4611Labels := rfl
  simpa [nodeValue4611, Sparse.eval] using hc.symm

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4613 node4613Labels = Sparse.eval nodeValue4613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4613) = mixedMoment B node4613 node4613Labels := rfl
  simpa [nodeValue4613, Sparse.eval] using hc.symm

theorem sound4614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4614 node4614Labels = Sparse.eval nodeValue4614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4614) = mixedMoment B node4614 node4614Labels := rfl
  simpa [nodeValue4614, Sparse.eval] using hc.symm

theorem sound4615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4615 node4615Labels = Sparse.eval nodeValue4615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4615) = mixedMoment B node4615 node4615Labels := rfl
  simpa [nodeValue4615, Sparse.eval] using hc.symm

theorem sound4616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4616 node4616Labels = Sparse.eval nodeValue4616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4616) = mixedMoment B node4616 node4616Labels := rfl
  simpa [nodeValue4616, Sparse.eval] using hc.symm

theorem sound4617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4617 node4617Labels = Sparse.eval nodeValue4617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4617) = mixedMoment B node4617 node4617Labels := rfl
  simpa [nodeValue4617, Sparse.eval] using hc.symm

theorem sound4618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4618 node4618Labels = Sparse.eval nodeValue4618 (mixedVector B) := by
  have h := singleton4618 B _hB
  rw [sound1293 B _hB _hF, sound3304 B _hB _hF] at h
  norm_num [nodeValue4618, nodeValue1293, nodeValue3304, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4619 node4619Labels = Sparse.eval nodeValue4619 (mixedVector B) := by
  have h := singleton4619 B _hB
  rw [sound1294 B _hB _hF, sound3305 B _hB _hF] at h
  norm_num [nodeValue4619, nodeValue1294, nodeValue3305, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4620 node4620Labels = Sparse.eval nodeValue4620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4620) = mixedMoment B node4620 node4620Labels := rfl
  simpa [nodeValue4620, Sparse.eval] using hc.symm

theorem sound4621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4621 node4621Labels = Sparse.eval nodeValue4621 (mixedVector B) := by
  have h := singleton4621 B _hB
  rw [sound1297 B _hB _hF, sound2289 B _hB _hF] at h
  norm_num [nodeValue4621, nodeValue1297, nodeValue2289, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4622 node4622Labels = Sparse.eval nodeValue4622 (mixedVector B) := by
  have h := singleton4622 B _hB
  rw [sound1299 B _hB _hF, sound3307 B _hB _hF] at h
  norm_num [nodeValue4622, nodeValue1299, nodeValue3307, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4623 node4623Labels = Sparse.eval nodeValue4623 (mixedVector B) := by
  have h := singleton4623 B _hB
  rw [sound1300 B _hB _hF, sound3308 B _hB _hF] at h
  norm_num [nodeValue4623, nodeValue1300, nodeValue3308, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4624 node4624Labels = Sparse.eval nodeValue4624 (mixedVector B) := by
  have h := singleton4624 B _hB
  rw [sound1301 B _hB _hF, sound3309 B _hB _hF] at h
  norm_num [nodeValue4624, nodeValue1301, nodeValue3309, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4625 node4625Labels = Sparse.eval nodeValue4625 (mixedVector B) := by
  have h := singleton4625 B _hB
  rw [sound1304 B _hB _hF, sound3310 B _hB _hF] at h
  norm_num [nodeValue4625, nodeValue1304, nodeValue3310, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4626 node4626Labels = Sparse.eval nodeValue4626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4626) = mixedMoment B node4626 node4626Labels := rfl
  simpa [nodeValue4626, Sparse.eval] using hc.symm

theorem sound4627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4627 node4627Labels = Sparse.eval nodeValue4627 (mixedVector B) := by
  have h := singleton4627 B _hB
  rw [sound1311 B _hB _hF, sound3311 B _hB _hF] at h
  norm_num [nodeValue4627, nodeValue1311, nodeValue3311, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4628 node4628Labels = Sparse.eval nodeValue4628 (mixedVector B) := by
  have h := singleton4628 B _hB
  rw [sound1312 B _hB _hF, sound3312 B _hB _hF] at h
  norm_num [nodeValue4628, nodeValue1312, nodeValue3312, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4629 node4629Labels = Sparse.eval nodeValue4629 (mixedVector B) := by
  have h := singleton4629 B _hB
  rw [sound1313 B _hB _hF, sound3313 B _hB _hF] at h
  norm_num [nodeValue4629, nodeValue1313, nodeValue3313, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4630 node4630Labels = Sparse.eval nodeValue4630 (mixedVector B) := by
  have h := singleton4630 B _hB
  rw [sound1759 B _hB _hF, sound1833 B _hB _hF] at h
  norm_num [nodeValue4630, nodeValue1759, nodeValue1833, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4631 node4631Labels = Sparse.eval nodeValue4631 (mixedVector B) := by
  have h := singleton4631 B _hB
  rw [sound1760 B _hB _hF, sound1836 B _hB _hF] at h
  norm_num [nodeValue4631, nodeValue1760, nodeValue1836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4632 node4632Labels = Sparse.eval nodeValue4632 (mixedVector B) := by
  have h := singleton4632 B _hB
  rw [sound1761 B _hB _hF, sound1837 B _hB _hF] at h
  norm_num [nodeValue4632, nodeValue1761, nodeValue1837, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4633 node4633Labels = Sparse.eval nodeValue4633 (mixedVector B) := by
  have h := singleton4633 B _hB
  rw [sound1762 B _hB _hF, sound1847 B _hB _hF] at h
  norm_num [nodeValue4633, nodeValue1762, nodeValue1847, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4634 node4634Labels = Sparse.eval nodeValue4634 (mixedVector B) := by
  have h := singleton4634 B _hB
  rw [sound1763 B _hB _hF, sound1842 B _hB _hF] at h
  norm_num [nodeValue4634, nodeValue1763, nodeValue1842, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4635 node4635Labels = Sparse.eval nodeValue4635 (mixedVector B) := by
  have h := singleton4635 B _hB
  rw [sound1764 B _hB _hF, sound1848 B _hB _hF] at h
  norm_num [nodeValue4635, nodeValue1764, nodeValue1848, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4636 node4636Labels = Sparse.eval nodeValue4636 (mixedVector B) := by
  have h := singleton4636 B _hB
  rw [sound1765 B _hB _hF, sound1843 B _hB _hF] at h
  norm_num [nodeValue4636, nodeValue1765, nodeValue1843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4637 node4637Labels = Sparse.eval nodeValue4637 (mixedVector B) := by
  have h := singleton4637 B _hB
  rw [sound1766 B _hB _hF, sound1850 B _hB _hF] at h
  norm_num [nodeValue4637, nodeValue1766, nodeValue1850, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4638 node4638Labels = Sparse.eval nodeValue4638 (mixedVector B) := by
  have h := singleton4638 B _hB
  rw [sound1767 B _hB _hF, sound1851 B _hB _hF] at h
  norm_num [nodeValue4638, nodeValue1767, nodeValue1851, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4639 node4639Labels = Sparse.eval nodeValue4639 (mixedVector B) := by
  have h := singleton4639 B _hB
  rw [sound1768 B _hB _hF, sound1834 B _hB _hF] at h
  norm_num [nodeValue4639, nodeValue1768, nodeValue1834, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4640 node4640Labels = Sparse.eval nodeValue4640 (mixedVector B) := by
  have h := singleton4640 B _hB
  rw [sound1769 B _hB _hF, sound1835 B _hB _hF] at h
  norm_num [nodeValue4640, nodeValue1769, nodeValue1835, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4641 node4641Labels = Sparse.eval nodeValue4641 (mixedVector B) := by
  simpa only [nodeValue4641, Sparse.eval_nil] using zero4641 B _hB _hF

theorem sound4642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4642 node4642Labels = Sparse.eval nodeValue4642 (mixedVector B) := by
  have h := singleton4642 B _hB
  rw [sound1771 B _hB _hF, sound1838 B _hB _hF] at h
  norm_num [nodeValue4642, nodeValue1771, nodeValue1838, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4643 node4643Labels = Sparse.eval nodeValue4643 (mixedVector B) := by
  simpa only [nodeValue4643, Sparse.eval_nil] using zero4643 B _hB _hF

theorem sound4644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4644 node4644Labels = Sparse.eval nodeValue4644 (mixedVector B) := by
  have h := singleton4644 B _hB
  rw [sound1773 B _hB _hF, sound1841 B _hB _hF] at h
  norm_num [nodeValue4644, nodeValue1773, nodeValue1841, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4645 node4645Labels = Sparse.eval nodeValue4645 (mixedVector B) := by
  have h := singleton4645 B _hB
  rw [sound1774 B _hB _hF, sound1840 B _hB _hF] at h
  norm_num [nodeValue4645, nodeValue1774, nodeValue1840, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4646 node4646Labels = Sparse.eval nodeValue4646 (mixedVector B) := by
  simpa only [nodeValue4646, Sparse.eval_nil] using zero4646 B _hB _hF

theorem sound4647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4647 node4647Labels = Sparse.eval nodeValue4647 (mixedVector B) := by
  simpa only [nodeValue4647, Sparse.eval_nil] using zero4647 B _hB _hF

theorem sound4648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4648 node4648Labels = Sparse.eval nodeValue4648 (mixedVector B) := by
  have h := singleton4648 B _hB
  rw [sound1776 B _hB _hF, sound1844 B _hB _hF] at h
  norm_num [nodeValue4648, nodeValue1776, nodeValue1844, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4649 node4649Labels = Sparse.eval nodeValue4649 (mixedVector B) := by
  simpa only [nodeValue4649, Sparse.eval_nil] using zero4649 B _hB _hF

theorem sound4650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4650 node4650Labels = Sparse.eval nodeValue4650 (mixedVector B) := by
  have h := singleton4650 B _hB
  rw [sound1778 B _hB _hF, sound1854 B _hB _hF] at h
  norm_num [nodeValue4650, nodeValue1778, nodeValue1854, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4651 node4651Labels = Sparse.eval nodeValue4651 (mixedVector B) := by
  have h := singleton4651 B _hB
  rw [sound1779 B _hB _hF, sound1845 B _hB _hF] at h
  norm_num [nodeValue4651, nodeValue1779, nodeValue1845, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4652 node4652Labels = Sparse.eval nodeValue4652 (mixedVector B) := by
  simpa only [nodeValue4652, Sparse.eval_nil] using zero4652 B _hB _hF

theorem sound4653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4653 node4653Labels = Sparse.eval nodeValue4653 (mixedVector B) := by
  have h := singleton4653 B _hB
  rw [sound1781 B _hB _hF, sound1846 B _hB _hF] at h
  norm_num [nodeValue4653, nodeValue1781, nodeValue1846, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4654 node4654Labels = Sparse.eval nodeValue4654 (mixedVector B) := by
  have h := singleton4654 B _hB
  rw [sound1782 B _hB _hF, sound1855 B _hB _hF] at h
  norm_num [nodeValue4654, nodeValue1782, nodeValue1855, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4655 node4655Labels = Sparse.eval nodeValue4655 (mixedVector B) := by
  simpa only [nodeValue4655, Sparse.eval_nil] using zero4655 B _hB _hF

theorem sound4656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4656 node4656Labels = Sparse.eval nodeValue4656 (mixedVector B) := by
  simpa only [nodeValue4656, Sparse.eval_nil] using zero4656 B _hB _hF

theorem sound4657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4657 node4657Labels = Sparse.eval nodeValue4657 (mixedVector B) := by
  have h := singleton4657 B _hB
  rw [sound1783 B _hB _hF, sound1857 B _hB _hF] at h
  norm_num [nodeValue4657, nodeValue1783, nodeValue1857, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4658 node4658Labels = Sparse.eval nodeValue4658 (mixedVector B) := by
  have h := singleton4658 B _hB
  rw [sound1784 B _hB _hF, sound1884 B _hB _hF] at h
  norm_num [nodeValue4658, nodeValue1784, nodeValue1884, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4659 node4659Labels = Sparse.eval nodeValue4659 (mixedVector B) := by
  have h := singleton4659 B _hB
  rw [sound1785 B _hB _hF, sound1981 B _hB _hF] at h
  norm_num [nodeValue4659, nodeValue1785, nodeValue1981, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4660 node4660Labels = Sparse.eval nodeValue4660 (mixedVector B) := by
  have h := singleton4660 B _hB
  rw [sound1786 B _hB _hF, sound1982 B _hB _hF] at h
  norm_num [nodeValue4660, nodeValue1786, nodeValue1982, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4661 node4661Labels = Sparse.eval nodeValue4661 (mixedVector B) := by
  have h := singleton4661 B _hB
  rw [sound1787 B _hB _hF, sound1983 B _hB _hF] at h
  norm_num [nodeValue4661, nodeValue1787, nodeValue1983, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4662 node4662Labels = Sparse.eval nodeValue4662 (mixedVector B) := by
  have h := singleton4662 B _hB
  rw [sound1788 B _hB _hF, sound1984 B _hB _hF] at h
  norm_num [nodeValue4662, nodeValue1788, nodeValue1984, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4663 node4663Labels = Sparse.eval nodeValue4663 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4663) = mixedMoment B node4663 node4663Labels := rfl
  simpa [nodeValue4663, Sparse.eval] using hc.symm

theorem sound4664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4664 node4664Labels = Sparse.eval nodeValue4664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4664) = mixedMoment B node4664 node4664Labels := rfl
  simpa [nodeValue4664, Sparse.eval] using hc.symm

theorem sound4665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4665 node4665Labels = Sparse.eval nodeValue4665 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4665) = mixedMoment B node4665 node4665Labels := rfl
  simpa [nodeValue4665, Sparse.eval] using hc.symm

theorem sound4666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4666 node4666Labels = Sparse.eval nodeValue4666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4666) = mixedMoment B node4666 node4666Labels := rfl
  simpa [nodeValue4666, Sparse.eval] using hc.symm

theorem sound4667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4667 node4667Labels = Sparse.eval nodeValue4667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4667) = mixedMoment B node4667 node4667Labels := rfl
  simpa [nodeValue4667, Sparse.eval] using hc.symm

theorem sound4668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4668 node4668Labels = Sparse.eval nodeValue4668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4668) = mixedMoment B node4668 node4668Labels := rfl
  simpa [nodeValue4668, Sparse.eval] using hc.symm

theorem sound4669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4669 node4669Labels = Sparse.eval nodeValue4669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4669) = mixedMoment B node4669 node4669Labels := rfl
  simpa [nodeValue4669, Sparse.eval] using hc.symm

theorem sound4670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4670 node4670Labels = Sparse.eval nodeValue4670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4670) = mixedMoment B node4670 node4670Labels := rfl
  simpa [nodeValue4670, Sparse.eval] using hc.symm

theorem sound4671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4671 node4671Labels = Sparse.eval nodeValue4671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4671) = mixedMoment B node4671 node4671Labels := rfl
  simpa [nodeValue4671, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
