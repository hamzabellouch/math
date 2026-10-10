import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons43

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2752 node2752Labels = Sparse.eval nodeValue2752 (mixedVector B) := by
  simpa only [nodeValue2752, Sparse.eval_nil] using zero2752 B _hB _hF

theorem sound2753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2753 node2753Labels = Sparse.eval nodeValue2753 (mixedVector B) := by
  have h := singleton2753 B _hB
  rw [sound397 B _hB _hF] at h
  norm_num [nodeValue2753, nodeValue397, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2754 node2754Labels = Sparse.eval nodeValue2754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2754) = mixedMoment B node2754 node2754Labels := rfl
  simpa [nodeValue2754, Sparse.eval] using hc.symm

theorem sound2755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2755 node2755Labels = Sparse.eval nodeValue2755 (mixedVector B) := by
  have h := singleton2755 B _hB
  rw [sound262 B _hB _hF] at h
  norm_num [nodeValue2755, nodeValue262, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2756 node2756Labels = Sparse.eval nodeValue2756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2756) = mixedMoment B node2756 node2756Labels := rfl
  simpa [nodeValue2756, Sparse.eval] using hc.symm

theorem sound2757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2757 node2757Labels = Sparse.eval nodeValue2757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2757) = mixedMoment B node2757 node2757Labels := rfl
  simpa [nodeValue2757, Sparse.eval] using hc.symm

theorem sound2758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2758 node2758Labels = Sparse.eval nodeValue2758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2758) = mixedMoment B node2758 node2758Labels := rfl
  simpa [nodeValue2758, Sparse.eval] using hc.symm

theorem sound2759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2759 node2759Labels = Sparse.eval nodeValue2759 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2759) = mixedMoment B node2759 node2759Labels := rfl
  simpa [nodeValue2759, Sparse.eval] using hc.symm

theorem sound2760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2760 node2760Labels = Sparse.eval nodeValue2760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2760) = mixedMoment B node2760 node2760Labels := rfl
  simpa [nodeValue2760, Sparse.eval] using hc.symm

theorem sound2761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2761 node2761Labels = Sparse.eval nodeValue2761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2761) = mixedMoment B node2761 node2761Labels := rfl
  simpa [nodeValue2761, Sparse.eval] using hc.symm

theorem sound2762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2762 node2762Labels = Sparse.eval nodeValue2762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2762) = mixedMoment B node2762 node2762Labels := rfl
  simpa [nodeValue2762, Sparse.eval] using hc.symm

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

theorem sound2766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2766 node2766Labels = Sparse.eval nodeValue2766 (mixedVector B) := by
  have h := singleton2766 B _hB
  rw [sound403 B _hB _hF] at h
  norm_num [nodeValue2766, nodeValue403, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2767 node2767Labels = Sparse.eval nodeValue2767 (mixedVector B) := by
  have h := singleton2767 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue2767, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2768 node2768Labels = Sparse.eval nodeValue2768 (mixedVector B) := by
  have h := singleton2768 B _hB
  rw [sound405 B _hB _hF] at h
  norm_num [nodeValue2768, nodeValue405, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2769 node2769Labels = Sparse.eval nodeValue2769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2769) = mixedMoment B node2769 node2769Labels := rfl
  simpa [nodeValue2769, Sparse.eval] using hc.symm

theorem sound2770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2770 node2770Labels = Sparse.eval nodeValue2770 (mixedVector B) := by
  have h := singleton2770 B _hB
  rw [sound407 B _hB _hF] at h
  norm_num [nodeValue2770, nodeValue407, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2771 node2771Labels = Sparse.eval nodeValue2771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2771) = mixedMoment B node2771 node2771Labels := rfl
  simpa [nodeValue2771, Sparse.eval] using hc.symm

theorem sound2772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2772 node2772Labels = Sparse.eval nodeValue2772 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2772) = mixedMoment B node2772 node2772Labels := rfl
  simpa [nodeValue2772, Sparse.eval] using hc.symm

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

theorem sound2774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2774 node2774Labels = Sparse.eval nodeValue2774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2774) = mixedMoment B node2774 node2774Labels := rfl
  simpa [nodeValue2774, Sparse.eval] using hc.symm

theorem sound2775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2775 node2775Labels = Sparse.eval nodeValue2775 (mixedVector B) := by
  have h := singleton2775 B _hB
  rw [sound411 B _hB _hF] at h
  norm_num [nodeValue2775, nodeValue411, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2776 node2776Labels = Sparse.eval nodeValue2776 (mixedVector B) := by
  have h := singleton2776 B _hB
  rw [sound412 B _hB _hF] at h
  norm_num [nodeValue2776, nodeValue412, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2777 node2777Labels = Sparse.eval nodeValue2777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2777) = mixedMoment B node2777 node2777Labels := rfl
  simpa [nodeValue2777, Sparse.eval] using hc.symm

theorem sound2778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2778 node2778Labels = Sparse.eval nodeValue2778 (mixedVector B) := by
  have h := singleton2778 B _hB
  rw [sound270 B _hB _hF] at h
  norm_num [nodeValue2778, nodeValue270, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2779 node2779Labels = Sparse.eval nodeValue2779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2779) = mixedMoment B node2779 node2779Labels := rfl
  simpa [nodeValue2779, Sparse.eval] using hc.symm

theorem sound2780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2780 node2780Labels = Sparse.eval nodeValue2780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2780) = mixedMoment B node2780 node2780Labels := rfl
  simpa [nodeValue2780, Sparse.eval] using hc.symm

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

theorem sound2784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2784 node2784Labels = Sparse.eval nodeValue2784 (mixedVector B) := by
  have h := singleton2784 B _hB
  rw [sound416 B _hB _hF] at h
  norm_num [nodeValue2784, nodeValue416, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2785 node2785Labels = Sparse.eval nodeValue2785 (mixedVector B) := by
  simpa only [nodeValue2785, Sparse.eval_nil] using zero2785 B _hB _hF

theorem sound2786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2786 node2786Labels = Sparse.eval nodeValue2786 (mixedVector B) := by
  simpa only [nodeValue2786, Sparse.eval_nil] using zero2786 B _hB _hF

theorem sound2787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2787 node2787Labels = Sparse.eval nodeValue2787 (mixedVector B) := by
  simpa only [nodeValue2787, Sparse.eval_nil] using zero2787 B _hB _hF

theorem sound2789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2789 node2789Labels = Sparse.eval nodeValue2789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2789) = mixedMoment B node2789 node2789Labels := rfl
  simpa [nodeValue2789, Sparse.eval] using hc.symm

theorem sound2790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2790 node2790Labels = Sparse.eval nodeValue2790 (mixedVector B) := by
  simpa only [nodeValue2790, Sparse.eval_nil] using zero2790 B _hB _hF

theorem sound2791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2791 node2791Labels = Sparse.eval nodeValue2791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2791) = mixedMoment B node2791 node2791Labels := rfl
  simpa [nodeValue2791, Sparse.eval] using hc.symm

theorem sound2792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2792 node2792Labels = Sparse.eval nodeValue2792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2792) = mixedMoment B node2792 node2792Labels := rfl
  simpa [nodeValue2792, Sparse.eval] using hc.symm

theorem sound2793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2793 node2793Labels = Sparse.eval nodeValue2793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2793) = mixedMoment B node2793 node2793Labels := rfl
  simpa [nodeValue2793, Sparse.eval] using hc.symm

theorem sound2794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2794 node2794Labels = Sparse.eval nodeValue2794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2794) = mixedMoment B node2794 node2794Labels := rfl
  simpa [nodeValue2794, Sparse.eval] using hc.symm

theorem sound2795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2795 node2795Labels = Sparse.eval nodeValue2795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2795) = mixedMoment B node2795 node2795Labels := rfl
  simpa [nodeValue2795, Sparse.eval] using hc.symm

theorem sound2796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2796 node2796Labels = Sparse.eval nodeValue2796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2796) = mixedMoment B node2796 node2796Labels := rfl
  simpa [nodeValue2796, Sparse.eval] using hc.symm

theorem sound2797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2797 node2797Labels = Sparse.eval nodeValue2797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2797) = mixedMoment B node2797 node2797Labels := rfl
  simpa [nodeValue2797, Sparse.eval] using hc.symm

theorem sound2798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2798 node2798Labels = Sparse.eval nodeValue2798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2798) = mixedMoment B node2798 node2798Labels := rfl
  simpa [nodeValue2798, Sparse.eval] using hc.symm

theorem sound2799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2799 node2799Labels = Sparse.eval nodeValue2799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2799) = mixedMoment B node2799 node2799Labels := rfl
  simpa [nodeValue2799, Sparse.eval] using hc.symm

theorem sound2800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2800 node2800Labels = Sparse.eval nodeValue2800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2800) = mixedMoment B node2800 node2800Labels := rfl
  simpa [nodeValue2800, Sparse.eval] using hc.symm

theorem sound2801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2801 node2801Labels = Sparse.eval nodeValue2801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2801) = mixedMoment B node2801 node2801Labels := rfl
  simpa [nodeValue2801, Sparse.eval] using hc.symm

theorem sound2802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2802 node2802Labels = Sparse.eval nodeValue2802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2802) = mixedMoment B node2802 node2802Labels := rfl
  simpa [nodeValue2802, Sparse.eval] using hc.symm

theorem sound2803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2803 node2803Labels = Sparse.eval nodeValue2803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2803) = mixedMoment B node2803 node2803Labels := rfl
  simpa [nodeValue2803, Sparse.eval] using hc.symm

theorem sound2804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2804 node2804Labels = Sparse.eval nodeValue2804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2804) = mixedMoment B node2804 node2804Labels := rfl
  simpa [nodeValue2804, Sparse.eval] using hc.symm

theorem sound2805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2805 node2805Labels = Sparse.eval nodeValue2805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2805) = mixedMoment B node2805 node2805Labels := rfl
  simpa [nodeValue2805, Sparse.eval] using hc.symm

theorem sound2806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2806 node2806Labels = Sparse.eval nodeValue2806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2806) = mixedMoment B node2806 node2806Labels := rfl
  simpa [nodeValue2806, Sparse.eval] using hc.symm

theorem sound2807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2807 node2807Labels = Sparse.eval nodeValue2807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2807) = mixedMoment B node2807 node2807Labels := rfl
  simpa [nodeValue2807, Sparse.eval] using hc.symm

theorem sound2808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2808 node2808Labels = Sparse.eval nodeValue2808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2808) = mixedMoment B node2808 node2808Labels := rfl
  simpa [nodeValue2808, Sparse.eval] using hc.symm

theorem sound2809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2809 node2809Labels = Sparse.eval nodeValue2809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2809) = mixedMoment B node2809 node2809Labels := rfl
  simpa [nodeValue2809, Sparse.eval] using hc.symm

theorem sound2810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2810 node2810Labels = Sparse.eval nodeValue2810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2810) = mixedMoment B node2810 node2810Labels := rfl
  simpa [nodeValue2810, Sparse.eval] using hc.symm

theorem sound2811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2811 node2811Labels = Sparse.eval nodeValue2811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2811) = mixedMoment B node2811 node2811Labels := rfl
  simpa [nodeValue2811, Sparse.eval] using hc.symm

theorem sound2812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2812 node2812Labels = Sparse.eval nodeValue2812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2812) = mixedMoment B node2812 node2812Labels := rfl
  simpa [nodeValue2812, Sparse.eval] using hc.symm

theorem sound2813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2813 node2813Labels = Sparse.eval nodeValue2813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2813) = mixedMoment B node2813 node2813Labels := rfl
  simpa [nodeValue2813, Sparse.eval] using hc.symm

theorem sound2814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2814 node2814Labels = Sparse.eval nodeValue2814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2814) = mixedMoment B node2814 node2814Labels := rfl
  simpa [nodeValue2814, Sparse.eval] using hc.symm

theorem sound2815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2815 node2815Labels = Sparse.eval nodeValue2815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2815) = mixedMoment B node2815 node2815Labels := rfl
  simpa [nodeValue2815, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
