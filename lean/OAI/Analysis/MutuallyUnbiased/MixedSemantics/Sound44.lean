import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons44

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2816 node2816Labels = Sparse.eval nodeValue2816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2816) = mixedMoment B node2816 node2816Labels := rfl
  simpa [nodeValue2816, Sparse.eval] using hc.symm

theorem sound2817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2817 node2817Labels = Sparse.eval nodeValue2817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2817) = mixedMoment B node2817 node2817Labels := rfl
  simpa [nodeValue2817, Sparse.eval] using hc.symm

theorem sound2818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2818 node2818Labels = Sparse.eval nodeValue2818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2818) = mixedMoment B node2818 node2818Labels := rfl
  simpa [nodeValue2818, Sparse.eval] using hc.symm

theorem sound2819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2819 node2819Labels = Sparse.eval nodeValue2819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2819) = mixedMoment B node2819 node2819Labels := rfl
  simpa [nodeValue2819, Sparse.eval] using hc.symm

theorem sound2820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2820 node2820Labels = Sparse.eval nodeValue2820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2820) = mixedMoment B node2820 node2820Labels := rfl
  simpa [nodeValue2820, Sparse.eval] using hc.symm

theorem sound2821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2821 node2821Labels = Sparse.eval nodeValue2821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2821) = mixedMoment B node2821 node2821Labels := rfl
  simpa [nodeValue2821, Sparse.eval] using hc.symm

theorem sound2822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2822 node2822Labels = Sparse.eval nodeValue2822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2822) = mixedMoment B node2822 node2822Labels := rfl
  simpa [nodeValue2822, Sparse.eval] using hc.symm

theorem sound2823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2823 node2823Labels = Sparse.eval nodeValue2823 (mixedVector B) := by
  simpa only [nodeValue2823, Sparse.eval_nil] using zero2823 B _hB _hF

theorem sound2824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2824 node2824Labels = Sparse.eval nodeValue2824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2824) = mixedMoment B node2824 node2824Labels := rfl
  simpa [nodeValue2824, Sparse.eval] using hc.symm

theorem sound2825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2825 node2825Labels = Sparse.eval nodeValue2825 (mixedVector B) := by
  simpa only [nodeValue2825, Sparse.eval_nil] using zero2825 B _hB _hF

theorem sound2826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2826 node2826Labels = Sparse.eval nodeValue2826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2826) = mixedMoment B node2826 node2826Labels := rfl
  simpa [nodeValue2826, Sparse.eval] using hc.symm

theorem sound2827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2827 node2827Labels = Sparse.eval nodeValue2827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2827) = mixedMoment B node2827 node2827Labels := rfl
  simpa [nodeValue2827, Sparse.eval] using hc.symm

theorem sound2828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2828 node2828Labels = Sparse.eval nodeValue2828 (mixedVector B) := by
  have h := singleton2828 B _hB
  rw [sound273 B _hB _hF] at h
  norm_num [nodeValue2828, nodeValue273, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2829 node2829Labels = Sparse.eval nodeValue2829 (mixedVector B) := by
  have h := singleton2829 B _hB
  rw [sound275 B _hB _hF] at h
  norm_num [nodeValue2829, nodeValue275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2830 node2830Labels = Sparse.eval nodeValue2830 (mixedVector B) := by
  have h := singleton2830 B _hB
  rw [sound276 B _hB _hF] at h
  norm_num [nodeValue2830, nodeValue276, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2831 node2831Labels = Sparse.eval nodeValue2831 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2831) = mixedMoment B node2831 node2831Labels := rfl
  simpa [nodeValue2831, Sparse.eval] using hc.symm

theorem sound2832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2832 node2832Labels = Sparse.eval nodeValue2832 (mixedVector B) := by
  have h := singleton2832 B _hB
  rw [sound186 B _hB _hF] at h
  norm_num [nodeValue2832, nodeValue186, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2833 node2833Labels = Sparse.eval nodeValue2833 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2833) = mixedMoment B node2833 node2833Labels := rfl
  simpa [nodeValue2833, Sparse.eval] using hc.symm

theorem sound2834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2834 node2834Labels = Sparse.eval nodeValue2834 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2834) = mixedMoment B node2834 node2834Labels := rfl
  simpa [nodeValue2834, Sparse.eval] using hc.symm

theorem sound2835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2835 node2835Labels = Sparse.eval nodeValue2835 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2835) = mixedMoment B node2835 node2835Labels := rfl
  simpa [nodeValue2835, Sparse.eval] using hc.symm

theorem sound2836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2836 node2836Labels = Sparse.eval nodeValue2836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2836) = mixedMoment B node2836 node2836Labels := rfl
  simpa [nodeValue2836, Sparse.eval] using hc.symm

theorem sound2837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2837 node2837Labels = Sparse.eval nodeValue2837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2837) = mixedMoment B node2837 node2837Labels := rfl
  simpa [nodeValue2837, Sparse.eval] using hc.symm

theorem sound2838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2838 node2838Labels = Sparse.eval nodeValue2838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2838) = mixedMoment B node2838 node2838Labels := rfl
  simpa [nodeValue2838, Sparse.eval] using hc.symm

theorem sound2839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2839 node2839Labels = Sparse.eval nodeValue2839 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2839) = mixedMoment B node2839 node2839Labels := rfl
  simpa [nodeValue2839, Sparse.eval] using hc.symm

theorem sound2840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2840 node2840Labels = Sparse.eval nodeValue2840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2840) = mixedMoment B node2840 node2840Labels := rfl
  simpa [nodeValue2840, Sparse.eval] using hc.symm

theorem sound2841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2841 node2841Labels = Sparse.eval nodeValue2841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2841) = mixedMoment B node2841 node2841Labels := rfl
  simpa [nodeValue2841, Sparse.eval] using hc.symm

theorem sound2842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2842 node2842Labels = Sparse.eval nodeValue2842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2842) = mixedMoment B node2842 node2842Labels := rfl
  simpa [nodeValue2842, Sparse.eval] using hc.symm

theorem sound2843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2843 node2843Labels = Sparse.eval nodeValue2843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2843) = mixedMoment B node2843 node2843Labels := rfl
  simpa [nodeValue2843, Sparse.eval] using hc.symm

theorem sound2844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2844 node2844Labels = Sparse.eval nodeValue2844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2844) = mixedMoment B node2844 node2844Labels := rfl
  simpa [nodeValue2844, Sparse.eval] using hc.symm

theorem sound2845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2845 node2845Labels = Sparse.eval nodeValue2845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2845) = mixedMoment B node2845 node2845Labels := rfl
  simpa [nodeValue2845, Sparse.eval] using hc.symm

theorem sound2846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2846 node2846Labels = Sparse.eval nodeValue2846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2846) = mixedMoment B node2846 node2846Labels := rfl
  simpa [nodeValue2846, Sparse.eval] using hc.symm

theorem sound2847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2847 node2847Labels = Sparse.eval nodeValue2847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2847) = mixedMoment B node2847 node2847Labels := rfl
  simpa [nodeValue2847, Sparse.eval] using hc.symm

theorem sound2848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2848 node2848Labels = Sparse.eval nodeValue2848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2848) = mixedMoment B node2848 node2848Labels := rfl
  simpa [nodeValue2848, Sparse.eval] using hc.symm

theorem sound2849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2849 node2849Labels = Sparse.eval nodeValue2849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2849) = mixedMoment B node2849 node2849Labels := rfl
  simpa [nodeValue2849, Sparse.eval] using hc.symm

theorem sound2850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2850 node2850Labels = Sparse.eval nodeValue2850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2850) = mixedMoment B node2850 node2850Labels := rfl
  simpa [nodeValue2850, Sparse.eval] using hc.symm

theorem sound2851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2851 node2851Labels = Sparse.eval nodeValue2851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2851) = mixedMoment B node2851 node2851Labels := rfl
  simpa [nodeValue2851, Sparse.eval] using hc.symm

theorem sound2852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2852 node2852Labels = Sparse.eval nodeValue2852 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2852) = mixedMoment B node2852 node2852Labels := rfl
  simpa [nodeValue2852, Sparse.eval] using hc.symm

theorem sound2853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2853 node2853Labels = Sparse.eval nodeValue2853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2853) = mixedMoment B node2853 node2853Labels := rfl
  simpa [nodeValue2853, Sparse.eval] using hc.symm

theorem sound2854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2854 node2854Labels = Sparse.eval nodeValue2854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2854) = mixedMoment B node2854 node2854Labels := rfl
  simpa [nodeValue2854, Sparse.eval] using hc.symm

theorem sound2855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2855 node2855Labels = Sparse.eval nodeValue2855 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2855) = mixedMoment B node2855 node2855Labels := rfl
  simpa [nodeValue2855, Sparse.eval] using hc.symm

theorem sound2856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2856 node2856Labels = Sparse.eval nodeValue2856 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2856) = mixedMoment B node2856 node2856Labels := rfl
  simpa [nodeValue2856, Sparse.eval] using hc.symm

theorem sound2857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2857 node2857Labels = Sparse.eval nodeValue2857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2857) = mixedMoment B node2857 node2857Labels := rfl
  simpa [nodeValue2857, Sparse.eval] using hc.symm

theorem sound2858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2858 node2858Labels = Sparse.eval nodeValue2858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2858) = mixedMoment B node2858 node2858Labels := rfl
  simpa [nodeValue2858, Sparse.eval] using hc.symm

theorem sound2859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2859 node2859Labels = Sparse.eval nodeValue2859 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2859) = mixedMoment B node2859 node2859Labels := rfl
  simpa [nodeValue2859, Sparse.eval] using hc.symm

theorem sound2860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2860 node2860Labels = Sparse.eval nodeValue2860 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2860) = mixedMoment B node2860 node2860Labels := rfl
  simpa [nodeValue2860, Sparse.eval] using hc.symm

theorem sound2861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2861 node2861Labels = Sparse.eval nodeValue2861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2861) = mixedMoment B node2861 node2861Labels := rfl
  simpa [nodeValue2861, Sparse.eval] using hc.symm

theorem sound2862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2862 node2862Labels = Sparse.eval nodeValue2862 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2862) = mixedMoment B node2862 node2862Labels := rfl
  simpa [nodeValue2862, Sparse.eval] using hc.symm

theorem sound2863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2863 node2863Labels = Sparse.eval nodeValue2863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2863) = mixedMoment B node2863 node2863Labels := rfl
  simpa [nodeValue2863, Sparse.eval] using hc.symm

theorem sound2864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2864 node2864Labels = Sparse.eval nodeValue2864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2864) = mixedMoment B node2864 node2864Labels := rfl
  simpa [nodeValue2864, Sparse.eval] using hc.symm

theorem sound2865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2865 node2865Labels = Sparse.eval nodeValue2865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2865) = mixedMoment B node2865 node2865Labels := rfl
  simpa [nodeValue2865, Sparse.eval] using hc.symm

theorem sound2866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2866 node2866Labels = Sparse.eval nodeValue2866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2866) = mixedMoment B node2866 node2866Labels := rfl
  simpa [nodeValue2866, Sparse.eval] using hc.symm

theorem sound2867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2867 node2867Labels = Sparse.eval nodeValue2867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2867) = mixedMoment B node2867 node2867Labels := rfl
  simpa [nodeValue2867, Sparse.eval] using hc.symm

theorem sound2868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2868 node2868Labels = Sparse.eval nodeValue2868 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2868) = mixedMoment B node2868 node2868Labels := rfl
  simpa [nodeValue2868, Sparse.eval] using hc.symm

theorem sound2869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2869 node2869Labels = Sparse.eval nodeValue2869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2869) = mixedMoment B node2869 node2869Labels := rfl
  simpa [nodeValue2869, Sparse.eval] using hc.symm

theorem sound2870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2870 node2870Labels = Sparse.eval nodeValue2870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2870) = mixedMoment B node2870 node2870Labels := rfl
  simpa [nodeValue2870, Sparse.eval] using hc.symm

theorem sound2871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2871 node2871Labels = Sparse.eval nodeValue2871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2871) = mixedMoment B node2871 node2871Labels := rfl
  simpa [nodeValue2871, Sparse.eval] using hc.symm

theorem sound2872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2872 node2872Labels = Sparse.eval nodeValue2872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2872) = mixedMoment B node2872 node2872Labels := rfl
  simpa [nodeValue2872, Sparse.eval] using hc.symm

theorem sound2873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2873 node2873Labels = Sparse.eval nodeValue2873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2873) = mixedMoment B node2873 node2873Labels := rfl
  simpa [nodeValue2873, Sparse.eval] using hc.symm

theorem sound2874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2874 node2874Labels = Sparse.eval nodeValue2874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2874) = mixedMoment B node2874 node2874Labels := rfl
  simpa [nodeValue2874, Sparse.eval] using hc.symm

theorem sound2875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2875 node2875Labels = Sparse.eval nodeValue2875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2875) = mixedMoment B node2875 node2875Labels := rfl
  simpa [nodeValue2875, Sparse.eval] using hc.symm

theorem sound2876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2876 node2876Labels = Sparse.eval nodeValue2876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2876) = mixedMoment B node2876 node2876Labels := rfl
  simpa [nodeValue2876, Sparse.eval] using hc.symm

theorem sound2877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2877 node2877Labels = Sparse.eval nodeValue2877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2877) = mixedMoment B node2877 node2877Labels := rfl
  simpa [nodeValue2877, Sparse.eval] using hc.symm

theorem sound2878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2878 node2878Labels = Sparse.eval nodeValue2878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2878) = mixedMoment B node2878 node2878Labels := rfl
  simpa [nodeValue2878, Sparse.eval] using hc.symm

theorem sound2879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2879 node2879Labels = Sparse.eval nodeValue2879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2879) = mixedMoment B node2879 node2879Labels := rfl
  simpa [nodeValue2879, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
