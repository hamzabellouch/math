import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons60

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3840 node3840Labels = Sparse.eval nodeValue3840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3840) = mixedMoment B node3840 node3840Labels := rfl
  simpa [nodeValue3840, Sparse.eval] using hc.symm

theorem sound3841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3841 node3841Labels = Sparse.eval nodeValue3841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3841) = mixedMoment B node3841 node3841Labels := rfl
  simpa [nodeValue3841, Sparse.eval] using hc.symm

theorem sound3842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3842 node3842Labels = Sparse.eval nodeValue3842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3842) = mixedMoment B node3842 node3842Labels := rfl
  simpa [nodeValue3842, Sparse.eval] using hc.symm

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3844 node3844Labels = Sparse.eval nodeValue3844 (mixedVector B) := by
  simpa only [nodeValue3844, Sparse.eval_nil] using zero3844 B _hB _hF

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

theorem sound3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3846 node3846Labels = Sparse.eval nodeValue3846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3846) = mixedMoment B node3846 node3846Labels := rfl
  simpa [nodeValue3846, Sparse.eval] using hc.symm

theorem sound3847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3847 node3847Labels = Sparse.eval nodeValue3847 (mixedVector B) := by
  have h := singleton3847 B _hB
  rw [sound462 B _hB _hF] at h
  norm_num [nodeValue3847, nodeValue462, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3848 node3848Labels = Sparse.eval nodeValue3848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3848) = mixedMoment B node3848 node3848Labels := rfl
  simpa [nodeValue3848, Sparse.eval] using hc.symm

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3851 node3851Labels = Sparse.eval nodeValue3851 (mixedVector B) := by
  have h := singleton3851 B _hB
  rw [sound488 B _hB _hF] at h
  norm_num [nodeValue3851, nodeValue488, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3852 node3852Labels = Sparse.eval nodeValue3852 (mixedVector B) := by
  have h := singleton3852 B _hB
  rw [sound489 B _hB _hF] at h
  norm_num [nodeValue3852, nodeValue489, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3853 node3853Labels = Sparse.eval nodeValue3853 (mixedVector B) := by
  have h := singleton3853 B _hB
  rw [sound490 B _hB _hF] at h
  norm_num [nodeValue3853, nodeValue490, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3854 node3854Labels = Sparse.eval nodeValue3854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3854) = mixedMoment B node3854 node3854Labels := rfl
  simpa [nodeValue3854, Sparse.eval] using hc.symm

theorem sound3855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3855 node3855Labels = Sparse.eval nodeValue3855 (mixedVector B) := by
  have h := singleton3855 B _hB
  rw [sound492 B _hB _hF] at h
  norm_num [nodeValue3855, nodeValue492, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3856 node3856Labels = Sparse.eval nodeValue3856 (mixedVector B) := by
  have h := singleton3856 B _hB
  rw [sound468 B _hB _hF] at h
  norm_num [nodeValue3856, nodeValue468, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3858 node3858Labels = Sparse.eval nodeValue3858 (mixedVector B) := by
  have h := singleton3858 B _hB
  rw [sound494 B _hB _hF] at h
  norm_num [nodeValue3858, nodeValue494, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3859 node3859Labels = Sparse.eval nodeValue3859 (mixedVector B) := by
  simpa only [nodeValue3859, Sparse.eval_nil] using zero3859 B _hB _hF

theorem sound3860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = Sparse.eval nodeValue3860 (mixedVector B) := by
  simpa only [nodeValue3860, Sparse.eval_nil] using zero3860 B _hB _hF

theorem sound3861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3861 node3861Labels = Sparse.eval nodeValue3861 (mixedVector B) := by
  simpa only [nodeValue3861, Sparse.eval_nil] using zero3861 B _hB _hF

theorem sound3863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3863 node3863Labels = Sparse.eval nodeValue3863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3863) = mixedMoment B node3863 node3863Labels := rfl
  simpa [nodeValue3863, Sparse.eval] using hc.symm

theorem sound3864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3864 node3864Labels = Sparse.eval nodeValue3864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3864) = mixedMoment B node3864 node3864Labels := rfl
  simpa [nodeValue3864, Sparse.eval] using hc.symm

theorem sound3865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3865 node3865Labels = Sparse.eval nodeValue3865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3865) = mixedMoment B node3865 node3865Labels := rfl
  simpa [nodeValue3865, Sparse.eval] using hc.symm

theorem sound3866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3866 node3866Labels = Sparse.eval nodeValue3866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3866) = mixedMoment B node3866 node3866Labels := rfl
  simpa [nodeValue3866, Sparse.eval] using hc.symm

theorem sound3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3867 node3867Labels = Sparse.eval nodeValue3867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3867) = mixedMoment B node3867 node3867Labels := rfl
  simpa [nodeValue3867, Sparse.eval] using hc.symm

theorem sound3868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3868 node3868Labels = Sparse.eval nodeValue3868 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3868) = mixedMoment B node3868 node3868Labels := rfl
  simpa [nodeValue3868, Sparse.eval] using hc.symm

theorem sound3869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3869 node3869Labels = Sparse.eval nodeValue3869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3869) = mixedMoment B node3869 node3869Labels := rfl
  simpa [nodeValue3869, Sparse.eval] using hc.symm

theorem sound3870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3870 node3870Labels = Sparse.eval nodeValue3870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3870) = mixedMoment B node3870 node3870Labels := rfl
  simpa [nodeValue3870, Sparse.eval] using hc.symm

theorem sound3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3871 node3871Labels = Sparse.eval nodeValue3871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3871) = mixedMoment B node3871 node3871Labels := rfl
  simpa [nodeValue3871, Sparse.eval] using hc.symm

theorem sound3872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3872 node3872Labels = Sparse.eval nodeValue3872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3872) = mixedMoment B node3872 node3872Labels := rfl
  simpa [nodeValue3872, Sparse.eval] using hc.symm

theorem sound3873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3873 node3873Labels = Sparse.eval nodeValue3873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3873) = mixedMoment B node3873 node3873Labels := rfl
  simpa [nodeValue3873, Sparse.eval] using hc.symm

theorem sound3874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3874 node3874Labels = Sparse.eval nodeValue3874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3874) = mixedMoment B node3874 node3874Labels := rfl
  simpa [nodeValue3874, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3877 node3877Labels = Sparse.eval nodeValue3877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3877) = mixedMoment B node3877 node3877Labels := rfl
  simpa [nodeValue3877, Sparse.eval] using hc.symm

theorem sound3878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3878 node3878Labels = Sparse.eval nodeValue3878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3878) = mixedMoment B node3878 node3878Labels := rfl
  simpa [nodeValue3878, Sparse.eval] using hc.symm

theorem sound3879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3879 node3879Labels = Sparse.eval nodeValue3879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3879) = mixedMoment B node3879 node3879Labels := rfl
  simpa [nodeValue3879, Sparse.eval] using hc.symm

theorem sound3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3880 node3880Labels = Sparse.eval nodeValue3880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3880) = mixedMoment B node3880 node3880Labels := rfl
  simpa [nodeValue3880, Sparse.eval] using hc.symm

theorem sound3881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3881 node3881Labels = Sparse.eval nodeValue3881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3881) = mixedMoment B node3881 node3881Labels := rfl
  simpa [nodeValue3881, Sparse.eval] using hc.symm

theorem sound3882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3882 node3882Labels = Sparse.eval nodeValue3882 (mixedVector B) := by
  have h := singleton3882 B _hB
  rw [sound499 B _hB _hF] at h
  norm_num [nodeValue3882, nodeValue499, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3883 node3883Labels = Sparse.eval nodeValue3883 (mixedVector B) := by
  have h := singleton3883 B _hB
  rw [sound467 B _hB _hF] at h
  norm_num [nodeValue3883, nodeValue467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

theorem sound3886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3886 node3886Labels = Sparse.eval nodeValue3886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3886) = mixedMoment B node3886 node3886Labels := rfl
  simpa [nodeValue3886, Sparse.eval] using hc.symm

theorem sound3887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3887 node3887Labels = Sparse.eval nodeValue3887 (mixedVector B) := by
  have h := singleton3887 B _hB
  rw [sound502 B _hB _hF] at h
  norm_num [nodeValue3887, nodeValue502, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3888 node3888Labels = Sparse.eval nodeValue3888 (mixedVector B) := by
  have h := singleton3888 B _hB
  rw [sound503 B _hB _hF] at h
  norm_num [nodeValue3888, nodeValue503, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3889 node3889Labels = Sparse.eval nodeValue3889 (mixedVector B) := by
  have h := singleton3889 B _hB
  rw [sound496 B _hB _hF] at h
  norm_num [nodeValue3889, nodeValue496, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3890 node3890Labels = Sparse.eval nodeValue3890 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3890) = mixedMoment B node3890 node3890Labels := rfl
  simpa [nodeValue3890, Sparse.eval] using hc.symm

theorem sound3891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3891 node3891Labels = Sparse.eval nodeValue3891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3891) = mixedMoment B node3891 node3891Labels := rfl
  simpa [nodeValue3891, Sparse.eval] using hc.symm

theorem sound3892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3892 node3892Labels = Sparse.eval nodeValue3892 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3892) = mixedMoment B node3892 node3892Labels := rfl
  simpa [nodeValue3892, Sparse.eval] using hc.symm

theorem sound3893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3893 node3893Labels = Sparse.eval nodeValue3893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3893) = mixedMoment B node3893 node3893Labels := rfl
  simpa [nodeValue3893, Sparse.eval] using hc.symm

theorem sound3894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3894 node3894Labels = Sparse.eval nodeValue3894 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3894) = mixedMoment B node3894 node3894Labels := rfl
  simpa [nodeValue3894, Sparse.eval] using hc.symm

theorem sound3895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3895 node3895Labels = Sparse.eval nodeValue3895 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3895) = mixedMoment B node3895 node3895Labels := rfl
  simpa [nodeValue3895, Sparse.eval] using hc.symm

theorem sound3896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3896 node3896Labels = Sparse.eval nodeValue3896 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3896) = mixedMoment B node3896 node3896Labels := rfl
  simpa [nodeValue3896, Sparse.eval] using hc.symm

theorem sound3897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3897 node3897Labels = Sparse.eval nodeValue3897 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3897) = mixedMoment B node3897 node3897Labels := rfl
  simpa [nodeValue3897, Sparse.eval] using hc.symm

theorem sound3898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3898 node3898Labels = Sparse.eval nodeValue3898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3898) = mixedMoment B node3898 node3898Labels := rfl
  simpa [nodeValue3898, Sparse.eval] using hc.symm

theorem sound3899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3899 node3899Labels = Sparse.eval nodeValue3899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3899) = mixedMoment B node3899 node3899Labels := rfl
  simpa [nodeValue3899, Sparse.eval] using hc.symm

theorem sound3900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3900 node3900Labels = Sparse.eval nodeValue3900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3900) = mixedMoment B node3900 node3900Labels := rfl
  simpa [nodeValue3900, Sparse.eval] using hc.symm

theorem sound3901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3901 node3901Labels = Sparse.eval nodeValue3901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3901) = mixedMoment B node3901 node3901Labels := rfl
  simpa [nodeValue3901, Sparse.eval] using hc.symm

theorem sound3902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3902 node3902Labels = Sparse.eval nodeValue3902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3902) = mixedMoment B node3902 node3902Labels := rfl
  simpa [nodeValue3902, Sparse.eval] using hc.symm

theorem sound3903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3903 node3903Labels = Sparse.eval nodeValue3903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3903) = mixedMoment B node3903 node3903Labels := rfl
  simpa [nodeValue3903, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
