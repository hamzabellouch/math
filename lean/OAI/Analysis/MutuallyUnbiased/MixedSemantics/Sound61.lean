import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons61

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3904 node3904Labels = Sparse.eval nodeValue3904 (mixedVector B) := by
  simpa only [nodeValue3904, Sparse.eval_nil] using zero3904 B _hB _hF

theorem sound3905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3905 node3905Labels = Sparse.eval nodeValue3905 (mixedVector B) := by
  simpa only [nodeValue3905, Sparse.eval_nil] using zero3905 B _hB _hF

theorem sound3906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3906 node3906Labels = Sparse.eval nodeValue3906 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3906) = mixedMoment B node3906 node3906Labels := rfl
  simpa [nodeValue3906, Sparse.eval] using hc.symm

theorem sound3908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3908 node3908Labels = Sparse.eval nodeValue3908 (mixedVector B) := by
  simpa only [nodeValue3908, Sparse.eval_nil] using zero3908 B _hB _hF

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

theorem sound3910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3910 node3910Labels = Sparse.eval nodeValue3910 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3910) = mixedMoment B node3910 node3910Labels := rfl
  simpa [nodeValue3910, Sparse.eval] using hc.symm

theorem sound3911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3911 node3911Labels = Sparse.eval nodeValue3911 (mixedVector B) := by
  have h := singleton3911 B _hB
  rw [sound504 B _hB _hF] at h
  norm_num [nodeValue3911, nodeValue504, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3913 node3913Labels = Sparse.eval nodeValue3913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3913) = mixedMoment B node3913 node3913Labels := rfl
  simpa [nodeValue3913, Sparse.eval] using hc.symm

theorem sound3914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3914 node3914Labels = Sparse.eval nodeValue3914 (mixedVector B) := by
  simpa only [nodeValue3914, Sparse.eval_nil] using zero3914 B _hB _hF

theorem sound3915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3915 node3915Labels = Sparse.eval nodeValue3915 (mixedVector B) := by
  have h := singleton3915 B _hB
  rw [sound505 B _hB _hF] at h
  norm_num [nodeValue3915, nodeValue505, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3916 node3916Labels = Sparse.eval nodeValue3916 (mixedVector B) := by
  have h := singleton3916 B _hB
  rw [sound507 B _hB _hF] at h
  norm_num [nodeValue3916, nodeValue507, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3917 node3917Labels = Sparse.eval nodeValue3917 (mixedVector B) := by
  simpa only [nodeValue3917, Sparse.eval_nil] using zero3917 B _hB _hF

theorem sound3918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3918 node3918Labels = Sparse.eval nodeValue3918 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3918) = mixedMoment B node3918 node3918Labels := rfl
  simpa [nodeValue3918, Sparse.eval] using hc.symm

theorem sound3919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3919 node3919Labels = Sparse.eval nodeValue3919 (mixedVector B) := by
  have h := singleton3919 B _hB
  rw [sound425 B _hB _hF] at h
  norm_num [nodeValue3919, nodeValue425, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3920 node3920Labels = Sparse.eval nodeValue3920 (mixedVector B) := by
  simpa only [nodeValue3920, Sparse.eval_nil] using zero3920 B _hB _hF

theorem sound3921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3921 node3921Labels = Sparse.eval nodeValue3921 (mixedVector B) := by
  simpa only [nodeValue3921, Sparse.eval_nil] using zero3921 B _hB _hF

theorem sound3922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3922 node3922Labels = Sparse.eval nodeValue3922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3922) = mixedMoment B node3922 node3922Labels := rfl
  simpa [nodeValue3922, Sparse.eval] using hc.symm

theorem sound3923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3923 node3923Labels = Sparse.eval nodeValue3923 (mixedVector B) := by
  simpa only [nodeValue3923, Sparse.eval_nil] using zero3923 B _hB _hF

theorem sound3924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3924 node3924Labels = Sparse.eval nodeValue3924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3924) = mixedMoment B node3924 node3924Labels := rfl
  simpa [nodeValue3924, Sparse.eval] using hc.symm

theorem sound3925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3925 node3925Labels = Sparse.eval nodeValue3925 (mixedVector B) := by
  have h := singleton3925 B _hB
  rw [sound453 B _hB _hF] at h
  norm_num [nodeValue3925, nodeValue453, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3926 node3926Labels = Sparse.eval nodeValue3926 (mixedVector B) := by
  have h := singleton3926 B _hB
  rw [sound433 B _hB _hF] at h
  norm_num [nodeValue3926, nodeValue433, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3927 node3927Labels = Sparse.eval nodeValue3927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3927) = mixedMoment B node3927 node3927Labels := rfl
  simpa [nodeValue3927, Sparse.eval] using hc.symm

theorem sound3928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3928 node3928Labels = Sparse.eval nodeValue3928 (mixedVector B) := by
  simpa only [nodeValue3928, Sparse.eval_nil] using zero3928 B _hB _hF

theorem sound3929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3929 node3929Labels = Sparse.eval nodeValue3929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3929) = mixedMoment B node3929 node3929Labels := rfl
  simpa [nodeValue3929, Sparse.eval] using hc.symm

theorem sound3930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3930 node3930Labels = Sparse.eval nodeValue3930 (mixedVector B) := by
  have h := singleton3930 B _hB
  rw [sound508 B _hB _hF] at h
  norm_num [nodeValue3930, nodeValue508, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3931 node3931Labels = Sparse.eval nodeValue3931 (mixedVector B) := by
  have h := singleton3931 B _hB
  rw [sound509 B _hB _hF] at h
  norm_num [nodeValue3931, nodeValue509, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3932 node3932Labels = Sparse.eval nodeValue3932 (mixedVector B) := by
  have h := singleton3932 B _hB
  rw [sound460 B _hB _hF] at h
  norm_num [nodeValue3932, nodeValue460, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3933 node3933Labels = Sparse.eval nodeValue3933 (mixedVector B) := by
  have h := singleton3933 B _hB
  rw [sound474 B _hB _hF] at h
  norm_num [nodeValue3933, nodeValue474, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3934 node3934Labels = Sparse.eval nodeValue3934 (mixedVector B) := by
  have h := singleton3934 B _hB
  rw [sound510 B _hB _hF] at h
  norm_num [nodeValue3934, nodeValue510, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3935 node3935Labels = Sparse.eval nodeValue3935 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3935) = mixedMoment B node3935 node3935Labels := rfl
  simpa [nodeValue3935, Sparse.eval] using hc.symm

theorem sound3936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3936 node3936Labels = Sparse.eval nodeValue3936 (mixedVector B) := by
  have h := singleton3936 B _hB
  rw [sound430 B _hB _hF] at h
  norm_num [nodeValue3936, nodeValue430, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3937 node3937Labels = Sparse.eval nodeValue3937 (mixedVector B) := by
  have h := singleton3937 B _hB
  rw [sound429 B _hB _hF] at h
  norm_num [nodeValue3937, nodeValue429, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3938 node3938Labels = Sparse.eval nodeValue3938 (mixedVector B) := by
  have h := singleton3938 B _hB
  rw [sound436 B _hB _hF] at h
  norm_num [nodeValue3938, nodeValue436, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3939 node3939Labels = Sparse.eval nodeValue3939 (mixedVector B) := by
  have h := singleton3939 B _hB
  rw [sound437 B _hB _hF] at h
  norm_num [nodeValue3939, nodeValue437, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3940 node3940Labels = Sparse.eval nodeValue3940 (mixedVector B) := by
  simpa only [nodeValue3940, Sparse.eval_nil] using zero3940 B _hB _hF

theorem sound3941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3941 node3941Labels = Sparse.eval nodeValue3941 (mixedVector B) := by
  simpa only [nodeValue3941, Sparse.eval_nil] using zero3941 B _hB _hF

theorem sound3942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3942 node3942Labels = Sparse.eval nodeValue3942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3942) = mixedMoment B node3942 node3942Labels := rfl
  simpa [nodeValue3942, Sparse.eval] using hc.symm

theorem sound3943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3943 node3943Labels = Sparse.eval nodeValue3943 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3943) = mixedMoment B node3943 node3943Labels := rfl
  simpa [nodeValue3943, Sparse.eval] using hc.symm

theorem sound3944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3944 node3944Labels = Sparse.eval nodeValue3944 (mixedVector B) := by
  simpa only [nodeValue3944, Sparse.eval_nil] using zero3944 B _hB _hF

theorem sound3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3945 node3945Labels = Sparse.eval nodeValue3945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3945) = mixedMoment B node3945 node3945Labels := rfl
  simpa [nodeValue3945, Sparse.eval] using hc.symm

theorem sound3946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3946 node3946Labels = Sparse.eval nodeValue3946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3946) = mixedMoment B node3946 node3946Labels := rfl
  simpa [nodeValue3946, Sparse.eval] using hc.symm

theorem sound3947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3947 node3947Labels = Sparse.eval nodeValue3947 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3947) = mixedMoment B node3947 node3947Labels := rfl
  simpa [nodeValue3947, Sparse.eval] using hc.symm

theorem sound3948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3948 node3948Labels = Sparse.eval nodeValue3948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3948) = mixedMoment B node3948 node3948Labels := rfl
  simpa [nodeValue3948, Sparse.eval] using hc.symm

theorem sound3949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3949 node3949Labels = Sparse.eval nodeValue3949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3949) = mixedMoment B node3949 node3949Labels := rfl
  simpa [nodeValue3949, Sparse.eval] using hc.symm

theorem sound3950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3950 node3950Labels = Sparse.eval nodeValue3950 (mixedVector B) := by
  simpa only [nodeValue3950, Sparse.eval_nil] using zero3950 B _hB _hF

theorem sound3951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3951 node3951Labels = Sparse.eval nodeValue3951 (mixedVector B) := by
  simpa only [nodeValue3951, Sparse.eval_nil] using zero3951 B _hB _hF

theorem sound3952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3952 node3952Labels = Sparse.eval nodeValue3952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3952) = mixedMoment B node3952 node3952Labels := rfl
  simpa [nodeValue3952, Sparse.eval] using hc.symm

theorem sound3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = Sparse.eval nodeValue3953 (mixedVector B) := by
  simpa only [nodeValue3953, Sparse.eval_nil] using zero3953 B _hB _hF

theorem sound3954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3954 node3954Labels = Sparse.eval nodeValue3954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3954) = mixedMoment B node3954 node3954Labels := rfl
  simpa [nodeValue3954, Sparse.eval] using hc.symm

theorem sound3955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3955 node3955Labels = Sparse.eval nodeValue3955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3955) = mixedMoment B node3955 node3955Labels := rfl
  simpa [nodeValue3955, Sparse.eval] using hc.symm

theorem sound3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = Sparse.eval nodeValue3956 (mixedVector B) := by
  simpa only [nodeValue3956, Sparse.eval_nil] using zero3956 B _hB _hF

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

theorem sound3959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3959 node3959Labels = Sparse.eval nodeValue3959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3959) = mixedMoment B node3959 node3959Labels := rfl
  simpa [nodeValue3959, Sparse.eval] using hc.symm

theorem sound3960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3960 node3960Labels = Sparse.eval nodeValue3960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3960) = mixedMoment B node3960 node3960Labels := rfl
  simpa [nodeValue3960, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

theorem sound3962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3962 node3962Labels = Sparse.eval nodeValue3962 (mixedVector B) := by
  simpa only [nodeValue3962, Sparse.eval_nil] using zero3962 B _hB _hF

theorem sound3963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3963 node3963Labels = Sparse.eval nodeValue3963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3963) = mixedMoment B node3963 node3963Labels := rfl
  simpa [nodeValue3963, Sparse.eval] using hc.symm

theorem sound3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3964 node3964Labels = Sparse.eval nodeValue3964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3964) = mixedMoment B node3964 node3964Labels := rfl
  simpa [nodeValue3964, Sparse.eval] using hc.symm

theorem sound3965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3965 node3965Labels = Sparse.eval nodeValue3965 (mixedVector B) := by
  have h := singleton3965 B _hB
  rw [sound517 B _hB _hF] at h
  norm_num [nodeValue3965, nodeValue517, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3966 node3966Labels = Sparse.eval nodeValue3966 (mixedVector B) := by
  have h := singleton3966 B _hB
  rw [sound457 B _hB _hF] at h
  norm_num [nodeValue3966, nodeValue457, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3967 node3967Labels = Sparse.eval nodeValue3967 (mixedVector B) := by
  have h := singleton3967 B _hB
  rw [sound472 B _hB _hF] at h
  norm_num [nodeValue3967, nodeValue472, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
