import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4032 node4032Labels = Sparse.eval nodeValue4032 (mixedVector B) := by
  have h := singleton4032 B _hB
  rw [sound478 B _hB _hF] at h
  norm_num [nodeValue4032, nodeValue478, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4033 node4033Labels = Sparse.eval nodeValue4033 (mixedVector B) := by
  have h := singleton4033 B _hB
  rw [sound488 B _hB _hF] at h
  norm_num [nodeValue4033, nodeValue488, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4034 node4034Labels = Sparse.eval nodeValue4034 (mixedVector B) := by
  simpa only [nodeValue4034, Sparse.eval_nil] using zero4034 B _hB _hF

theorem sound4035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4035 node4035Labels = Sparse.eval nodeValue4035 (mixedVector B) := by
  simpa only [nodeValue4035, Sparse.eval_nil] using zero4035 B _hB _hF

theorem sound4036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4036 node4036Labels = Sparse.eval nodeValue4036 (mixedVector B) := by
  simpa only [nodeValue4036, Sparse.eval_nil] using zero4036 B _hB _hF

theorem sound4037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4037 node4037Labels = Sparse.eval nodeValue4037 (mixedVector B) := by
  simpa only [nodeValue4037, Sparse.eval_nil] using zero4037 B _hB _hF

theorem sound4038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4038 node4038Labels = Sparse.eval nodeValue4038 (mixedVector B) := by
  simpa only [nodeValue4038, Sparse.eval_nil] using zero4038 B _hB _hF

theorem sound4039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4039 node4039Labels = Sparse.eval nodeValue4039 (mixedVector B) := by
  have h := singleton4039 B _hB
  rw [sound504 B _hB _hF] at h
  norm_num [nodeValue4039, nodeValue504, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4040 node4040Labels = Sparse.eval nodeValue4040 (mixedVector B) := by
  simpa only [nodeValue4040, Sparse.eval_nil] using zero4040 B _hB _hF

theorem sound4041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4041 node4041Labels = Sparse.eval nodeValue4041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4041) = mixedMoment B node4041 node4041Labels := rfl
  simpa [nodeValue4041, Sparse.eval] using hc.symm

theorem sound4042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4042 node4042Labels = Sparse.eval nodeValue4042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4042) = mixedMoment B node4042 node4042Labels := rfl
  simpa [nodeValue4042, Sparse.eval] using hc.symm

theorem sound4043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4043 node4043Labels = Sparse.eval nodeValue4043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4043) = mixedMoment B node4043 node4043Labels := rfl
  simpa [nodeValue4043, Sparse.eval] using hc.symm

theorem sound4044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4044 node4044Labels = Sparse.eval nodeValue4044 (mixedVector B) := by
  simpa only [nodeValue4044, Sparse.eval_nil] using zero4044 B _hB _hF

theorem sound4045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4045 node4045Labels = Sparse.eval nodeValue4045 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4045) = mixedMoment B node4045 node4045Labels := rfl
  simpa [nodeValue4045, Sparse.eval] using hc.symm

theorem sound4046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4046 node4046Labels = Sparse.eval nodeValue4046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4046) = mixedMoment B node4046 node4046Labels := rfl
  simpa [nodeValue4046, Sparse.eval] using hc.symm

theorem sound4047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4047 node4047Labels = Sparse.eval nodeValue4047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4047) = mixedMoment B node4047 node4047Labels := rfl
  simpa [nodeValue4047, Sparse.eval] using hc.symm

theorem sound4048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4048 node4048Labels = Sparse.eval nodeValue4048 (mixedVector B) := by
  simpa only [nodeValue4048, Sparse.eval_nil] using zero4048 B _hB _hF

theorem sound4049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4049 node4049Labels = Sparse.eval nodeValue4049 (mixedVector B) := by
  simpa only [nodeValue4049, Sparse.eval_nil] using zero4049 B _hB _hF

theorem sound4050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4050 node4050Labels = Sparse.eval nodeValue4050 (mixedVector B) := by
  have h := singleton4050 B _hB
  rw [sound526 B _hB _hF] at h
  norm_num [nodeValue4050, nodeValue526, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4051 node4051Labels = Sparse.eval nodeValue4051 (mixedVector B) := by
  have h := singleton4051 B _hB
  rw [sound531 B _hB _hF] at h
  norm_num [nodeValue4051, nodeValue531, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4052 node4052Labels = Sparse.eval nodeValue4052 (mixedVector B) := by
  simpa only [nodeValue4052, Sparse.eval_nil] using zero4052 B _hB _hF

theorem sound4053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4053 node4053Labels = Sparse.eval nodeValue4053 (mixedVector B) := by
  have h := singleton4053 B _hB
  rw [sound533 B _hB _hF] at h
  norm_num [nodeValue4053, nodeValue533, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4054 node4054Labels = Sparse.eval nodeValue4054 (mixedVector B) := by
  simpa only [nodeValue4054, Sparse.eval_nil] using zero4054 B _hB _hF

theorem sound4055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4055 node4055Labels = Sparse.eval nodeValue4055 (mixedVector B) := by
  simpa only [nodeValue4055, Sparse.eval_nil] using zero4055 B _hB _hF

theorem sound4056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4056 node4056Labels = Sparse.eval nodeValue4056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4056) = mixedMoment B node4056 node4056Labels := rfl
  simpa [nodeValue4056, Sparse.eval] using hc.symm

theorem sound4057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4057 node4057Labels = Sparse.eval nodeValue4057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4057) = mixedMoment B node4057 node4057Labels := rfl
  simpa [nodeValue4057, Sparse.eval] using hc.symm

theorem sound4058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4058 node4058Labels = Sparse.eval nodeValue4058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4058) = mixedMoment B node4058 node4058Labels := rfl
  simpa [nodeValue4058, Sparse.eval] using hc.symm

theorem sound4059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4059 node4059Labels = Sparse.eval nodeValue4059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4059) = mixedMoment B node4059 node4059Labels := rfl
  simpa [nodeValue4059, Sparse.eval] using hc.symm

theorem sound4060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4060 node4060Labels = Sparse.eval nodeValue4060 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4060) = mixedMoment B node4060 node4060Labels := rfl
  simpa [nodeValue4060, Sparse.eval] using hc.symm

theorem sound4061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4061 node4061Labels = Sparse.eval nodeValue4061 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4061) = mixedMoment B node4061 node4061Labels := rfl
  simpa [nodeValue4061, Sparse.eval] using hc.symm

theorem sound4062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4062 node4062Labels = Sparse.eval nodeValue4062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4062) = mixedMoment B node4062 node4062Labels := rfl
  simpa [nodeValue4062, Sparse.eval] using hc.symm

theorem sound4063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4063 node4063Labels = Sparse.eval nodeValue4063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4063) = mixedMoment B node4063 node4063Labels := rfl
  simpa [nodeValue4063, Sparse.eval] using hc.symm

theorem sound4064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4064 node4064Labels = Sparse.eval nodeValue4064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4064) = mixedMoment B node4064 node4064Labels := rfl
  simpa [nodeValue4064, Sparse.eval] using hc.symm

theorem sound4065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4065 node4065Labels = Sparse.eval nodeValue4065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4065) = mixedMoment B node4065 node4065Labels := rfl
  simpa [nodeValue4065, Sparse.eval] using hc.symm

theorem sound4066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4066 node4066Labels = Sparse.eval nodeValue4066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4066) = mixedMoment B node4066 node4066Labels := rfl
  simpa [nodeValue4066, Sparse.eval] using hc.symm

theorem sound4067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4067 node4067Labels = Sparse.eval nodeValue4067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4067) = mixedMoment B node4067 node4067Labels := rfl
  simpa [nodeValue4067, Sparse.eval] using hc.symm

theorem sound4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4068 node4068Labels = Sparse.eval nodeValue4068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4068) = mixedMoment B node4068 node4068Labels := rfl
  simpa [nodeValue4068, Sparse.eval] using hc.symm

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4072 node4072Labels = Sparse.eval nodeValue4072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4072) = mixedMoment B node4072 node4072Labels := rfl
  simpa [nodeValue4072, Sparse.eval] using hc.symm

theorem sound4073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4073 node4073Labels = Sparse.eval nodeValue4073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4073) = mixedMoment B node4073 node4073Labels := rfl
  simpa [nodeValue4073, Sparse.eval] using hc.symm

theorem sound4074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4074 node4074Labels = Sparse.eval nodeValue4074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4074) = mixedMoment B node4074 node4074Labels := rfl
  simpa [nodeValue4074, Sparse.eval] using hc.symm

theorem sound4075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4075 node4075Labels = Sparse.eval nodeValue4075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4075) = mixedMoment B node4075 node4075Labels := rfl
  simpa [nodeValue4075, Sparse.eval] using hc.symm

theorem sound4076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4076 node4076Labels = Sparse.eval nodeValue4076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4076) = mixedMoment B node4076 node4076Labels := rfl
  simpa [nodeValue4076, Sparse.eval] using hc.symm

theorem sound4077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4077 node4077Labels = Sparse.eval nodeValue4077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4077) = mixedMoment B node4077 node4077Labels := rfl
  simpa [nodeValue4077, Sparse.eval] using hc.symm

theorem sound4078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4078 node4078Labels = Sparse.eval nodeValue4078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4078) = mixedMoment B node4078 node4078Labels := rfl
  simpa [nodeValue4078, Sparse.eval] using hc.symm

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

theorem sound4086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4086 node4086Labels = Sparse.eval nodeValue4086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4086) = mixedMoment B node4086 node4086Labels := rfl
  simpa [nodeValue4086, Sparse.eval] using hc.symm

theorem sound4087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4087 node4087Labels = Sparse.eval nodeValue4087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4087) = mixedMoment B node4087 node4087Labels := rfl
  simpa [nodeValue4087, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

theorem sound4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4089 node4089Labels = Sparse.eval nodeValue4089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4089) = mixedMoment B node4089 node4089Labels := rfl
  simpa [nodeValue4089, Sparse.eval] using hc.symm

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

theorem sound4093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4093 node4093Labels = Sparse.eval nodeValue4093 (mixedVector B) := by
  have h := singleton4093 B _hB
  rw [sound5 B _hB _hF] at h
  norm_num [nodeValue4093, nodeValue5, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4094 node4094Labels = Sparse.eval nodeValue4094 (mixedVector B) := by
  have h := singleton4094 B _hB
  rw [sound6 B _hB _hF] at h
  norm_num [nodeValue4094, nodeValue6, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4095 node4095Labels = Sparse.eval nodeValue4095 (mixedVector B) := by
  simpa only [nodeValue4095, Sparse.eval_nil] using zero4095 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
