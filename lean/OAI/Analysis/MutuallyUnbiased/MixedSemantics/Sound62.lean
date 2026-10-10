import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons62

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3968 node3968Labels = Sparse.eval nodeValue3968 (mixedVector B) := by
  simpa only [nodeValue3968, Sparse.eval_nil] using zero3968 B _hB _hF

theorem sound3969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3969 node3969Labels = Sparse.eval nodeValue3969 (mixedVector B) := by
  have h := singleton3969 B _hB
  rw [sound511 B _hB _hF] at h
  norm_num [nodeValue3969, nodeValue511, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3970 node3970Labels = Sparse.eval nodeValue3970 (mixedVector B) := by
  have h := singleton3970 B _hB
  rw [sound454 B _hB _hF] at h
  norm_num [nodeValue3970, nodeValue454, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3971 node3971Labels = Sparse.eval nodeValue3971 (mixedVector B) := by
  simpa only [nodeValue3971, Sparse.eval_nil] using zero3971 B _hB _hF

theorem sound3972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3972 node3972Labels = Sparse.eval nodeValue3972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3972) = mixedMoment B node3972 node3972Labels := rfl
  simpa [nodeValue3972, Sparse.eval] using hc.symm

theorem sound3973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3973 node3973Labels = Sparse.eval nodeValue3973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3973) = mixedMoment B node3973 node3973Labels := rfl
  simpa [nodeValue3973, Sparse.eval] using hc.symm

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

theorem sound3975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3975 node3975Labels = Sparse.eval nodeValue3975 (mixedVector B) := by
  simpa only [nodeValue3975, Sparse.eval_nil] using zero3975 B _hB _hF

theorem sound3976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3976 node3976Labels = Sparse.eval nodeValue3976 (mixedVector B) := by
  simpa only [nodeValue3976, Sparse.eval_nil] using zero3976 B _hB _hF

theorem sound3977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3977 node3977Labels = Sparse.eval nodeValue3977 (mixedVector B) := by
  have h := singleton3977 B _hB
  rw [sound461 B _hB _hF] at h
  norm_num [nodeValue3977, nodeValue461, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3978 node3978Labels = Sparse.eval nodeValue3978 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3978) = mixedMoment B node3978 node3978Labels := rfl
  simpa [nodeValue3978, Sparse.eval] using hc.symm

theorem sound3979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3979 node3979Labels = Sparse.eval nodeValue3979 (mixedVector B) := by
  simpa only [nodeValue3979, Sparse.eval_nil] using zero3979 B _hB _hF

theorem sound3980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3980 node3980Labels = Sparse.eval nodeValue3980 (mixedVector B) := by
  have h := singleton3980 B _hB
  rw [sound520 B _hB _hF] at h
  norm_num [nodeValue3980, nodeValue520, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3981 node3981Labels = Sparse.eval nodeValue3981 (mixedVector B) := by
  have h := singleton3981 B _hB
  rw [sound521 B _hB _hF] at h
  norm_num [nodeValue3981, nodeValue521, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3982 node3982Labels = Sparse.eval nodeValue3982 (mixedVector B) := by
  have h := singleton3982 B _hB
  rw [sound489 B _hB _hF] at h
  norm_num [nodeValue3982, nodeValue489, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

theorem sound3984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3984 node3984Labels = Sparse.eval nodeValue3984 (mixedVector B) := by
  have h := singleton3984 B _hB
  rw [sound523 B _hB _hF] at h
  norm_num [nodeValue3984, nodeValue523, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3985 node3985Labels = Sparse.eval nodeValue3985 (mixedVector B) := by
  simpa only [nodeValue3985, Sparse.eval_nil] using zero3985 B _hB _hF

theorem sound3986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3986 node3986Labels = Sparse.eval nodeValue3986 (mixedVector B) := by
  simpa only [nodeValue3986, Sparse.eval_nil] using zero3986 B _hB _hF

theorem sound3987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3987 node3987Labels = Sparse.eval nodeValue3987 (mixedVector B) := by
  have h := singleton3987 B _hB
  rw [sound503 B _hB _hF] at h
  norm_num [nodeValue3987, nodeValue503, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3988 node3988Labels = Sparse.eval nodeValue3988 (mixedVector B) := by
  simpa only [nodeValue3988, Sparse.eval_nil] using zero3988 B _hB _hF

theorem sound3989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3989 node3989Labels = Sparse.eval nodeValue3989 (mixedVector B) := by
  simpa only [nodeValue3989, Sparse.eval_nil] using zero3989 B _hB _hF

theorem sound3990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3990 node3990Labels = Sparse.eval nodeValue3990 (mixedVector B) := by
  have h := singleton3990 B _hB
  rw [sound479 B _hB _hF] at h
  norm_num [nodeValue3990, nodeValue479, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3991 node3991Labels = Sparse.eval nodeValue3991 (mixedVector B) := by
  simpa only [nodeValue3991, Sparse.eval_nil] using zero3991 B _hB _hF

theorem sound3992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3992 node3992Labels = Sparse.eval nodeValue3992 (mixedVector B) := by
  have h := singleton3992 B _hB
  rw [sound520 B _hB _hF] at h
  norm_num [nodeValue3992, nodeValue520, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3993 node3993Labels = Sparse.eval nodeValue3993 (mixedVector B) := by
  have h := singleton3993 B _hB
  rw [sound493 B _hB _hF] at h
  norm_num [nodeValue3993, nodeValue493, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3994 node3994Labels = Sparse.eval nodeValue3994 (mixedVector B) := by
  have h := singleton3994 B _hB
  rw [sound519 B _hB _hF] at h
  norm_num [nodeValue3994, nodeValue519, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3995 node3995Labels = Sparse.eval nodeValue3995 (mixedVector B) := by
  have h := singleton3995 B _hB
  rw [sound514 B _hB _hF] at h
  norm_num [nodeValue3995, nodeValue514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3996 node3996Labels = Sparse.eval nodeValue3996 (mixedVector B) := by
  simpa only [nodeValue3996, Sparse.eval_nil] using zero3996 B _hB _hF

theorem sound3997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3997 node3997Labels = Sparse.eval nodeValue3997 (mixedVector B) := by
  have h := singleton3997 B _hB
  rw [sound522 B _hB _hF] at h
  norm_num [nodeValue3997, nodeValue522, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3998 node3998Labels = Sparse.eval nodeValue3998 (mixedVector B) := by
  have h := singleton3998 B _hB
  rw [sound523 B _hB _hF] at h
  norm_num [nodeValue3998, nodeValue523, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3999 node3999Labels = Sparse.eval nodeValue3999 (mixedVector B) := by
  simpa only [nodeValue3999, Sparse.eval_nil] using zero3999 B _hB _hF

theorem sound4000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4000 node4000Labels = Sparse.eval nodeValue4000 (mixedVector B) := by
  simpa only [nodeValue4000, Sparse.eval_nil] using zero4000 B _hB _hF

theorem sound4001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4001 node4001Labels = Sparse.eval nodeValue4001 (mixedVector B) := by
  simpa only [nodeValue4001, Sparse.eval_nil] using zero4001 B _hB _hF

theorem sound4002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4002 node4002Labels = Sparse.eval nodeValue4002 (mixedVector B) := by
  have h := singleton4002 B _hB
  rw [sound513 B _hB _hF] at h
  norm_num [nodeValue4002, nodeValue513, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4003 node4003Labels = Sparse.eval nodeValue4003 (mixedVector B) := by
  have h := singleton4003 B _hB
  rw [sound483 B _hB _hF] at h
  norm_num [nodeValue4003, nodeValue483, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4004 node4004Labels = Sparse.eval nodeValue4004 (mixedVector B) := by
  have h := singleton4004 B _hB
  rw [sound516 B _hB _hF] at h
  norm_num [nodeValue4004, nodeValue516, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4005 node4005Labels = Sparse.eval nodeValue4005 (mixedVector B) := by
  simpa only [nodeValue4005, Sparse.eval_nil] using zero4005 B _hB _hF

theorem sound4006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4006 node4006Labels = Sparse.eval nodeValue4006 (mixedVector B) := by
  simpa only [nodeValue4006, Sparse.eval_nil] using zero4006 B _hB _hF

theorem sound4007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4007 node4007Labels = Sparse.eval nodeValue4007 (mixedVector B) := by
  simpa only [nodeValue4007, Sparse.eval_nil] using zero4007 B _hB _hF

theorem sound4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4008 node4008Labels = Sparse.eval nodeValue4008 (mixedVector B) := by
  simpa only [nodeValue4008, Sparse.eval_nil] using zero4008 B _hB _hF

theorem sound4009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4009 node4009Labels = Sparse.eval nodeValue4009 (mixedVector B) := by
  simpa only [nodeValue4009, Sparse.eval_nil] using zero4009 B _hB _hF

theorem sound4010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4010 node4010Labels = Sparse.eval nodeValue4010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4010) = mixedMoment B node4010 node4010Labels := rfl
  simpa [nodeValue4010, Sparse.eval] using hc.symm

theorem sound4011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4011 node4011Labels = Sparse.eval nodeValue4011 (mixedVector B) := by
  simpa only [nodeValue4011, Sparse.eval_nil] using zero4011 B _hB _hF

theorem sound4012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4012 node4012Labels = Sparse.eval nodeValue4012 (mixedVector B) := by
  have h := singleton4012 B _hB
  rw [sound494 B _hB _hF] at h
  norm_num [nodeValue4012, nodeValue494, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4013 node4013Labels = Sparse.eval nodeValue4013 (mixedVector B) := by
  have h := singleton4013 B _hB
  rw [sound526 B _hB _hF] at h
  norm_num [nodeValue4013, nodeValue526, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4014 node4014Labels = Sparse.eval nodeValue4014 (mixedVector B) := by
  have h := singleton4014 B _hB
  rw [sound527 B _hB _hF] at h
  norm_num [nodeValue4014, nodeValue527, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4015 node4015Labels = Sparse.eval nodeValue4015 (mixedVector B) := by
  have h := singleton4015 B _hB
  rw [sound528 B _hB _hF] at h
  norm_num [nodeValue4015, nodeValue528, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4016 node4016Labels = Sparse.eval nodeValue4016 (mixedVector B) := by
  simpa only [nodeValue4016, Sparse.eval_nil] using zero4016 B _hB _hF

theorem sound4017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4017 node4017Labels = Sparse.eval nodeValue4017 (mixedVector B) := by
  have h := singleton4017 B _hB
  rw [sound528 B _hB _hF] at h
  norm_num [nodeValue4017, nodeValue528, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4018 node4018Labels = Sparse.eval nodeValue4018 (mixedVector B) := by
  simpa only [nodeValue4018, Sparse.eval_nil] using zero4018 B _hB _hF

theorem sound4019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4019 node4019Labels = Sparse.eval nodeValue4019 (mixedVector B) := by
  simpa only [nodeValue4019, Sparse.eval_nil] using zero4019 B _hB _hF

theorem sound4020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4020 node4020Labels = Sparse.eval nodeValue4020 (mixedVector B) := by
  have h := singleton4020 B _hB
  rw [sound530 B _hB _hF] at h
  norm_num [nodeValue4020, nodeValue530, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4021 node4021Labels = Sparse.eval nodeValue4021 (mixedVector B) := by
  simpa only [nodeValue4021, Sparse.eval_nil] using zero4021 B _hB _hF

theorem sound4022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4022 node4022Labels = Sparse.eval nodeValue4022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4022) = mixedMoment B node4022 node4022Labels := rfl
  simpa [nodeValue4022, Sparse.eval] using hc.symm

theorem sound4023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4023 node4023Labels = Sparse.eval nodeValue4023 (mixedVector B) := by
  have h := singleton4023 B _hB
  rw [sound456 B _hB _hF] at h
  norm_num [nodeValue4023, nodeValue456, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4024 node4024Labels = Sparse.eval nodeValue4024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4024) = mixedMoment B node4024 node4024Labels := rfl
  simpa [nodeValue4024, Sparse.eval] using hc.symm

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

theorem sound4026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4026 node4026Labels = Sparse.eval nodeValue4026 (mixedVector B) := by
  have h := singleton4026 B _hB
  rw [sound486 B _hB _hF] at h
  norm_num [nodeValue4026, nodeValue486, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4027 node4027Labels = Sparse.eval nodeValue4027 (mixedVector B) := by
  have h := singleton4027 B _hB
  rw [sound487 B _hB _hF] at h
  norm_num [nodeValue4027, nodeValue487, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4028 node4028Labels = Sparse.eval nodeValue4028 (mixedVector B) := by
  have h := singleton4028 B _hB
  rw [sound500 B _hB _hF] at h
  norm_num [nodeValue4028, nodeValue500, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4029 node4029Labels = Sparse.eval nodeValue4029 (mixedVector B) := by
  have h := singleton4029 B _hB
  rw [sound502 B _hB _hF] at h
  norm_num [nodeValue4029, nodeValue502, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4030 node4030Labels = Sparse.eval nodeValue4030 (mixedVector B) := by
  have h := singleton4030 B _hB
  rw [sound501 B _hB _hF] at h
  norm_num [nodeValue4030, nodeValue501, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4031 node4031Labels = Sparse.eval nodeValue4031 (mixedVector B) := by
  have h := singleton4031 B _hB
  rw [sound471 B _hB _hF] at h
  norm_num [nodeValue4031, nodeValue471, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
