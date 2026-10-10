import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons48

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3072 node3072Labels = Sparse.eval nodeValue3072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3072) = mixedMoment B node3072 node3072Labels := rfl
  simpa [nodeValue3072, Sparse.eval] using hc.symm

theorem sound3073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3073 node3073Labels = Sparse.eval nodeValue3073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3073) = mixedMoment B node3073 node3073Labels := rfl
  simpa [nodeValue3073, Sparse.eval] using hc.symm

theorem sound3074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3074 node3074Labels = Sparse.eval nodeValue3074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3074) = mixedMoment B node3074 node3074Labels := rfl
  simpa [nodeValue3074, Sparse.eval] using hc.symm

theorem sound3075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3075 node3075Labels = Sparse.eval nodeValue3075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3075) = mixedMoment B node3075 node3075Labels := rfl
  simpa [nodeValue3075, Sparse.eval] using hc.symm

theorem sound3076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3076 node3076Labels = Sparse.eval nodeValue3076 (mixedVector B) := by
  simpa only [nodeValue3076, Sparse.eval_nil] using zero3076 B _hB _hF

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3078 node3078Labels = Sparse.eval nodeValue3078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3078) = mixedMoment B node3078 node3078Labels := rfl
  simpa [nodeValue3078, Sparse.eval] using hc.symm

theorem sound3079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3079 node3079Labels = Sparse.eval nodeValue3079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3079) = mixedMoment B node3079 node3079Labels := rfl
  simpa [nodeValue3079, Sparse.eval] using hc.symm

theorem sound3080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3080 node3080Labels = Sparse.eval nodeValue3080 (mixedVector B) := by
  simpa only [nodeValue3080, Sparse.eval_nil] using zero3080 B _hB _hF

theorem sound3081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3081 node3081Labels = Sparse.eval nodeValue3081 (mixedVector B) := by
  have h := singleton3081 B _hB
  rw [sound370 B _hB _hF] at h
  norm_num [nodeValue3081, nodeValue370, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3082 node3082Labels = Sparse.eval nodeValue3082 (mixedVector B) := by
  have h := singleton3082 B _hB
  rw [sound233 B _hB _hF] at h
  norm_num [nodeValue3082, nodeValue233, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3083 node3083Labels = Sparse.eval nodeValue3083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3083) = mixedMoment B node3083 node3083Labels := rfl
  simpa [nodeValue3083, Sparse.eval] using hc.symm

theorem sound3084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3084 node3084Labels = Sparse.eval nodeValue3084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3084) = mixedMoment B node3084 node3084Labels := rfl
  simpa [nodeValue3084, Sparse.eval] using hc.symm

theorem sound3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = Sparse.eval nodeValue3085 (mixedVector B) := by
  simpa only [nodeValue3085, Sparse.eval_nil] using zero3085 B _hB _hF

theorem sound3086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3086 node3086Labels = Sparse.eval nodeValue3086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3086) = mixedMoment B node3086 node3086Labels := rfl
  simpa [nodeValue3086, Sparse.eval] using hc.symm

theorem sound3087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3087 node3087Labels = Sparse.eval nodeValue3087 (mixedVector B) := by
  have h := singleton3087 B _hB
  rw [sound376 B _hB _hF] at h
  norm_num [nodeValue3087, nodeValue376, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3088 node3088Labels = Sparse.eval nodeValue3088 (mixedVector B) := by
  have h := singleton3088 B _hB
  rw [sound378 B _hB _hF] at h
  norm_num [nodeValue3088, nodeValue378, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3089 node3089Labels = Sparse.eval nodeValue3089 (mixedVector B) := by
  have h := singleton3089 B _hB
  rw [sound377 B _hB _hF] at h
  norm_num [nodeValue3089, nodeValue377, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3090 node3090Labels = Sparse.eval nodeValue3090 (mixedVector B) := by
  have h := singleton3090 B _hB
  rw [sound379 B _hB _hF] at h
  norm_num [nodeValue3090, nodeValue379, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3091 node3091Labels = Sparse.eval nodeValue3091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3091) = mixedMoment B node3091 node3091Labels := rfl
  simpa [nodeValue3091, Sparse.eval] using hc.symm

theorem sound3092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3092 node3092Labels = Sparse.eval nodeValue3092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3092) = mixedMoment B node3092 node3092Labels := rfl
  simpa [nodeValue3092, Sparse.eval] using hc.symm

theorem sound3093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3093 node3093Labels = Sparse.eval nodeValue3093 (mixedVector B) := by
  have h := singleton3093 B _hB
  rw [sound360 B _hB _hF] at h
  norm_num [nodeValue3093, nodeValue360, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3094 node3094Labels = Sparse.eval nodeValue3094 (mixedVector B) := by
  have h := singleton3094 B _hB
  rw [sound361 B _hB _hF] at h
  norm_num [nodeValue3094, nodeValue361, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3095 node3095Labels = Sparse.eval nodeValue3095 (mixedVector B) := by
  have h := singleton3095 B _hB
  rw [sound237 B _hB _hF] at h
  norm_num [nodeValue3095, nodeValue237, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3096 node3096Labels = Sparse.eval nodeValue3096 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3096) = mixedMoment B node3096 node3096Labels := rfl
  simpa [nodeValue3096, Sparse.eval] using hc.symm

theorem sound3097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3097 node3097Labels = Sparse.eval nodeValue3097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3097) = mixedMoment B node3097 node3097Labels := rfl
  simpa [nodeValue3097, Sparse.eval] using hc.symm

theorem sound3098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3098 node3098Labels = Sparse.eval nodeValue3098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3098) = mixedMoment B node3098 node3098Labels := rfl
  simpa [nodeValue3098, Sparse.eval] using hc.symm

theorem sound3099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3099 node3099Labels = Sparse.eval nodeValue3099 (mixedVector B) := by
  have h := singleton3099 B _hB
  rw [sound401 B _hB _hF] at h
  norm_num [nodeValue3099, nodeValue401, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3100 node3100Labels = Sparse.eval nodeValue3100 (mixedVector B) := by
  have h := singleton3100 B _hB
  rw [sound403 B _hB _hF] at h
  norm_num [nodeValue3100, nodeValue403, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3101 node3101Labels = Sparse.eval nodeValue3101 (mixedVector B) := by
  have h := singleton3101 B _hB
  rw [sound405 B _hB _hF] at h
  norm_num [nodeValue3101, nodeValue405, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3102 node3102Labels = Sparse.eval nodeValue3102 (mixedVector B) := by
  have h := singleton3102 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue3102, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3103 node3103Labels = Sparse.eval nodeValue3103 (mixedVector B) := by
  have h := singleton3103 B _hB
  rw [sound402 B _hB _hF] at h
  norm_num [nodeValue3103, nodeValue402, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3104 node3104Labels = Sparse.eval nodeValue3104 (mixedVector B) := by
  simpa only [nodeValue3104, Sparse.eval_nil] using zero3104 B _hB _hF

theorem sound3105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3105 node3105Labels = Sparse.eval nodeValue3105 (mixedVector B) := by
  have h := singleton3105 B _hB
  rw [sound371 B _hB _hF] at h
  norm_num [nodeValue3105, nodeValue371, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3106 node3106Labels = Sparse.eval nodeValue3106 (mixedVector B) := by
  have h := singleton3106 B _hB
  rw [sound372 B _hB _hF] at h
  norm_num [nodeValue3106, nodeValue372, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3107 node3107Labels = Sparse.eval nodeValue3107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3107) = mixedMoment B node3107 node3107Labels := rfl
  simpa [nodeValue3107, Sparse.eval] using hc.symm

theorem sound3108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3108 node3108Labels = Sparse.eval nodeValue3108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3108) = mixedMoment B node3108 node3108Labels := rfl
  simpa [nodeValue3108, Sparse.eval] using hc.symm

theorem sound3109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3109 node3109Labels = Sparse.eval nodeValue3109 (mixedVector B) := by
  have h := singleton3109 B _hB
  rw [sound387 B _hB _hF] at h
  norm_num [nodeValue3109, nodeValue387, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3110 node3110Labels = Sparse.eval nodeValue3110 (mixedVector B) := by
  have h := singleton3110 B _hB
  rw [sound390 B _hB _hF] at h
  norm_num [nodeValue3110, nodeValue390, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3111 node3111Labels = Sparse.eval nodeValue3111 (mixedVector B) := by
  simpa only [nodeValue3111, Sparse.eval_nil] using zero3111 B _hB _hF

theorem sound3112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3112 node3112Labels = Sparse.eval nodeValue3112 (mixedVector B) := by
  simpa only [nodeValue3112, Sparse.eval_nil] using zero3112 B _hB _hF

theorem sound3113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3113 node3113Labels = Sparse.eval nodeValue3113 (mixedVector B) := by
  have h := singleton3113 B _hB
  rw [sound388 B _hB _hF] at h
  norm_num [nodeValue3113, nodeValue388, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3114 node3114Labels = Sparse.eval nodeValue3114 (mixedVector B) := by
  simpa only [nodeValue3114, Sparse.eval_nil] using zero3114 B _hB _hF

theorem sound3115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3115 node3115Labels = Sparse.eval nodeValue3115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3115) = mixedMoment B node3115 node3115Labels := rfl
  simpa [nodeValue3115, Sparse.eval] using hc.symm

theorem sound3116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3116 node3116Labels = Sparse.eval nodeValue3116 (mixedVector B) := by
  have h := singleton3116 B _hB
  rw [sound368 B _hB _hF] at h
  norm_num [nodeValue3116, nodeValue368, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3117 node3117Labels = Sparse.eval nodeValue3117 (mixedVector B) := by
  have h := singleton3117 B _hB
  rw [sound369 B _hB _hF] at h
  norm_num [nodeValue3117, nodeValue369, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3118 node3118Labels = Sparse.eval nodeValue3118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3118) = mixedMoment B node3118 node3118Labels := rfl
  simpa [nodeValue3118, Sparse.eval] using hc.symm

theorem sound3119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3119 node3119Labels = Sparse.eval nodeValue3119 (mixedVector B) := by
  have h := singleton3119 B _hB
  rw [sound414 B _hB _hF] at h
  norm_num [nodeValue3119, nodeValue414, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3120 node3120Labels = Sparse.eval nodeValue3120 (mixedVector B) := by
  have h := singleton3120 B _hB
  rw [sound416 B _hB _hF] at h
  norm_num [nodeValue3120, nodeValue416, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3121 node3121Labels = Sparse.eval nodeValue3121 (mixedVector B) := by
  have h := singleton3121 B _hB
  rw [sound420 B _hB _hF] at h
  norm_num [nodeValue3121, nodeValue420, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3122 node3122Labels = Sparse.eval nodeValue3122 (mixedVector B) := by
  simpa only [nodeValue3122, Sparse.eval_nil] using zero3122 B _hB _hF

theorem sound3123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3123 node3123Labels = Sparse.eval nodeValue3123 (mixedVector B) := by
  simpa only [nodeValue3123, Sparse.eval_nil] using zero3123 B _hB _hF

theorem sound3124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3124 node3124Labels = Sparse.eval nodeValue3124 (mixedVector B) := by
  simpa only [nodeValue3124, Sparse.eval_nil] using zero3124 B _hB _hF

theorem sound3125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3125 node3125Labels = Sparse.eval nodeValue3125 (mixedVector B) := by
  have h := singleton3125 B _hB
  rw [sound415 B _hB _hF] at h
  norm_num [nodeValue3125, nodeValue415, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3126 node3126Labels = Sparse.eval nodeValue3126 (mixedVector B) := by
  simpa only [nodeValue3126, Sparse.eval_nil] using zero3126 B _hB _hF

theorem sound3127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3127 node3127Labels = Sparse.eval nodeValue3127 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3127) = mixedMoment B node3127 node3127Labels := rfl
  simpa [nodeValue3127, Sparse.eval] using hc.symm

theorem sound3128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3128 node3128Labels = Sparse.eval nodeValue3128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3128) = mixedMoment B node3128 node3128Labels := rfl
  simpa [nodeValue3128, Sparse.eval] using hc.symm

theorem sound3129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3129 node3129Labels = Sparse.eval nodeValue3129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3129) = mixedMoment B node3129 node3129Labels := rfl
  simpa [nodeValue3129, Sparse.eval] using hc.symm

theorem sound3130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3130 node3130Labels = Sparse.eval nodeValue3130 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3130) = mixedMoment B node3130 node3130Labels := rfl
  simpa [nodeValue3130, Sparse.eval] using hc.symm

theorem sound3131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3131 node3131Labels = Sparse.eval nodeValue3131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3131) = mixedMoment B node3131 node3131Labels := rfl
  simpa [nodeValue3131, Sparse.eval] using hc.symm

theorem sound3132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3132 node3132Labels = Sparse.eval nodeValue3132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3132) = mixedMoment B node3132 node3132Labels := rfl
  simpa [nodeValue3132, Sparse.eval] using hc.symm

theorem sound3133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3133 node3133Labels = Sparse.eval nodeValue3133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3133) = mixedMoment B node3133 node3133Labels := rfl
  simpa [nodeValue3133, Sparse.eval] using hc.symm

theorem sound3134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3134 node3134Labels = Sparse.eval nodeValue3134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3134) = mixedMoment B node3134 node3134Labels := rfl
  simpa [nodeValue3134, Sparse.eval] using hc.symm

theorem sound3135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3135 node3135Labels = Sparse.eval nodeValue3135 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3135) = mixedMoment B node3135 node3135Labels := rfl
  simpa [nodeValue3135, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
