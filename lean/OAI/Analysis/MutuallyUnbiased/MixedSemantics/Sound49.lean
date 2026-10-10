import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons49

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3136 node3136Labels = Sparse.eval nodeValue3136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3136) = mixedMoment B node3136 node3136Labels := rfl
  simpa [nodeValue3136, Sparse.eval] using hc.symm

theorem sound3137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3137 node3137Labels = Sparse.eval nodeValue3137 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3137) = mixedMoment B node3137 node3137Labels := rfl
  simpa [nodeValue3137, Sparse.eval] using hc.symm

theorem sound3138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3138 node3138Labels = Sparse.eval nodeValue3138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3138) = mixedMoment B node3138 node3138Labels := rfl
  simpa [nodeValue3138, Sparse.eval] using hc.symm

theorem sound3139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3139 node3139Labels = Sparse.eval nodeValue3139 (mixedVector B) := by
  have h := singleton3139 B _hB
  rw [sound174 B _hB _hF] at h
  norm_num [nodeValue3139, nodeValue174, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3140 node3140Labels = Sparse.eval nodeValue3140 (mixedVector B) := by
  have h := singleton3140 B _hB
  rw [sound171 B _hB _hF] at h
  norm_num [nodeValue3140, nodeValue171, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3141 node3141Labels = Sparse.eval nodeValue3141 (mixedVector B) := by
  have h := singleton3141 B _hB
  rw [sound182 B _hB _hF] at h
  norm_num [nodeValue3141, nodeValue182, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3142 node3142Labels = Sparse.eval nodeValue3142 (mixedVector B) := by
  have h := singleton3142 B _hB
  rw [sound183 B _hB _hF] at h
  norm_num [nodeValue3142, nodeValue183, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3143 node3143Labels = Sparse.eval nodeValue3143 (mixedVector B) := by
  have h := singleton3143 B _hB
  rw [sound173 B _hB _hF] at h
  norm_num [nodeValue3143, nodeValue173, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3144 node3144Labels = Sparse.eval nodeValue3144 (mixedVector B) := by
  have h := singleton3144 B _hB
  rw [sound178 B _hB _hF] at h
  norm_num [nodeValue3144, nodeValue178, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3145 node3145Labels = Sparse.eval nodeValue3145 (mixedVector B) := by
  have h := singleton3145 B _hB
  rw [sound185 B _hB _hF] at h
  norm_num [nodeValue3145, nodeValue185, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3146 node3146Labels = Sparse.eval nodeValue3146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3146) = mixedMoment B node3146 node3146Labels := rfl
  simpa [nodeValue3146, Sparse.eval] using hc.symm

theorem sound3147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3147 node3147Labels = Sparse.eval nodeValue3147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3147) = mixedMoment B node3147 node3147Labels := rfl
  simpa [nodeValue3147, Sparse.eval] using hc.symm

theorem sound3148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3148 node3148Labels = Sparse.eval nodeValue3148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3148) = mixedMoment B node3148 node3148Labels := rfl
  simpa [nodeValue3148, Sparse.eval] using hc.symm

theorem sound3149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3149 node3149Labels = Sparse.eval nodeValue3149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3149) = mixedMoment B node3149 node3149Labels := rfl
  simpa [nodeValue3149, Sparse.eval] using hc.symm

theorem sound3150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3150 node3150Labels = Sparse.eval nodeValue3150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3150) = mixedMoment B node3150 node3150Labels := rfl
  simpa [nodeValue3150, Sparse.eval] using hc.symm

theorem sound3151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3151 node3151Labels = Sparse.eval nodeValue3151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3151) = mixedMoment B node3151 node3151Labels := rfl
  simpa [nodeValue3151, Sparse.eval] using hc.symm

theorem sound3152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3152 node3152Labels = Sparse.eval nodeValue3152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3152) = mixedMoment B node3152 node3152Labels := rfl
  simpa [nodeValue3152, Sparse.eval] using hc.symm

theorem sound3153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3153 node3153Labels = Sparse.eval nodeValue3153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3153) = mixedMoment B node3153 node3153Labels := rfl
  simpa [nodeValue3153, Sparse.eval] using hc.symm

theorem sound3154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3154 node3154Labels = Sparse.eval nodeValue3154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3154) = mixedMoment B node3154 node3154Labels := rfl
  simpa [nodeValue3154, Sparse.eval] using hc.symm

theorem sound3155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3155 node3155Labels = Sparse.eval nodeValue3155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3155) = mixedMoment B node3155 node3155Labels := rfl
  simpa [nodeValue3155, Sparse.eval] using hc.symm

theorem sound3156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3156 node3156Labels = Sparse.eval nodeValue3156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3156) = mixedMoment B node3156 node3156Labels := rfl
  simpa [nodeValue3156, Sparse.eval] using hc.symm

theorem sound3157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3157 node3157Labels = Sparse.eval nodeValue3157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3157) = mixedMoment B node3157 node3157Labels := rfl
  simpa [nodeValue3157, Sparse.eval] using hc.symm

theorem sound3158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3158 node3158Labels = Sparse.eval nodeValue3158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3158) = mixedMoment B node3158 node3158Labels := rfl
  simpa [nodeValue3158, Sparse.eval] using hc.symm

theorem sound3159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3159 node3159Labels = Sparse.eval nodeValue3159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3159) = mixedMoment B node3159 node3159Labels := rfl
  simpa [nodeValue3159, Sparse.eval] using hc.symm

theorem sound3160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3160 node3160Labels = Sparse.eval nodeValue3160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3160) = mixedMoment B node3160 node3160Labels := rfl
  simpa [nodeValue3160, Sparse.eval] using hc.symm

theorem sound3161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3161 node3161Labels = Sparse.eval nodeValue3161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3161) = mixedMoment B node3161 node3161Labels := rfl
  simpa [nodeValue3161, Sparse.eval] using hc.symm

theorem sound3162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3162 node3162Labels = Sparse.eval nodeValue3162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3162) = mixedMoment B node3162 node3162Labels := rfl
  simpa [nodeValue3162, Sparse.eval] using hc.symm

theorem sound3163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3163 node3163Labels = Sparse.eval nodeValue3163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3163) = mixedMoment B node3163 node3163Labels := rfl
  simpa [nodeValue3163, Sparse.eval] using hc.symm

theorem sound3164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3164 node3164Labels = Sparse.eval nodeValue3164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3164) = mixedMoment B node3164 node3164Labels := rfl
  simpa [nodeValue3164, Sparse.eval] using hc.symm

theorem sound3165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3165 node3165Labels = Sparse.eval nodeValue3165 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3165) = mixedMoment B node3165 node3165Labels := rfl
  simpa [nodeValue3165, Sparse.eval] using hc.symm

theorem sound3166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3166 node3166Labels = Sparse.eval nodeValue3166 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3166) = mixedMoment B node3166 node3166Labels := rfl
  simpa [nodeValue3166, Sparse.eval] using hc.symm

theorem sound3167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3167 node3167Labels = Sparse.eval nodeValue3167 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3167) = mixedMoment B node3167 node3167Labels := rfl
  simpa [nodeValue3167, Sparse.eval] using hc.symm

theorem sound3168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3168 node3168Labels = Sparse.eval nodeValue3168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3168) = mixedMoment B node3168 node3168Labels := rfl
  simpa [nodeValue3168, Sparse.eval] using hc.symm

theorem sound3169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3169 node3169Labels = Sparse.eval nodeValue3169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3169) = mixedMoment B node3169 node3169Labels := rfl
  simpa [nodeValue3169, Sparse.eval] using hc.symm

theorem sound3170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3170 node3170Labels = Sparse.eval nodeValue3170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3170) = mixedMoment B node3170 node3170Labels := rfl
  simpa [nodeValue3170, Sparse.eval] using hc.symm

theorem sound3171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3171 node3171Labels = Sparse.eval nodeValue3171 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3171) = mixedMoment B node3171 node3171Labels := rfl
  simpa [nodeValue3171, Sparse.eval] using hc.symm

theorem sound3172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3172 node3172Labels = Sparse.eval nodeValue3172 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3172) = mixedMoment B node3172 node3172Labels := rfl
  simpa [nodeValue3172, Sparse.eval] using hc.symm

theorem sound3173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3173 node3173Labels = Sparse.eval nodeValue3173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3173) = mixedMoment B node3173 node3173Labels := rfl
  simpa [nodeValue3173, Sparse.eval] using hc.symm

theorem sound3174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3174 node3174Labels = Sparse.eval nodeValue3174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3174) = mixedMoment B node3174 node3174Labels := rfl
  simpa [nodeValue3174, Sparse.eval] using hc.symm

theorem sound3175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3175 node3175Labels = Sparse.eval nodeValue3175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3175) = mixedMoment B node3175 node3175Labels := rfl
  simpa [nodeValue3175, Sparse.eval] using hc.symm

theorem sound3176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3176 node3176Labels = Sparse.eval nodeValue3176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3176) = mixedMoment B node3176 node3176Labels := rfl
  simpa [nodeValue3176, Sparse.eval] using hc.symm

theorem sound3177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3177 node3177Labels = Sparse.eval nodeValue3177 (mixedVector B) := by
  have h := singleton3177 B _hB
  rw [sound219 B _hB _hF] at h
  norm_num [nodeValue3177, nodeValue219, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3178 node3178Labels = Sparse.eval nodeValue3178 (mixedVector B) := by
  have h := singleton3178 B _hB
  rw [sound231 B _hB _hF] at h
  norm_num [nodeValue3178, nodeValue231, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3179 node3179Labels = Sparse.eval nodeValue3179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3179) = mixedMoment B node3179 node3179Labels := rfl
  simpa [nodeValue3179, Sparse.eval] using hc.symm

theorem sound3180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3180 node3180Labels = Sparse.eval nodeValue3180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3180) = mixedMoment B node3180 node3180Labels := rfl
  simpa [nodeValue3180, Sparse.eval] using hc.symm

theorem sound3181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3181 node3181Labels = Sparse.eval nodeValue3181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3181) = mixedMoment B node3181 node3181Labels := rfl
  simpa [nodeValue3181, Sparse.eval] using hc.symm

theorem sound3182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3182 node3182Labels = Sparse.eval nodeValue3182 (mixedVector B) := by
  have h := singleton3182 B _hB
  rw [sound243 B _hB _hF] at h
  norm_num [nodeValue3182, nodeValue243, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3183 node3183Labels = Sparse.eval nodeValue3183 (mixedVector B) := by
  have h := singleton3183 B _hB
  rw [sound248 B _hB _hF] at h
  norm_num [nodeValue3183, nodeValue248, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3184 node3184Labels = Sparse.eval nodeValue3184 (mixedVector B) := by
  have h := singleton3184 B _hB
  rw [sound245 B _hB _hF] at h
  norm_num [nodeValue3184, nodeValue245, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3185 node3185Labels = Sparse.eval nodeValue3185 (mixedVector B) := by
  have h := singleton3185 B _hB
  rw [sound244 B _hB _hF] at h
  norm_num [nodeValue3185, nodeValue244, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3186 node3186Labels = Sparse.eval nodeValue3186 (mixedVector B) := by
  have h := singleton3186 B _hB
  rw [sound241 B _hB _hF] at h
  norm_num [nodeValue3186, nodeValue241, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3187 node3187Labels = Sparse.eval nodeValue3187 (mixedVector B) := by
  have h := singleton3187 B _hB
  rw [sound251 B _hB _hF] at h
  norm_num [nodeValue3187, nodeValue251, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3188 node3188Labels = Sparse.eval nodeValue3188 (mixedVector B) := by
  have h := singleton3188 B _hB
  rw [sound252 B _hB _hF] at h
  norm_num [nodeValue3188, nodeValue252, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3189 node3189Labels = Sparse.eval nodeValue3189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3189) = mixedMoment B node3189 node3189Labels := rfl
  simpa [nodeValue3189, Sparse.eval] using hc.symm

theorem sound3190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3190 node3190Labels = Sparse.eval nodeValue3190 (mixedVector B) := by
  have h := singleton3190 B _hB
  rw [sound209 B _hB _hF] at h
  norm_num [nodeValue3190, nodeValue209, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3191 node3191Labels = Sparse.eval nodeValue3191 (mixedVector B) := by
  have h := singleton3191 B _hB
  rw [sound210 B _hB _hF] at h
  norm_num [nodeValue3191, nodeValue210, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3192 node3192Labels = Sparse.eval nodeValue3192 (mixedVector B) := by
  have h := singleton3192 B _hB
  rw [sound205 B _hB _hF] at h
  norm_num [nodeValue3192, nodeValue205, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3193 node3193Labels = Sparse.eval nodeValue3193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3193) = mixedMoment B node3193 node3193Labels := rfl
  simpa [nodeValue3193, Sparse.eval] using hc.symm

theorem sound3194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3194 node3194Labels = Sparse.eval nodeValue3194 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3194) = mixedMoment B node3194 node3194Labels := rfl
  simpa [nodeValue3194, Sparse.eval] using hc.symm

theorem sound3195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3195 node3195Labels = Sparse.eval nodeValue3195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3195) = mixedMoment B node3195 node3195Labels := rfl
  simpa [nodeValue3195, Sparse.eval] using hc.symm

theorem sound3196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3196 node3196Labels = Sparse.eval nodeValue3196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3196) = mixedMoment B node3196 node3196Labels := rfl
  simpa [nodeValue3196, Sparse.eval] using hc.symm

theorem sound3197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3197 node3197Labels = Sparse.eval nodeValue3197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3197) = mixedMoment B node3197 node3197Labels := rfl
  simpa [nodeValue3197, Sparse.eval] using hc.symm

theorem sound3198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3198 node3198Labels = Sparse.eval nodeValue3198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3198) = mixedMoment B node3198 node3198Labels := rfl
  simpa [nodeValue3198, Sparse.eval] using hc.symm

theorem sound3199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3199 node3199Labels = Sparse.eval nodeValue3199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3199) = mixedMoment B node3199 node3199Labels := rfl
  simpa [nodeValue3199, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
