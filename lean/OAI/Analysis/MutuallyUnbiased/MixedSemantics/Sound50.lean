import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons50

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3200 node3200Labels = Sparse.eval nodeValue3200 (mixedVector B) := by
  have h := singleton3200 B _hB
  rw [sound215 B _hB _hF] at h
  norm_num [nodeValue3200, nodeValue215, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3201 node3201Labels = Sparse.eval nodeValue3201 (mixedVector B) := by
  have h := singleton3201 B _hB
  rw [sound217 B _hB _hF] at h
  norm_num [nodeValue3201, nodeValue217, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3202 node3202Labels = Sparse.eval nodeValue3202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3202) = mixedMoment B node3202 node3202Labels := rfl
  simpa [nodeValue3202, Sparse.eval] using hc.symm

theorem sound3203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3203 node3203Labels = Sparse.eval nodeValue3203 (mixedVector B) := by
  have h := singleton3203 B _hB
  rw [sound223 B _hB _hF] at h
  norm_num [nodeValue3203, nodeValue223, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3204 node3204Labels = Sparse.eval nodeValue3204 (mixedVector B) := by
  have h := singleton3204 B _hB
  rw [sound221 B _hB _hF] at h
  norm_num [nodeValue3204, nodeValue221, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3205 node3205Labels = Sparse.eval nodeValue3205 (mixedVector B) := by
  have h := singleton3205 B _hB
  rw [sound220 B _hB _hF] at h
  norm_num [nodeValue3205, nodeValue220, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3206 node3206Labels = Sparse.eval nodeValue3206 (mixedVector B) := by
  have h := singleton3206 B _hB
  rw [sound226 B _hB _hF] at h
  norm_num [nodeValue3206, nodeValue226, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3207 node3207Labels = Sparse.eval nodeValue3207 (mixedVector B) := by
  have h := singleton3207 B _hB
  rw [sound227 B _hB _hF] at h
  norm_num [nodeValue3207, nodeValue227, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3208 node3208Labels = Sparse.eval nodeValue3208 (mixedVector B) := by
  simpa only [nodeValue3208, Sparse.eval_nil] using zero3208 B _hB _hF

theorem sound3209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3209 node3209Labels = Sparse.eval nodeValue3209 (mixedVector B) := by
  have h := singleton3209 B _hB
  rw [sound232 B _hB _hF] at h
  norm_num [nodeValue3209, nodeValue232, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3210 node3210Labels = Sparse.eval nodeValue3210 (mixedVector B) := by
  have h := singleton3210 B _hB
  rw [sound235 B _hB _hF] at h
  norm_num [nodeValue3210, nodeValue235, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3211 node3211Labels = Sparse.eval nodeValue3211 (mixedVector B) := by
  have h := singleton3211 B _hB
  rw [sound234 B _hB _hF] at h
  norm_num [nodeValue3211, nodeValue234, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3212 node3212Labels = Sparse.eval nodeValue3212 (mixedVector B) := by
  simpa only [nodeValue3212, Sparse.eval_nil] using zero3212 B _hB _hF

theorem sound3213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3213 node3213Labels = Sparse.eval nodeValue3213 (mixedVector B) := by
  simpa only [nodeValue3213, Sparse.eval_nil] using zero3213 B _hB _hF

theorem sound3214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3214 node3214Labels = Sparse.eval nodeValue3214 (mixedVector B) := by
  simpa only [nodeValue3214, Sparse.eval_nil] using zero3214 B _hB _hF

theorem sound3215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3215 node3215Labels = Sparse.eval nodeValue3215 (mixedVector B) := by
  simpa only [nodeValue3215, Sparse.eval_nil] using zero3215 B _hB _hF

theorem sound3216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3216 node3216Labels = Sparse.eval nodeValue3216 (mixedVector B) := by
  simpa only [nodeValue3216, Sparse.eval_nil] using zero3216 B _hB _hF

theorem sound3217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3217 node3217Labels = Sparse.eval nodeValue3217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3217) = mixedMoment B node3217 node3217Labels := rfl
  simpa [nodeValue3217, Sparse.eval] using hc.symm

theorem sound3218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3218 node3218Labels = Sparse.eval nodeValue3218 (mixedVector B) := by
  have h := singleton3218 B _hB
  rw [sound200 B _hB _hF] at h
  norm_num [nodeValue3218, nodeValue200, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3219 node3219Labels = Sparse.eval nodeValue3219 (mixedVector B) := by
  have h := singleton3219 B _hB
  rw [sound204 B _hB _hF] at h
  norm_num [nodeValue3219, nodeValue204, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3220 node3220Labels = Sparse.eval nodeValue3220 (mixedVector B) := by
  simpa only [nodeValue3220, Sparse.eval_nil] using zero3220 B _hB _hF

theorem sound3221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3221 node3221Labels = Sparse.eval nodeValue3221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3221) = mixedMoment B node3221 node3221Labels := rfl
  simpa [nodeValue3221, Sparse.eval] using hc.symm

theorem sound3222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3222 node3222Labels = Sparse.eval nodeValue3222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3222) = mixedMoment B node3222 node3222Labels := rfl
  simpa [nodeValue3222, Sparse.eval] using hc.symm

theorem sound3223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3223 node3223Labels = Sparse.eval nodeValue3223 (mixedVector B) := by
  have h := singleton3223 B _hB
  rw [sound261 B _hB _hF] at h
  norm_num [nodeValue3223, nodeValue261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3224 node3224Labels = Sparse.eval nodeValue3224 (mixedVector B) := by
  have h := singleton3224 B _hB
  rw [sound269 B _hB _hF] at h
  norm_num [nodeValue3224, nodeValue269, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3225 node3225Labels = Sparse.eval nodeValue3225 (mixedVector B) := by
  have h := singleton3225 B _hB
  rw [sound268 B _hB _hF] at h
  norm_num [nodeValue3225, nodeValue268, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3226 node3226Labels = Sparse.eval nodeValue3226 (mixedVector B) := by
  have h := singleton3226 B _hB
  rw [sound259 B _hB _hF] at h
  norm_num [nodeValue3226, nodeValue259, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3227 node3227Labels = Sparse.eval nodeValue3227 (mixedVector B) := by
  have h := singleton3227 B _hB
  rw [sound260 B _hB _hF] at h
  norm_num [nodeValue3227, nodeValue260, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3228 node3228Labels = Sparse.eval nodeValue3228 (mixedVector B) := by
  simpa only [nodeValue3228, Sparse.eval_nil] using zero3228 B _hB _hF

theorem sound3229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3229 node3229Labels = Sparse.eval nodeValue3229 (mixedVector B) := by
  simpa only [nodeValue3229, Sparse.eval_nil] using zero3229 B _hB _hF

theorem sound3230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3230 node3230Labels = Sparse.eval nodeValue3230 (mixedVector B) := by
  simpa only [nodeValue3230, Sparse.eval_nil] using zero3230 B _hB _hF

theorem sound3231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3231 node3231Labels = Sparse.eval nodeValue3231 (mixedVector B) := by
  simpa only [nodeValue3231, Sparse.eval_nil] using zero3231 B _hB _hF

theorem sound3232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3232 node3232Labels = Sparse.eval nodeValue3232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3232) = mixedMoment B node3232 node3232Labels := rfl
  simpa [nodeValue3232, Sparse.eval] using hc.symm

theorem sound3233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3233 node3233Labels = Sparse.eval nodeValue3233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3233) = mixedMoment B node3233 node3233Labels := rfl
  simpa [nodeValue3233, Sparse.eval] using hc.symm

theorem sound3234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3234 node3234Labels = Sparse.eval nodeValue3234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3234) = mixedMoment B node3234 node3234Labels := rfl
  simpa [nodeValue3234, Sparse.eval] using hc.symm

theorem sound3235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3235 node3235Labels = Sparse.eval nodeValue3235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3235) = mixedMoment B node3235 node3235Labels := rfl
  simpa [nodeValue3235, Sparse.eval] using hc.symm

theorem sound3236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3236 node3236Labels = Sparse.eval nodeValue3236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3236) = mixedMoment B node3236 node3236Labels := rfl
  simpa [nodeValue3236, Sparse.eval] using hc.symm

theorem sound3237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3237 node3237Labels = Sparse.eval nodeValue3237 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3237) = mixedMoment B node3237 node3237Labels := rfl
  simpa [nodeValue3237, Sparse.eval] using hc.symm

theorem sound3238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3238 node3238Labels = Sparse.eval nodeValue3238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3238) = mixedMoment B node3238 node3238Labels := rfl
  simpa [nodeValue3238, Sparse.eval] using hc.symm

theorem sound3239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3239 node3239Labels = Sparse.eval nodeValue3239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3239) = mixedMoment B node3239 node3239Labels := rfl
  simpa [nodeValue3239, Sparse.eval] using hc.symm

theorem sound3240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3240 node3240Labels = Sparse.eval nodeValue3240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3240) = mixedMoment B node3240 node3240Labels := rfl
  simpa [nodeValue3240, Sparse.eval] using hc.symm

theorem sound3241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3241 node3241Labels = Sparse.eval nodeValue3241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3241) = mixedMoment B node3241 node3241Labels := rfl
  simpa [nodeValue3241, Sparse.eval] using hc.symm

theorem sound3242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3242 node3242Labels = Sparse.eval nodeValue3242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3242) = mixedMoment B node3242 node3242Labels := rfl
  simpa [nodeValue3242, Sparse.eval] using hc.symm

theorem sound3243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3243 node3243Labels = Sparse.eval nodeValue3243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3243) = mixedMoment B node3243 node3243Labels := rfl
  simpa [nodeValue3243, Sparse.eval] using hc.symm

theorem sound3244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3244 node3244Labels = Sparse.eval nodeValue3244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3244) = mixedMoment B node3244 node3244Labels := rfl
  simpa [nodeValue3244, Sparse.eval] using hc.symm

theorem sound3245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3245 node3245Labels = Sparse.eval nodeValue3245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3245) = mixedMoment B node3245 node3245Labels := rfl
  simpa [nodeValue3245, Sparse.eval] using hc.symm

theorem sound3246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3246 node3246Labels = Sparse.eval nodeValue3246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3246) = mixedMoment B node3246 node3246Labels := rfl
  simpa [nodeValue3246, Sparse.eval] using hc.symm

theorem sound3247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3247 node3247Labels = Sparse.eval nodeValue3247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3247) = mixedMoment B node3247 node3247Labels := rfl
  simpa [nodeValue3247, Sparse.eval] using hc.symm

theorem sound3248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3248 node3248Labels = Sparse.eval nodeValue3248 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3248) = mixedMoment B node3248 node3248Labels := rfl
  simpa [nodeValue3248, Sparse.eval] using hc.symm

theorem sound3249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3249 node3249Labels = Sparse.eval nodeValue3249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3249) = mixedMoment B node3249 node3249Labels := rfl
  simpa [nodeValue3249, Sparse.eval] using hc.symm

theorem sound3250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3250 node3250Labels = Sparse.eval nodeValue3250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3250) = mixedMoment B node3250 node3250Labels := rfl
  simpa [nodeValue3250, Sparse.eval] using hc.symm

theorem sound3251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3251 node3251Labels = Sparse.eval nodeValue3251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3251) = mixedMoment B node3251 node3251Labels := rfl
  simpa [nodeValue3251, Sparse.eval] using hc.symm

theorem sound3252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3252 node3252Labels = Sparse.eval nodeValue3252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3252) = mixedMoment B node3252 node3252Labels := rfl
  simpa [nodeValue3252, Sparse.eval] using hc.symm

theorem sound3253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3253 node3253Labels = Sparse.eval nodeValue3253 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3253) = mixedMoment B node3253 node3253Labels := rfl
  simpa [nodeValue3253, Sparse.eval] using hc.symm

theorem sound3254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3254 node3254Labels = Sparse.eval nodeValue3254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3254) = mixedMoment B node3254 node3254Labels := rfl
  simpa [nodeValue3254, Sparse.eval] using hc.symm

theorem sound3255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3255 node3255Labels = Sparse.eval nodeValue3255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3255) = mixedMoment B node3255 node3255Labels := rfl
  simpa [nodeValue3255, Sparse.eval] using hc.symm

theorem sound3256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3256 node3256Labels = Sparse.eval nodeValue3256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3256) = mixedMoment B node3256 node3256Labels := rfl
  simpa [nodeValue3256, Sparse.eval] using hc.symm

theorem sound3257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3257 node3257Labels = Sparse.eval nodeValue3257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3257) = mixedMoment B node3257 node3257Labels := rfl
  simpa [nodeValue3257, Sparse.eval] using hc.symm

theorem sound3258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3258 node3258Labels = Sparse.eval nodeValue3258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3258) = mixedMoment B node3258 node3258Labels := rfl
  simpa [nodeValue3258, Sparse.eval] using hc.symm

theorem sound3259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3259 node3259Labels = Sparse.eval nodeValue3259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3259) = mixedMoment B node3259 node3259Labels := rfl
  simpa [nodeValue3259, Sparse.eval] using hc.symm

theorem sound3260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3260 node3260Labels = Sparse.eval nodeValue3260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3260) = mixedMoment B node3260 node3260Labels := rfl
  simpa [nodeValue3260, Sparse.eval] using hc.symm

theorem sound3261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3261 node3261Labels = Sparse.eval nodeValue3261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3261) = mixedMoment B node3261 node3261Labels := rfl
  simpa [nodeValue3261, Sparse.eval] using hc.symm

theorem sound3262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3262 node3262Labels = Sparse.eval nodeValue3262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3262) = mixedMoment B node3262 node3262Labels := rfl
  simpa [nodeValue3262, Sparse.eval] using hc.symm

theorem sound3263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3263 node3263Labels = Sparse.eval nodeValue3263 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3263) = mixedMoment B node3263 node3263Labels := rfl
  simpa [nodeValue3263, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
