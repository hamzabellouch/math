import OAI.Analysis.FreeEntropy.GaussianDeBruijn

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open MeasureTheory Set Classical
namespace FiniteEntropySeparation
 theorem entropy_subprobability_bound {Ω : Type u1} [MeasurableSpace Ω] (ν : Measure Ω)
    (f g : Ω → ℝ) (hf : ∀x,0<f x) (hg : ∀x,0<g x)
    (hfi : Integrable f ν) (hgi : Integrable g ν)
    (hff : Integrable (fun x => f x*Real.log (f x)) ν)
    (hfg : Integrable (fun x => f x*Real.log (g x)) ν)
    (hfmass : ∫x,f x ∂ν=1) (hgmass : ∫x,g x ∂ν≤1) :
    -(∫x,f x*Real.log (f x) ∂ν) ≤ -(∫x,f x*Real.log (g x) ∂ν) := by
  have hp x : f x*Real.log (g x)-f x*Real.log (f x) ≤ g x-f x := by
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos (hg x) (hf x))) (hf x).le
    rw [Real.log_div (hg x).ne' (hf x).ne'] at hh
    have he : f x*(g x/f x-1)=g x-f x := by field_simp [(hf x).ne']
    rw [he] at hh
    nlinarith
  have hi := integral_mono (hfg.sub hff) (hgi.sub hfi) hp
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hfg hff,integral_sub hgi hfi,hfmass] at hi
  linarith
 def eventTilt {Ω : Type u2} (g : Ω → ℝ) (E : Set Ω) (z : ℝ) (x : Ω) : ℝ :=
  (if x∈E then Real.exp z else 1)/2*g x
 theorem eventTilt_expand {Ω : Type u3} (g : Ω → ℝ) (E : Set Ω) (z : ℝ) (x : Ω) :
    eventTilt g E z x = g x/2+(Real.exp z-1)/2*E.indicator g x := by
  classical
  by_cases hx : x∈E <;> simp [eventTilt,hx] <;> ring
 theorem eventTilt_log {Ω : Type u4} (g : Ω → ℝ) (hg : ∀x,0<g x) (E : Set Ω) (z : ℝ) (x : Ω) :
    Real.log (eventTilt g E z x)=Real.log (g x)+(if x∈E then z else 0)-Real.log 2 := by
  classical
  by_cases hx : x∈E
  · simp only [eventTilt,hx,ite_true]
    rw [Real.log_mul (div_ne_zero (Real.exp_ne_zero z) (by norm_num : (2:ℝ)≠0)) (hg x).ne',
      Real.log_div (Real.exp_ne_zero z) (by norm_num : (2:ℝ)≠0),Real.log_exp]
    ring
  · simp only [eventTilt,hx,ite_false]
    rw [Real.log_mul (by norm_num : (1/2:ℝ)≠0) (hg x).ne',
      Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (2:ℝ)≠0),Real.log_one]
    ring
 theorem entropy_event_bound {Ω : Type u5} [MeasurableSpace Ω] (ν : Measure Ω)
    (f g : Ω → ℝ) (hf : ∀x,0<f x) (hg : ∀x,0<g x)
    (hfi : Integrable f ν) (hgi : Integrable g ν)
    (hff : Integrable (fun x => f x*Real.log (f x)) ν)
    (hfg : Integrable (fun x => f x*Real.log (g x)) ν)
    (hfmass : ∫x,f x ∂ν=1) (hgmass : ∫x,g x ∂ν=1)
    (E : Set Ω) (hE : MeasurableSet E) {z : ℝ} (hz : 0≤z)
    (hα : (1/2:ℝ)≤∫x in E,f x ∂ν) (hβ : (∫x in E,g x ∂ν)≤Real.exp (-z)) :
    -(∫x,f x*Real.log (f x) ∂ν) ≤ -(∫x,f x*Real.log (g x) ∂ν)-z/2+Real.log 2 := by
  classical
  have hi : Integrable (eventTilt g E z) ν := by
    have heq : eventTilt g E z = fun x => g x/2+(Real.exp z-1)/2*E.indicator g x := funext (eventTilt_expand g E z)
    rw [heq]
    exact (hgi.div_const 2).add ((hgi.indicator hE).const_mul _)
  have hm : (∫x,eventTilt g E z x ∂ν)≤1 := by
    simp only [eventTilt_expand]
    rw [integral_add (hgi.div_const 2) ((hgi.indicator hE).const_mul _),integral_div,
      integral_const_mul,integral_indicator hE,hgmass]
    have hb0 : 0≤∫x in E,g x ∂ν := integral_nonneg (fun x => (hg x).le)
    have h := mul_le_mul_of_nonneg_left hβ (Real.exp_pos z).le
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at h
    nlinarith
  have hp x : 0<eventTilt g E z x := by
    unfold eventTilt
    split_ifs
    · exact mul_pos (div_pos (Real.exp_pos z) (by norm_num)) (hg x)
    · exact mul_pos (by norm_num) (hg x)
  have he x : f x*Real.log (eventTilt g E z x)=f x*Real.log (g x)+z*E.indicator f x-Real.log 2*f x := by
    rw [eventTilt_log g hg]
    by_cases hx : x∈E <;> simp [hx] <;> ring
  have hlog : Integrable (fun x => f x*Real.log (eventTilt g E z x)) ν := by
    simp only [he]
    exact (hfg.add ((hfi.indicator hE).const_mul z)).sub (hfi.const_mul _)
  have hb := entropy_subprobability_bound ν f (eventTilt g E z) hf hp hfi hi hff hlog hfmass hm
  simp only [he] at hb
  have hj : Integrable (fun x => f x*Real.log (g x)+z*E.indicator f x) ν := hfg.add ((hfi.indicator hE).const_mul z)
  rw [integral_sub hj (hfi.const_mul (Real.log 2)),
    integral_add hfg ((hfi.indicator hE).const_mul z),integral_const_mul,integral_const_mul,
    integral_indicator hE,hfmass,mul_one] at hb
  nlinarith [mul_le_mul_of_nonneg_left hα hz]
end FiniteEntropySeparation

end

end OAI
