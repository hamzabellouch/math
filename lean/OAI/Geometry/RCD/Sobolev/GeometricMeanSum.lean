import OAI.Geometry.RCD.Sobolev.LogSumExpIntegrable

namespace OAI

/-! # Integrating a multiplicative two-term density lower bound -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {Ω : Type*} [MeasurableSpace Ω]

theorem geometric_mean_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g h w : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (hw : Integrable w μ)
    (hb : ∀ᵐ x ∂μ, Real.exp (w x)*(Real.exp (f x)+Real.exp (g x))/2 ≤ Real.exp (h x)) :
    Real.exp (∫ x, w x ∂μ)*
      (Real.exp (∫ x, f x ∂μ)+Real.exp (∫ x, g x ∂μ))/2 ≤ Real.exp (∫ x, h x ∂μ) := by
  let L := fun x => Real.log (Real.exp (f x)+Real.exp (g x))
  have hL : Integrable L μ := integrable_log_sum_exp μ hf hg
  have hlog : ∀ᵐ x ∂μ, w x+L x-Real.log 2 ≤ h x := by
    filter_upwards [hb] with x hx
    have hp : 0 < Real.exp (w x)*(Real.exp (f x)+Real.exp (g x)) := by positivity
    have hl := Real.log_le_log (div_pos hp (by norm_num : (0:ℝ)<2)) hx
    rw [Real.log_div hp.ne' (by norm_num),Real.log_mul (Real.exp_ne_zero _)
      (by positivity),Real.log_exp,Real.log_exp] at hl
    exact hl
  have hi : Integrable (fun x => w x+L x-Real.log 2) μ :=
    (hw.add hL).sub (integrable_const _)
  have hmono := integral_mono_ae hi hh hlog
  have hint : (∫ x, w x+L x-Real.log 2 ∂μ)=
      (∫ x, w x ∂μ)+(∫ x, L x ∂μ)-Real.log 2 := by
    have ha : (∫ x, w x+L x-Real.log 2 ∂μ)=
        (∫ x, w x+L x ∂μ)-(∫ _ : Ω, Real.log 2 ∂μ) :=
      integral_sub (hw.add hL) (integrable_const _)
    rw [ha,integral_add hw hL]
    simp
  rw [hint] at hmono
  have hj := log_sum_exp_integral_le μ hf hg
  have hfin : (∫ x, w x ∂μ)+
      Real.log (Real.exp (∫ x, f x ∂μ)+Real.exp (∫ x, g x ∂μ))-Real.log 2 ≤
      ∫ x, h x ∂μ := by linarith
  have he := Real.exp_le_exp.mpr hfin
  simpa only [Real.exp_sub,Real.exp_add,Real.exp_log (by positivity :
    0 < Real.exp (∫ x, f x ∂μ)+Real.exp (∫ x, g x ∂μ)),
    Real.exp_log (by norm_num : (0:ℝ)<2)] using he

end RegularPointCoordinates

end

end OAI
