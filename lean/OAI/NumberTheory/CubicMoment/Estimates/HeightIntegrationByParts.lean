import OAI.NumberTheory.CubicMoment.Estimates.FourierTwoDerivatives

namespace OAI

/-! Exact twofold integration by parts for the actual height exponential. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace CubicFirstMoment

def heightFourierIntegral (h : ℝ → ℂ) (ℓ : ℝ) : ℂ := 𝓕 h (-ℓ/(2*Real.pi))

lemma heightFourierIntegral_eq (h : ℝ → ℂ) (ℓ : ℝ) :
    heightFourierIntegral h ℓ = ∫ t : ℝ, h t*Complex.exp ((ℓ*t:ℝ)*Complex.I) := by
  rw [heightFourierIntegral,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  have he : -2*Real.pi*t*(-ℓ/(2*Real.pi)) = ℓ*t := by
    field_simp
  rw [he,smul_eq_mul,mul_comm]

lemma heightFourierIntegral_const_mul (h : ℝ → ℂ) (c : ℂ) (ℓ : ℝ) :
    heightFourierIntegral (fun t => c*h t) ℓ = c*heightFourierIntegral h ℓ := by
  rw [heightFourierIntegral_eq,heightFourierIntegral_eq,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

lemma heightFourierIntegral_second (h : ℝ → ℂ) (hi : Integrable h)
    (hd : Differentiable ℝ h) (hi' : Integrable (deriv h))
    (hd' : Differentiable ℝ (deriv h)) (hi'' : Integrable (deriv (deriv h))) (ℓ : ℝ) :
    heightFourierIntegral (deriv (deriv h)) ℓ = -(ℓ:ℂ)^2*heightFourierIntegral h ℓ := by
  unfold heightFourierIntegral
  rw [fourier_second_deriv h hi hd hi' hd' hi'']
  simp only [smul_eq_mul]
  have he : (2*Real.pi*Complex.I*((-ℓ/(2*Real.pi):ℝ):ℂ)) = -(ℓ:ℂ)*Complex.I := by
    push_cast
    field_simp
  rw [he,mul_pow,Complex.I_sq]
  ring

end CubicFirstMoment

end

end OAI
