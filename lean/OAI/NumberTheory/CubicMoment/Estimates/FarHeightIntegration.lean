import OAI.NumberTheory.CubicMoment.Estimates.HeightIntegrationByParts
import OAI.NumberTheory.CubicMoment.Estimates.FarInverseSquare
import Mathlib.Analysis.Fourier.Inversion

namespace OAI

/-! The far-cell height identity and its uniformly integrable Fourier kernel.
These are identities for the actual height integral, with no arithmetic input. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace CubicFirstMoment

lemma far_height_identity (h : ℝ → ℂ) (hi : Integrable h)
    (hd : Differentiable ℝ h) (hi' : Integrable (deriv h))
    (hd' : Differentiable ℝ (deriv h)) (hi'' : Integrable (deriv (deriv h)))
    {J T ℓ : ℝ} (hJ : 0 < J) (hT : 0 < T) (hfar : 1 ≤ |J*ℓ|) :
    heightFourierIntegral h ℓ =
      -((J/T:ℝ):ℂ)^2 * farInverseSquare (J*ℓ) *
        heightFourierIntegral (fun t => (T:ℂ)^2*deriv (deriv h) t) ℓ := by
  have hl : ℓ ≠ 0 := by
    intro hz
    simp only [hz,mul_zero,abs_zero] at hfar
    linarith
  have hJc : (J:ℂ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hTc : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hlc : (ℓ:ℂ) ≠ 0 := by exact_mod_cast hl
  rw [heightFourierIntegral_const_mul,heightFourierIntegral_second h hi hd hi' hd' hi'']
  simp only [farInverseSquare,farInverseSquareReal_eq hfar,zpow_neg,zpow_ofNat]
  push_cast
  field_simp

lemma far_dilated_integrable {J : ℝ} (hJ : 0 < J) :
    Integrable (fun x : ℝ => farInverseSquare (J*x)) := by
  exact (integrable_comp_mul_left_iff farInverseSquare hJ.ne').mpr
    farInverseSquare_integrable

lemma far_dilated_fourier_integrable {J : ℝ} (hJ : 0 < J) :
    Integrable (𝓕 (fun x : ℝ => farInverseSquare (J*x))) := by
  have he (t : ℝ) : 𝓕 (fun x => farInverseSquare (J*x)) t =
      (J:ℂ)⁻¹*𝓕 farInverseSquare (t/J) := by
    have hm : 𝓕 (scaledKernel farInverseSquare J) t =
        (J:ℂ)*𝓕 (fun x => farInverseSquare (J*x)) t := by
      simp only [Real.fourier_real_eq_integral_exp_smul,scaledKernel,smul_eq_mul]
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [←fourier_scaledKernel farInverseSquare hJ t,hm]
    exact (inv_mul_cancel_left₀ (show (J:ℂ) ≠ 0 by exact_mod_cast hJ.ne') _).symm
  change Integrable (fun t : ℝ => 𝓕 (fun x => farInverseSquare (J*x)) t)
  simp_rw [he]
  exact ((integrable_comp_div_iff _ hJ.ne').mpr farInverseSquare_fourier_integrable).const_mul _

/-- Fourier inversion separates the far-cell product weight, with its
frequency shifts independent of the height variable. -/
lemma far_fourier_representation {J : ℝ} (hJ : 0 < J) (x : ℝ) :
    farInverseSquare (J*x) =
      ∫ u : ℝ, Complex.exp ((2*Real.pi*u*x:ℝ)*Complex.I) *
        𝓕 (fun y => farInverseSquare (J*y)) u := by
  have hc : Continuous (fun y : ℝ => farInverseSquare (J*y)) :=
    farInverseSquare_smooth.continuous.comp (continuous_const.mul continuous_id)
  have he := congrFun (hc.fourierInv_fourier_eq (far_dilated_integrable hJ)
    (far_dilated_fourier_integrable hJ)) x
  rw [Real.fourierInv_eq'] at he
  simpa only [RCLike.inner_apply,conj_trivial,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using he.symm

end CubicFirstMoment

end

end OAI
