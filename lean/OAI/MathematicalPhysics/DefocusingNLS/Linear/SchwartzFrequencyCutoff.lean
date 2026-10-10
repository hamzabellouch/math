import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDyadicPartition
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierLocalization

namespace OAI

/-! # A smooth frequency cutoff and its exact radian inverse Fourier kernel -/

open scoped SchwartzMap FourierTransform

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def radianInverseKernel (ψ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((Units.mk0 (2 * Real.pi) (by positivity)) • ContinuousLinearEquiv.refl ℝ E) ψ)

theorem radianFourierKernel_inverseKernel (ψ : 𝓢(E, ℂ)) :
    radianFourierKernel (radianInverseKernel ψ) = ψ := by
  ext ξ
  change (𝓕 (radianInverseKernel ψ)) ((2 * Real.pi)⁻¹ • ξ) = ψ ξ
  rw [radianInverseKernel, FourierTransform.fourier_fourierInv_eq]
  change ψ ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ)) = ψ ξ
  rw [smul_smul, mul_inv_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity), one_smul]

noncomputable def smoothFrequencyCutoff (R : ℝ) (hR : 0 < R) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((Units.mk0 ((2 * R)⁻¹) (by positivity)) • ContinuousLinearEquiv.refl ℝ E)
    homogeneousCoreCutoff

@[simp] theorem smoothFrequencyCutoff_apply (R : ℝ) (hR : 0 < R) (ξ : E) :
    smoothFrequencyCutoff R hR ξ = homogeneousCoreCutoff ((2 * R)⁻¹ • ξ) := rfl

theorem smoothFrequencyCutoff_one (R : ℝ) (hR : 0 < R) (ξ : E) (hξ : ‖ξ‖ ≤ R) :
    smoothFrequencyCutoff R hR ξ = 1 := by
  rw [smoothFrequencyCutoff_apply]
  apply homogeneousCoreCutoff_one
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 * R)⁻¹)]
  have h := mul_le_mul_of_nonneg_left hξ (show 0 ≤ (2 * R)⁻¹ by positivity)
  have he : (2 * R)⁻¹ * R = 1 / 2 := by field_simp
  exact he ▸ h

theorem smoothFrequencyCutoff_zero (R : ℝ) (hR : 0 < R) (ξ : E) (hξ : 2 * R ≤ ‖ξ‖) :
    smoothFrequencyCutoff R hR ξ = 0 := by
  rw [smoothFrequencyCutoff_apply]
  apply homogeneousCoreCutoff_zero
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 * R)⁻¹)]
  have h := mul_le_mul_of_nonneg_left hξ (show 0 ≤ (2 * R)⁻¹ by positivity)
  simpa only [inv_mul_cancel₀ (show 2 * R ≠ 0 by positivity)] using h

theorem smoothFrequencyCutoff_norm_le (R : ℝ) (hR : 0 < R) (ξ : E) :
    ‖smoothFrequencyCutoff R hR ξ‖ ≤ 1 := by
  rw [smoothFrequencyCutoff_apply, homogeneousCoreCutoff_apply, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg homogeneousCoreBump.nonneg]
  exact homogeneousCoreBump.le_one

theorem one_sub_smoothFrequencyCutoff_norm_le (R : ℝ) (hR : 0 < R) (ξ : E) :
    ‖1 - smoothFrequencyCutoff R hR ξ‖ ≤ 1 := by
  rw [smoothFrequencyCutoff_apply, homogeneousCoreCutoff_apply, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr homogeneousCoreBump.le_one)]
  exact sub_le_self _ homogeneousCoreBump.nonneg

end DefocusingNLS

end OAI
