import OAI.NumberTheory.JointDickman.Analysis.MellinPackets

namespace OAI

/-! # Normalized logarithmic windows at a prescribed scale -/
namespace JointDickman
open MeasureTheory
open scoped SchwartzMap FourierTransform

/-- The normalized dilation `w(v/δ)/δ`, for a positive window scale. -/
noncomputable def normalizedSchwartzScale (w : 𝓢(ℝ, ℂ)) (δ : ℝ) (hδ : 0 < δ) :
    𝓢(ℝ, ℂ) :=
  ((δ : ℂ)⁻¹) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 δ hδ.ne')).symm w

theorem normalizedSchwartzScale_apply (w : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
    normalizedSchwartzScale w δ hδ v = w (v / δ) / (δ : ℂ) := by
  simp only [normalizedSchwartzScale, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply_symm, Units.val_inv_eq_inv_val,
    Units.val_mk0, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The normalization removes the scale factor in the Fourier transform. -/
theorem normalizedSchwartzScale_fourier (w : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    (𝓕 (normalizedSchwartzScale w δ hδ) : 𝓢(ℝ, ℂ)) ξ =
      (𝓕 w : 𝓢(ℝ, ℂ)) (δ * ξ) := by
  let F : ℝ → ℂ := fun v =>
    Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) * w (v / δ)
  have hchange := Measure.integral_comp_mul_left F δ
  have hpoint (v : ℝ) : F (δ * v) =
      Complex.exp (((-2 * Real.pi * v * (δ * ξ) : ℝ) : ℂ) * Complex.I) * w v := by
    dsimp [F]
    rw [mul_div_cancel_left₀ v hδ.ne']
    congr 2
    push_cast
    ring
  have hfactor : (|δ⁻¹| : ℝ) = δ⁻¹ := abs_of_pos (inv_pos.mpr hδ)
  simp_rw [hpoint] at hchange
  rw [hfactor] at hchange
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
    SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = (δ : ℂ)⁻¹ * ∫ v : ℝ, F v := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => by
        dsimp only
        rw [normalizedSchwartzScale_apply]
        dsimp [F]
        ring)
    _ = _ := by
      simpa only [smul_eq_mul, Complex.real_smul, Complex.ofReal_inv] using hchange.symm

/-- The exact energy identity at the short logarithmic scale `δ`. -/
theorem scaled_mellinPacket_energy (S : Finset ℕ) (a : ℕ → ℂ)
    (w : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) :
    (∫ v : ℝ, ‖mellinPacket S a (normalizedSchwartzScale w δ hδ) v‖ ^ 2) =
      ∫ ξ : ℝ, ‖(𝓕 w : 𝓢(ℝ, ℂ)) (δ * ξ)‖ ^ 2 *
        ‖mellinPolynomial S a ξ‖ ^ 2 := by
  rw [mellinPacket_energy]
  simp only [normalizedSchwartzScale_fourier]

end JointDickman

end OAI
