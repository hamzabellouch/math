import OAI.MeasureTheory.Falconer.Slicing.GaussianFourier

namespace OAI

/-! The Euclidean Laplacian and radial moments of the inverse Fourier transform. -/

namespace Falconer
open MeasureTheory Laplacian
open scoped FourierTransform SchwartzMap LineDeriv RealInnerProductSpace

theorem inverse_fourier_lineDeriv_apply {n : ℕ} (φ : 𝓢(Space n, ℂ))
    (v ξ : Space n) :
    𝓕⁻ (∂_{v} φ) ξ = -(2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℝ) * 𝓕⁻ φ ξ := by
  have hg : (inner ℝ · v).HasTemperateGrowth := by fun_prop
  have h := congrArg (fun f : 𝓢(Space n, ℂ) => f ξ)
    (SchwartzMap.fourierInv_lineDerivOp_eq φ v)
  simpa [SchwartzMap.smulLeftCLM_apply hg, smul_eq_mul, mul_assoc] using h

theorem inverse_fourier_laplacian_apply {n : ℕ} (φ : 𝓢(Space n, ℂ)) (ξ : Space n) :
    𝓕⁻ (Δ φ) ξ = (-(2 * (Real.pi : ℂ))^2 * (‖ξ‖^2 : ℝ)) * 𝓕⁻ φ ξ := by
  let e := stdOrthonormalBasis ℝ (Space n)
  rw [SchwartzMap.laplacian_eq_sum e]
  simp only [FourierTransform.fourierInv_sum, sum_apply, inverse_fourier_lineDeriv_apply]
  have hsum : ∑ i, ((inner ℝ ξ (e i) : ℝ) : ℂ)^2 = (‖ξ‖^2 : ℝ) := by
    exact_mod_cast e.sum_sq_inner_left ξ
  calc
    _ = (-(2 * (Real.pi : ℂ))^2 * ∑ i, ((inner ℝ ξ (e i) : ℝ) : ℂ)^2) *
        𝓕⁻ φ ξ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
      simp [Complex.I_sq]
    _ = _ := by rw [hsum]

theorem schwartz_iterate_laplacian_coe {n : ℕ} (j : ℕ) (φ : 𝓢(Space n, ℂ)) :
    (((laplacian : 𝓢(Space n, ℂ) → 𝓢(Space n, ℂ))^[j] φ) : Space n → ℂ) =
      (laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] (φ : Space n → ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    funext x
    exact SchwartzMap.laplacian_apply _ x

theorem inverse_fourier_iterate_laplacian {n : ℕ} (j : ℕ)
    (φ : 𝓢(Space n, ℂ)) (ξ : Space n) :
    𝓕⁻ ((laplacian : 𝓢(Space n, ℂ) → 𝓢(Space n, ℂ))^[j] φ) ξ =
      (-(2 * (Real.pi : ℂ))^2)^j * ((‖ξ‖^2 : ℝ) : ℂ)^j * 𝓕⁻ φ ξ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', inverse_fourier_laplacian_apply, ih]
    ring

theorem integral_inverse_fourier {n : ℕ} (φ : 𝓢(Space n, ℂ)) :
    (∫ ξ : Space n, 𝓕⁻ φ ξ) = φ 0 := by
  have hid : 𝓕 (𝓕⁻ φ : 𝓢(Space n, ℂ)) = φ := FourierTransform.fourier_fourierInv_eq φ
  have h := congrArg (fun f : 𝓢(Space n, ℂ) => f 0) hid
  change 𝓕 (((𝓕⁻ φ : 𝓢(Space n, ℂ))) : Space n → ℂ) 0 = φ 0 at h
  simpa only [Real.fourier_eq, inner_zero_right, neg_zero,
    AddChar.map_zero_eq_one, one_smul] using h

theorem inverse_fourier_radial_moment {n : ℕ} (j : ℕ) (φ : 𝓢(Space n, ℂ)) :
    (∫ ξ : Space n, ((‖ξ‖^2 : ℝ) : ℂ)^j * 𝓕⁻ φ ξ) =
      ((-(2 * (Real.pi : ℂ))^2)^j)⁻¹ *
        ((laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] (φ : Space n → ℂ)) 0 := by
  have h := integral_inverse_fourier ((laplacian : 𝓢(Space n, ℂ) → 𝓢(Space n, ℂ))^[j] φ)
  simp only [inverse_fourier_iterate_laplacian] at h
  simp_rw [mul_assoc] at h
  rw [integral_const_mul] at h
  rw [← schwartz_iterate_laplacian_coe j φ]
  have hc : (-(2 * (Real.pi : ℂ))^2)^j ≠ 0 := by
    apply pow_ne_zero
    exact neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Falconer

end OAI
