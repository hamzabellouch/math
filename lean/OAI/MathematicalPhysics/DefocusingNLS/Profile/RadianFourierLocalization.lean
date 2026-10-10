import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzLocalizationKernel
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

/-! # Exact radian Fourier normalization for a localized Fourier polynomial

The torus characters in the manuscript are exp(i n·y/L), while Mathlib's
Fourier transform uses exp(-2π i y·ξ). We rescale the transform explicitly.
-/

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def radianFourierIntegral (f : E → ℂ) (ξ : E) : ℂ :=
  ∫ y, Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) * f y

/-- The radian-normalized Fourier transform of a cutoff is still Schwartz. -/
noncomputable def radianFourierKernel (χ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((Units.mk0 ((2 * Real.pi)⁻¹) (by positivity)) • ContinuousLinearEquiv.refl ℝ E) (𝓕 χ)

theorem radianFourierKernel_apply (χ : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel χ ξ = radianFourierIntegral χ ξ := by
  change 𝓕 (χ : E → ℂ) ((2 * Real.pi)⁻¹ • ξ) = _
  rw [Real.fourier_eq']
  unfold radianFourierIntegral
  apply integral_congr_ae
  filter_upwards [] with y
  rw [real_inner_smul_right]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- Positive dilation in physical space gives exactly the twelve-dimensional Jacobian. -/
theorem radianFourier_dilation (L : ℝ) (hL : 0 < L) (f : E → ℂ) (ξ : E) :
    radianFourierIntegral (fun y => f (L⁻¹ • y)) ξ =
      (L ^ (12 : ℕ) : ℝ) • radianFourierIntegral f (L • ξ) := by
  let g : E → ℂ := fun x => Complex.exp ((-⟪x, L • ξ⟫ : ℝ) * Complex.I) * f x
  have hg (y : E) : Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) * f (L⁻¹ • y) =
      g (L⁻¹ • y) := by
    simp only [g, real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  unfold radianFourierIntegral
  simp_rw [hg]
  simpa only [finrank_euclideanSpace_fin] using
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure E) g hL.le

/-- The localized physical Fourier polynomial, before zero extension is needed. -/
noncomputable def localizedFourierPolynomial (L : ℝ) (χ : 𝓢(E, ℂ))
    (S : Finset frequencyLattice) (v : frequencyLattice → ℂ) (y : E) : ℂ :=
  χ (L⁻¹ • y) * ∑ n ∈ S, v n * Complex.exp ((⟪L⁻¹ • y, (n : E)⟫ : ℝ) * Complex.I)

private theorem radianFourier_modulated_sum (χ : 𝓢(E, ℂ))
    (S : Finset frequencyLattice) (v : frequencyLattice → ℂ) (ξ : E) :
    radianFourierIntegral (fun y => χ y * ∑ n ∈ S,
        v n * Complex.exp ((⟪y, (n : E)⟫ : ℝ) * Complex.I)) ξ =
      ∑ n ∈ S, v n * radianFourierIntegral χ (ξ - n) := by
  have hterm (n : frequencyLattice) : Integrable (fun y : E =>
      v n * (Complex.exp ((-⟪y, ξ - n⟫ : ℝ) * Complex.I) * χ y)) := by
    apply Integrable.const_mul
    apply χ.integrable.bdd_mul (c := 1) (by fun_prop)
    filter_upwards [] with y
    exact (Complex.norm_exp_ofReal_mul_I _).le
  unfold radianFourierIntegral
  have heq (y : E) :
      Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) *
        (χ y * ∑ n ∈ S, v n * Complex.exp ((⟪y, (n : E)⟫ : ℝ) * Complex.I)) =
      ∑ n ∈ S, v n * (Complex.exp ((-⟪y, ξ - n⟫ : ℝ) * Complex.I) * χ y) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    have he : Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) *
        Complex.exp ((⟪y, (n : E)⟫ : ℝ) * Complex.I) =
        Complex.exp ((-⟪y, ξ - n⟫ : ℝ) * Complex.I) := by
      rw [← Complex.exp_add, inner_sub_right]
      congr 1
      push_cast
      ring
    calc
      _ = v n * ((Complex.exp ((-⟪y, ξ⟫ : ℝ) * Complex.I) *
        Complex.exp ((⟪y, (n : E)⟫ : ℝ) * Complex.I)) * χ y) := by ring
      _ = _ := by rw [he]
  simp_rw [heq]
  rw [integral_finsetSum S (fun n _ => hterm n)]
  simp only [integral_const_mul]

/-- The exact finite Fourier cutoff formula, in the manuscript's radian convention. -/
theorem localizedFourierPolynomial_transform (L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (S : Finset frequencyLattice) (v : frequencyLattice → ℂ) (ξ : E) :
    radianFourierIntegral (localizedFourierPolynomial L χ S v) ξ =
      (L ^ (12 : ℕ) : ℝ) • ∑ n ∈ S, v n * radianFourierKernel χ (L • ξ - n) := by
  unfold localizedFourierPolynomial
  rw [radianFourier_dilation L hL (fun y => χ y * ∑ n ∈ S,
    v n * Complex.exp ((⟪y, (n : E)⟫ : ℝ) * Complex.I)) ξ, radianFourier_modulated_sum]
  simp only [radianFourierKernel_apply]

end DefocusingNLS

end OAI
