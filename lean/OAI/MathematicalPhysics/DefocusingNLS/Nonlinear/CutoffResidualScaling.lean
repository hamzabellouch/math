import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingSum
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity
import Mathlib.Analysis.InnerProductSpace.Laplacian

namespace OAI

/-! # Exact normalization of the cutoff residual

The residual has three terms. When
`p = 2m+1` and `2am = 1`, all three have the common physical factor L^(-2-2a).
-/

open scoped SchwartzMap Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem oddPowerNonlinearity_real_mul (m : ℕ) (c : ℝ) (z : ℂ) :
    oddPowerNonlinearity m ((c : ℂ) * z) =
      ((c ^ (2 * m + 1) : ℝ) : ℂ) * oddPowerNonlinearity m z := by
  simp only [oddPowerNonlinearity, mul_pow, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.ofReal_pow]
  rw [show 2 * m + 1 = (m + 1) + m by omega, pow_add]
  ring

theorem oddPowerNonlinearity_profile_scaling (a L : ℝ) (m : ℕ)
    (hL : 0 < L) (ha : 2 * a * (m : ℝ) = 1) (z : ℂ) :
    oddPowerNonlinearity m ((L ^ (2 * a) : ℝ) * z) =
      (L ^ (2 + 2 * a) : ℝ) * oddPowerNonlinearity m z := by
  rw [oddPowerNonlinearity_real_mul]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  congr 1
  push_cast
  nlinarith

noncomputable def cutoffResidual (m : ℕ) (L : ℝ) (χ : E → ℝ) (Q : E → ℂ)
    (y : E) : ℂ :=
  2 * (L⁻¹ : ℝ) * (∑ j : Fin 12,
    (fderiv ℝ χ (L⁻¹ • y) ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
      fderiv ℝ Q y ((EuclideanSpace.basisFun (Fin 12) ℝ) j)) +
    (L⁻¹ ^ (2 : ℕ) : ℝ) * (Δ χ (L⁻¹ • y) : ℂ) * Q y +
    ((χ (L⁻¹ • y) - χ (L⁻¹ • y) ^ (2 * m + 1) : ℝ) : ℂ) * oddPowerNonlinearity m (Q y)

noncomputable def normalizedCutoffResidual (a L : ℝ) (m : ℕ)
    (χ : E → ℝ) (Q : E → ℂ) (x : E) : ℂ :=
  2 * (∑ j : Fin 12,
    (fderiv ℝ χ x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
      ((L ^ (2 * a + 1) : ℝ) * fderiv ℝ Q (L • x) ((EuclideanSpace.basisFun (Fin 12) ℝ) j))) +
    (Δ χ x : ℂ) * ((L ^ (2 * a) : ℝ) * Q (L • x)) +
    ((χ x - χ x ^ (2 * m + 1) : ℝ) : ℂ) *
      oddPowerNonlinearity m ((L ^ (2 * a) : ℝ) * Q (L • x))

theorem cutoffResidual_scaling (a L : ℝ) (m : ℕ) (hL : 0 < L)
    (ha : 2 * a * (m : ℝ) = 1) (χ : E → ℝ) (Q : E → ℂ) (x : E) :
    cutoffResidual m L χ Q (L • x) =
      (L ^ (-2 - 2 * a) : ℝ) * normalizedCutoffResidual a L m χ Q x := by
  have harg : L⁻¹ • (L • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
  have h₁ : L ^ (-2 - 2 * a) * L ^ (2 * a + 1) = L⁻¹ := by
    rw [← Real.rpow_add hL]
    convert Real.rpow_neg_one L using 1; congr 1; ring
  have h₂ : L ^ (-2 - 2 * a) * L ^ (2 * a) = L⁻¹ ^ (2 : ℕ) := by
    rw [← Real.rpow_add hL]
    have he : -2 - 2 * a + 2 * a = -(2 : ℝ) := by ring
    rw [he, Real.rpow_neg hL.le, Real.rpow_two, inv_pow]
  have h₃ : L ^ (-2 - 2 * a) * L ^ (2 + 2 * a) = 1 := by
    rw [← Real.rpow_add hL]
    have he : -2 - 2 * a + (2 + 2 * a) = 0 := by ring
    rw [he, Real.rpow_zero]
  have hc₁ : ((L ^ (-2 - 2 * a) : ℝ) : ℂ) * (L ^ (2 * a + 1) : ℝ) = (L⁻¹ : ℝ) := by
    exact_mod_cast h₁
  have hc₂ : ((L ^ (-2 - 2 * a) : ℝ) : ℂ) * (L ^ (2 * a) : ℝ) = (L⁻¹ ^ (2 : ℕ) : ℝ) := by
    exact_mod_cast h₂
  have hc₃ : ((L ^ (-2 - 2 * a) : ℝ) : ℂ) * (L ^ (2 + 2 * a) : ℝ) = 1 := by
    exact_mod_cast h₃
  have hsum : (∑ j : Fin 12,
      (fderiv ℝ χ x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
        ((L ^ (2 * a + 1) : ℝ) * fderiv ℝ Q (L • x) ((EuclideanSpace.basisFun (Fin 12) ℝ) j))) =
      (L ^ (2 * a + 1) : ℝ) * (∑ j : Fin 12,
        (fderiv ℝ χ x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
          fderiv ℝ Q (L • x) ((EuclideanSpace.basisFun (Fin 12) ℝ) j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold cutoffResidual normalizedCutoffResidual
  rw [harg, oddPowerNonlinearity_profile_scaling a L m hL ha, hsum]
  symm
  calc
    _ = 2 * (((L ^ (-2 - 2 * a) : ℝ) : ℂ) * (L ^ (2 * a + 1) : ℝ)) *
        (∑ j : Fin 12, (fderiv ℝ χ x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) *
          fderiv ℝ Q (L • x) ((EuclideanSpace.basisFun (Fin 12) ℝ) j)) +
      (((L ^ (-2 - 2 * a) : ℝ) : ℂ) * (L ^ (2 * a) : ℝ)) * (Δ χ x : ℂ) * Q (L • x) +
      (((L ^ (-2 - 2 * a) : ℝ) : ℂ) * (L ^ (2 + 2 * a) : ℝ)) *
        ((χ x - χ x ^ (2 * m + 1) : ℝ) : ℂ) * oddPowerNonlinearity m (Q (L • x)) := by ring
    _ = _ := by rw [hc₁, hc₂, hc₃]; ring

end DefocusingNLS

end OAI
