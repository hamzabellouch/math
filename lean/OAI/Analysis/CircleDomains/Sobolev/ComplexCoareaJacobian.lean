import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorEnergy
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Tactic.LinearCombination

namespace OAI

/-! The scalar Jacobian identity in regular complex coordinates. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma complex_real_det_columns (B : ℂ →L[ℝ] ℂ) :
    B.det = (B 1).re * (B Complex.I).im - (B Complex.I).re * (B 1).im := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    ContinuousLinearMap.coe_coe, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma coarea_covector_jacobian (A : ℂ →L[ℝ] ℝ) (B : ℂ →L[ℝ] ℂ)
    (h1 : A (B 1) = 1) (hI : A (B Complex.I) = 0) :
    ‖A‖ * |B.det| = ‖B Complex.I‖ := by
  rw [complexCovector_apply] at h1 hI
  let Δ := (B 1).re * (B Complex.I).im - (B Complex.I).re * (B 1).im
  have ha : A 1 * Δ = (B Complex.I).im := by
    dsimp only [Δ]
    linear_combination (B Complex.I).im * h1 - (B 1).im * hI
  have hb : A Complex.I * Δ = -(B Complex.I).re := by
    dsimp only [Δ]
    linear_combination -(B Complex.I).re * h1 + (B 1).re * hI
  have hs : (‖A‖ * |B.det|) ^ 2 = ‖B Complex.I‖ ^ 2 := by
    rw [mul_pow, sq_abs, complexCovector_norm_sq, complex_real_det_columns,
      Complex.sq_norm, Complex.normSq_apply]
    simp only [← pow_two]
    change ((A 1)^2 + (A Complex.I)^2) * Δ^2 = (B Complex.I).re^2 + (B Complex.I).im^2
    calc
      _ = (A 1 * Δ)^2 + (A Complex.I * Δ)^2 := by ring
      _ = (B Complex.I).re^2 + (B Complex.I).im^2 := by rw [ha, hb]; ring
  exact (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (norm_nonneg _)).mp hs

end CircleDomainRigidity

end

end OAI
