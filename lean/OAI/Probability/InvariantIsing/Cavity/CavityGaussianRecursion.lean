import OAI.Probability.InvariantIsing.Cavity.CavityMultivariateGaussian
import OAI.Probability.InvariantIsing.Cavity.CavityStepPrecision

namespace OAI

/-! Scaling the covariance step by its positive cascade exponent. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_scaled_sqrt_factor {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 ≤ ζ) :
    (Real.sqrt ζ • CFC.sqrt S) * (Real.sqrt ζ • CFC.sqrt S).transpose = ζ • S := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt hζ, cavity_covariance_sqrt_factor S hS]

lemma cavity_scaled_factor_precision {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ) (hζ : 0 ≤ ζ) :
    cavityFactorPrecision K (Real.sqrt ζ • B) = cavityFactorPrecision (ζ • K) B := by
  simp only [cavityFactorPrecision, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hζ]

/-- The exact precision required by the Gaussian law, obtained from the
diagonal covariance ordering, including zero covariance increments. -/
theorem cavity_scaled_step_precision {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (hS : S.PosSemidef) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (p c : Fin d → ℝ) (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i)
    (hcp : ∀ i, c i ≤ p i) (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (hΔ : Matrix.diagonal p - Matrix.diagonal c = ζ • S) :
    (cavityFactorPrecision (ζ • cavityBackwardQuadratic K (Matrix.diagonal c))
      (CFC.sqrt S)).PosDef := by
  rw [← cavity_scaled_factor_precision _ _ ζ hζ]
  apply cavity_step_precision_posDef K (Real.sqrt ζ • CFC.sqrt S) hK
    p c hp hc0 hcp hc hgap
  rw [cavity_scaled_sqrt_factor S hS ζ hζ]
  exact hΔ

lemma cavity_scaled_backward_step {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S) :
    cavityBackwardQuadratic (ζ • cavityBackwardQuadratic K C) S =
      ζ • cavityBackwardQuadratic K P := by
  have he : S * (ζ • cavityBackwardQuadratic K C) =
      (P - C) * cavityBackwardQuadratic K C := by
    rw [hΔ, Matrix.mul_smul, Matrix.smul_mul]
  change (ζ • cavityBackwardQuadratic K C) *
      (1 - S * (ζ • cavityBackwardQuadratic K C))⁻¹ =
    ζ • cavityBackwardQuadratic K P
  rw [he, Matrix.smul_mul]
  exact congrArg (fun M => ζ • M) (cavityBackwardQuadratic_step K P C hP hC)

lemma cavity_scaled_step_determinant {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (hC : IsUnit (1 - C * K).det) (hΔ : P - C = ζ • S) :
    (1 - S * (ζ • cavityBackwardQuadratic K C)).det =
      (1 - P * K).det / (1 - C * K).det := by
  have he : S * (ζ • cavityBackwardQuadratic K C) =
      (P - C) * cavityBackwardQuadratic K C := by
    rw [hΔ, Matrix.mul_smul, Matrix.smul_mul]
  rw [he]
  exact cavity_quadratic_det_ratio K P C hC

/-- The single backward Gaussian step `cav:q-gaussian-integral`.
The precision hypothesis is supplied by `cavity_scaled_step_precision`
for the manuscript's diagonal covariance path. -/
theorem cavity_gaussian_recursive_logIntegral {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (hC : C.transpose = C) (hS : S.PosSemidef) (ζ : ℝ) (hζ : 0 < ζ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    (1 / ζ) * Real.log (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp (ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫)
      ∂multivariateGaussian 0 S) =
      -(1 / (2 * ζ)) * Real.log ((1 - P * K).det / (1 - C * K).det) +
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K P) u⟫ / 2 := by
  have hL : (cavityBackwardQuadratic K C).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (cavityBackwardQuadratic_transpose K C hK hC hCdet)
  have hζL : (ζ • cavityBackwardQuadratic K C).IsHermitian := hL.smul (IsSelfAdjoint.all ζ)
  have he (z : EuclideanSpace ℝ (Fin d)) :
      ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (ζ • cavityBackwardQuadratic K C) (u + z)⟫ / 2 =
      ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫ := by
    simp only [map_smul, smul_apply, real_inner_smul_right]
    ring
  have h := cavity_multivariate_gaussian_logIntegral
    (ζ • cavityBackwardQuadratic K C) S hζL hS hQ u
  simp_rw [he] at h
  rw [cavity_scaled_step_determinant K P C S ζ hCdet hΔ,
    cavity_scaled_backward_step K P C S ζ hPdet hCdet hΔ] at h
  simp only [map_smul, smul_apply, real_inner_smul_right] at h
  rw [h]
  field_simp [hζ.ne']

end InvariantIsing

end

end OAI
