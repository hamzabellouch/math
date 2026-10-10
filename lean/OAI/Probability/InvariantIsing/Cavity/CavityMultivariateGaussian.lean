import OAI.Probability.InvariantIsing.Cavity.CavityGaussianFactor
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace OAI

/-! The quadratic integral for the actual multivariate Gaussian law.
The covariance is allowed to be singular. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_covariance_sqrt_factor {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    CFC.sqrt S * (CFC.sqrt S).transpose = S := by
  have hs : (CFC.sqrt S).transpose = CFC.sqrt S := by
    have hs' : (CFC.sqrt S).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg S)
    exact Matrix.isHermitian_iff_isSymm.mp hs'.isHermitian
  rw [hs]
  exact CFC.sqrt_mul_sqrt_self S hS.nonneg

theorem cavity_multivariate_gaussian_integrable {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2))
      (multivariateGaussian 0 S) := by
  rw [multivariateGaussian]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, zero_add] using
    cavity_gaussian_factor_integrable K (CFC.sqrt S) hK hQ u

/-- The exact covariance form of `cav:q-factor`, with no inverse of the
covariance and hence no nondegeneracy assumption on it. -/
theorem cavity_multivariate_gaussian_integral {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2)
      ∂multivariateGaussian 0 S) =
      (Real.sqrt (1 - S * K).det)⁻¹ *
        Real.exp (⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ)
          (cavityBackwardQuadratic K S) u⟫ / 2) := by
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop)]
  simpa only [zero_add, cavity_covariance_sqrt_factor S hS] using
    cavity_gaussian_factor_integral K (CFC.sqrt S) hK hQ u

theorem cavity_multivariate_gaussian_logIntegral {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    Real.log (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2)
      ∂multivariateGaussian 0 S) =
      -Real.log (1 - S * K).det / 2 +
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K S) u⟫ / 2 := by
  have hd : 0 < (1 - S * K).det := by
    simpa only [cavity_factor_det, cavity_covariance_sqrt_factor S hS] using hQ.det_pos
  rw [cavity_multivariate_gaussian_integral K S hK hS hQ u,
    Real.log_mul (inv_ne_zero (Real.sqrt_pos.2 hd).ne') (Real.exp_ne_zero _),
    Real.log_inv, Real.log_sqrt hd.le, Real.log_exp]
  ring

end InvariantIsing

end

end OAI
