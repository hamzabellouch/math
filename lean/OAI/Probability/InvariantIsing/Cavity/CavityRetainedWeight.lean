import OAI.Probability.InvariantIsing.Cavity.CavityGaussianInnovation

namespace OAI

/-! Normalized fractional weights for the quadratic retained marks. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_retained_weight_density {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ)
    (hf : Integrable (fun z => Real.exp (f z)) μ) (b : ℝ) (hb : b ≠ 0) :
    μ.withDensity (fun z => ENNReal.ofReal
      (Real.exp ((f z - Real.log (∫ x, Real.exp (f x) ∂μ)) / b) ^ b)) =
      μ.tilted f := by
  unfold Measure.tilted
  congr 1
  funext z
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, div_mul_cancel₀ _ hb,
    Real.exp_sub, Real.exp_log (integral_exp_pos hf)]

/-- The fractional density used in the retained tree is exactly the
normalized quadratic tilt, with no ordinary terminal exponential
moment required. -/
theorem cavity_retained_gaussian_innovation_law {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : ζ ≠ 0)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    let f := fun z : EuclideanSpace ℝ (Fin d) =>
      ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫
    ((multivariateGaussian 0 S).withDensity
      (fun z => ENNReal.ofReal
        (Real.exp ((f z - Real.log (∫ x, Real.exp (f x)
          ∂multivariateGaussian 0 S)) / ζ) ^ ζ))).map
      (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹ (u + z) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u) =
      multivariateGaussian 0
        ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) := by
  dsimp only
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
  have hf := cavity_multivariate_gaussian_integrable
    (ζ • cavityBackwardQuadratic K C) S hζL hQ u
  simp_rw [he] at hf
  rw [cavity_retained_weight_density _ _ hf ζ hζ]
  exact cavity_gaussian_step_innovation_law K P C S hK hC hS ζ hPdet hCdet hΔ hQ u

end InvariantIsing

end

end OAI
