import OAI.Probability.InvariantIsing.Cavity.CavityRetainedWeight

namespace OAI

/-! Explicit polynomial weights for the quadratic cascade recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityQuadraticStepWeight {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (⟪p.1 + p.2, Matrix.toEuclideanCLM (𝕜 := ℝ)
    (cavityBackwardQuadratic K C) (p.1 + p.2)⟫ / 2 -
    ⟪p.1, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K P) p.1⟫ / 2 +
    Real.log ((1 - P * K).det / (1 - C * K).det) / (2 * ζ))

lemma measurable_cavityQuadraticStepWeight {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ) :
    Measurable (cavityQuadraticStepWeight K P C ζ) := by
  unfold cavityQuadraticStepWeight
  fun_prop

lemma cavityQuadraticStepWeight_pos {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    0 < cavityQuadraticStepWeight K P C ζ p := Real.exp_pos _

lemma cavityQuadraticStepWeight_eq_normalized {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u z : EuclideanSpace ℝ (Fin d)) :
    cavityQuadraticStepWeight K P C ζ (u, z) =
      Real.exp (((ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫) -
        Real.log (∫ x : EuclideanSpace ℝ (Fin d), Real.exp
          (ζ / 2 * ⟪u + x, Matrix.toEuclideanCLM (𝕜 := ℝ)
            (cavityBackwardQuadratic K C) (u + x)⟫) ∂multivariateGaussian 0 S)) / ζ) := by
  have h := cavity_gaussian_recursive_logIntegral K P C S hK hC hS ζ hζ
    hPdet hCdet hΔ hQ u
  unfold cavityQuadraticStepWeight
  congr 1
  symm
  calc
    _ = ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
          (cavityBackwardQuadratic K C) (u + z)⟫ / 2 -
        (1 / ζ) * Real.log (∫ x : EuclideanSpace ℝ (Fin d), Real.exp
          (ζ / 2 * ⟪u + x, Matrix.toEuclideanCLM (𝕜 := ℝ)
            (cavityBackwardQuadratic K C) (u + x)⟫) ∂multivariateGaussian 0 S) := by
      field_simp [hζ.ne']
    _ = _ := by rw [h]; ring

/-- The concrete backward polynomial weight supplies the normalized
innovation law required at every ancestor in `cavityInnovationTree_law`. -/
theorem cavity_quadratic_step_weight_innovation_law {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    ((multivariateGaussian 0 S).withDensity
      (fun z => ENNReal.ofReal (cavityQuadraticStepWeight K P C ζ (u, z) ^ ζ))).map
      (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹ (u + z) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u) =
      multivariateGaussian 0
        ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) := by
  simp_rw [cavityQuadraticStepWeight_eq_normalized K P C S hK hC hS ζ hζ
    hPdet hCdet hΔ hQ u]
  exact cavity_retained_gaussian_innovation_law K P C S hK hC hS ζ hζ.ne'
    hPdet hCdet hΔ hQ u

end InvariantIsing

end

end OAI
