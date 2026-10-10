import OAI.Probability.InvariantIsing.Cavity.CavityRootIntegration

namespace OAI

/-! The ordinary Gaussian residual is separate from the Poisson levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

theorem cavity_residual_integral {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hH : H.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt H)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2)
        ∂multivariateGaussian 0 H) =
      Real.exp (-Real.log (1 - H * K).det / 2 +
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K H) u⟫ / 2) := by
  have hi := cavity_multivariate_gaussian_integrable K H hK hQ u
  have hl := cavity_multivariate_gaussian_logIntegral K H hK hH hQ u
  rw [← Real.exp_log (integral_exp_pos hi), hl]

theorem cavity_residual_innovation_law {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hH : H.PosSemidef)
    (hdet : IsUnit (1 - H * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt H)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    ((multivariateGaussian 0 H).tilted (fun z => (1 / 2 : ℝ) *
      ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫)).map
      (fun z => u + z - Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H * K)⁻¹ u) =
      multivariateGaussian 0 (cavityResolvent K H) := by
  have hzero : IsUnit (1 - (0 : Matrix (Fin d) (Fin d) ℝ) * K).det := by simp
  have hΔ : H - 0 = (1 : ℝ) • H := by simp
  have hp : (cavityFactorPrecision
      ((1 : ℝ) • cavityBackwardQuadratic K 0) (CFC.sqrt H)).PosDef := by
    simpa only [cavityBackwardQuadratic_zero, one_smul] using hQ
  simpa only [cavityBackwardQuadratic_zero, zero_mul, sub_zero, inv_one, map_one,
    one_apply_eq_self, Matrix.transpose_one, mul_one, cavityResolvent] using
    cavity_gaussian_step_innovation_law K H 0 H hK (by simp) hH 1 hdet hzero hΔ hp u

theorem cavity_noiseTreeFactor_add_const {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (X : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (u : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (a : ℝ) (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    noiseTreeFactor n b μ (fun i z => X i z + a) u s V =
      ENNReal.ofReal (Real.exp a) * noiseTreeFactor n b μ X u s V := by
  induction n generalizing b μ X u s with
  | zero =>
    simp only [noiseTreeFactor, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_comm _ _
  | succ n ih =>
    rw [noiseTreeFactor, noiseTreeFactor]
    simp_rw [ih]
    simp_rw [← mul_assoc, mul_comm (ENNReal.ofReal (max _ 0)) (ENNReal.ofReal (Real.exp a)),
      mul_assoc]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end InvariantIsing

end

end OAI
