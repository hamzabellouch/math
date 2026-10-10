import OAI.Probability.InvariantIsing.Cavity.CavityResidualKernel

namespace OAI

/-! The residual factorization for the actual finite quadratic cascade. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

/-- For every tree with finite actual normalizer, integrating and centering
its ordinary residual leaves the precise quadratic tilted leaf law. -/
theorem cavity_quadratic_residual_leaf_law {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞) :
    (normalizeMass (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
      (multivariateGaussian 0 (H n))).withDensity
        (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) =>
          ENNReal.ofReal (Real.exp (⟪cavityLeafSum n s p.1 + p.2,
            Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2))))).map
      (fun p => (p.1, cavityLeafSum n s p.1 + p.2 -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))) =
      (noiseTiltedLeafLaw n
        (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun _ p => p.1 + p.2) s V).prod
          (multivariateGaussian 0 (cavityResolvent K (H n))) := by
  let ν := noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V
  let F := fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
    ⟪cavityLeafSum n s v, Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cavityBackwardQuadratic K (H n)) (cavityLeafSum n s v)⟫ / 2
  have hKh : K.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hK
  have hI : Integrable (fun v => Real.exp (F v)) ν :=
    cavity_residual_partition_leaf_integrable n K (H n) hKh hR hQ s V hZ
  have hFm : Measurable F := by
    dsimp [F]
    have hs := measurable_cavityLeafSum n s
    fun_prop
  have hterminal : noiseLeafTerminal n (cavityQuadraticValue n K H b)
      (fun _ p => p.1 + p.2) s = F := by
    funext v
    rw [cavity_noiseLeafTerminal_sum, cavityQuadraticValue_terminal]
  have he : ν.tilted F = noiseTiltedLeafLaw n
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V := by
    rw [← cavityQuadratic_terminalGibbsLaw n K H b s V,
      noiseTerminalGibbsLaw, hterminal]
    exact (normalizeMass_exp ν F hFm hI).symm
  have h := cavity_residual_joint_kernel ν (cavityLeafSum n s) (measurable_cavityLeafSum n s)
    K (H n) hK hR hdet hQ hI
  change _ = (ν.tilted F).prod (multivariateGaussian 0 (cavityResolvent K (H n))) at h
  rw [he] at h
  exact h

end InvariantIsing

end

end OAI
