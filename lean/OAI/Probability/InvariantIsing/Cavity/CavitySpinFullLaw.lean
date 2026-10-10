import OAI.Probability.InvariantIsing.Cavity.CavitySpinTiltTransport

namespace OAI

/-! Exact full-factor spin law before and after the quadratic innovation
change of variables. The ordinary residual is part of each probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal RealInnerProductSpace

namespace InvariantIsing

def cavityResidualSpinFullLaw {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) (π : Measure (Spin k)) :
    Measure ((NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k) :=
  (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 R)).prod π).tilted
      (fun p => cavityLogFactor K L C
        (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)

lemma cavityQuadraticResidualGibbs_eq_tilted {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R s V < ∞) :
    cavityQuadraticResidualGibbs n K R s V =
      ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
        (multivariateGaussian 0 R)).tilted
          (fun p => ⟪cavityLeafSum n s p.1 + p.2,
            Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2) := by
  have hm : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => ⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2) := by
    have hs := measurable_cavityLeafSum n s
    fun_prop
  exact normalizeMass_exp _ _ hm (cavity_residual_quadratic_integrable n K R s V hZ)

theorem cavityResidualSpinFullLaw_eq_successive {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) (π : Measure (Spin k))
    [IsProbabilityMeasure π] (hZ : cavityResidualPartition n K R s V < ∞) :
    cavityResidualSpinFullLaw n K R L C s V π =
      ((cavityQuadraticResidualGibbs n K R s V).prod π).tilted
        (cavityLinearResidualPotential n L C s) := by
  have hm : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => ⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2) := by
    have hs := measurable_cavityLeafSum n s
    fun_prop
  rw [cavityQuadraticResidualGibbs_eq_tilted n K R s V hZ,
    cavity_tilt_prod_left _ π _ hm,
    tilted_tilted ((cavity_residual_quadratic_integrable n K R s V hZ).comp_fst π)]
  unfold cavityResidualSpinFullLaw
  congr 1
  funext p
  exact (cavity_rooted_exponent_split n K L C ((s, p.1), p.2)).symm

theorem cavity_full_spin_innovation_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    (cavityResidualSpinFullLaw n K (H n) L C s V π).map
        (Prod.map (cavityResidualInnovationMap n K H b s) id) =
      (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (cavityInnovationTree n b (cavityGaussianMarks S)
          (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
          (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V)).prod
            (multivariateGaussian 0 (cavityResolvent K (H n)))).prod π).tilted
        (cavityLinearResidualPotential n L C
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)) := by
  rw [cavityResidualSpinFullLaw_eq_successive n K (H n) L C s V π hZ]
  exact cavity_spin_tilt_innovation_transport n K H S b L C hK hR hdet hQ s V hZ hV π

end InvariantIsing

end

end OAI
