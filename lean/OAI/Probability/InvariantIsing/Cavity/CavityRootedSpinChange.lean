import OAI.Probability.InvariantIsing.Cavity.CavitySpinIntegrability

namespace OAI

/-! The full spin change of variables with the common Gaussian root retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavitySpinDisorderInnovation {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ ω.1,
    cavityInnovationTree n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun i => cavityStepInnovation K (H i) (H (i + 1))) ω.1 ω.2)

lemma measurable_cavitySpinDisorderInnovation {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) : Measurable (cavitySpinDisorderInnovation n K H S b) := by
  exact ((Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹).measurable.comp measurable_fst).prodMk
    (measurable_cavityInnovationTree n b (cavityGaussianMarks S) _ _
      (fun i => measurable_cavityQuadraticStepWeight _ _ _ _)
      (fun i => measurable_cavityStepInnovation _ _ _))

theorem cavity_rooted_full_spin_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) ω.1 ω.2 < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) ω.1 ω.2)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n (H n) ω).prod π)) :
    (cavityRootedFullGibbs n K (H n) L C π ω).map (cavityRootedSpinInnovation n K H b) =
      cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π
        (cavitySpinDisorderInnovation n K H S b ω) := by
  have he' := cavity_spin_innovation_exp_integrable n K H S b L C hK hR hdet hQ
    ω.1 ω.2 hZ hV π he
  let ω' := cavitySpinDisorderInnovation n K H S b ω
  let T := Prod.map (cavityResidualInnovationMap n K H b ω.1) (id : Spin k → Spin k)
  have hT : Measurable T := (measurable_cavityResidualInnovationMap n K H b ω.1).prodMap measurable_id
  have hcomp : cavityRootedSpinInnovation (k := k) n K H b ∘ cavityAttachSpinRoot n ω.1 =
      cavityAttachSpinRoot n ω'.1 ∘ T := by
    funext p
    rfl
  rw [cavityRootedFullGibbs_eq_residual_map n K (H n) L C π ω.1 ω.2 he,
    Measure.map_map (measurable_cavityRootedSpinInnovation n K H b)
      (measurable_cavityAttachSpinRoot n ω.1), hcomp,
    ← Measure.map_map (measurable_cavityAttachSpinRoot n ω'.1) hT]
  have htr := cavity_full_spin_innovation_transport n K H S b L C hK hR hdet hQ ω.1 ω.2 hZ hV π
  change (cavityResidualSpinFullLaw n K (H n) L C ω.1 ω.2 π).map T =
    cavityResidualSpinFullLaw n 0 (cavityResolvent K (H n)) L C ω'.1 ω'.2 π at htr
  rw [htr]
  exact (cavityRootedFullGibbs_eq_residual_map n 0 (cavityResolvent K (H n)) L C π ω'.1 ω'.2 he').symm

end InvariantIsing

end

end OAI
