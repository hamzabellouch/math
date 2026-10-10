import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticStepWeight
import OAI.Probability.InvariantIsing.Cavity.CavityInnovationTree

namespace OAI

/-! Independent Gaussian innovations for the retained finite quadratic tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityGaussianMarks {d : ℕ} (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (i : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
  ⟨multivariateGaussian 0 (S i), inferInstance⟩

def cavityStepInnovation {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹ (p.1 + p.2) -
    Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ p.1

lemma measurable_cavityStepInnovation {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (cavityStepInnovation K P C) := by
  unfold cavityStepInnovation
  fun_prop

/-- Actual backward quadratic weights turn the finite Gaussian tree
into a tree with independent centered Gaussian innovations. -/
theorem cavity_quadratic_innovation_tree_law {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _).map
      (cavityInnovationTree n b (cavityGaussianMarks S)
        (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun i => cavityStepInnovation K (H i) (H (i + 1))) u) =
      noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
        (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) := by
  apply cavityInnovationTree_law
  · intro i
    exact measurable_cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  · intro i
    exact measurable_cavityStepInnovation K (H i) (H (i + 1))
  · intro i s a
    exact cavityQuadraticStepWeight_pos K (H i) (H (i + 1)) (b i) (s, a)
  · intro i s
    exact cavity_quadratic_step_weight_innovation_law K (H i) (H (i + 1)) (S i)
      hK (hH (i + 1)) (hS i) (b i) (hb i) (hdet i) (hdet (i + 1))
      (hΔ i) (hQ i) s

end InvariantIsing

end

end OAI
