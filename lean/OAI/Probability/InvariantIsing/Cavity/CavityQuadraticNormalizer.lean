import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticTree
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRoot

namespace OAI

/-! The finite quadratic cascade normalizer from its conditional moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityDeterminantStep {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  Real.log ((1 - H i * K).det / (1 - H (i + 1) * K).det) / (2 * b i)

def cavityQuadraticValue {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ) (i : ℕ)
    (s : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⟪s, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K (H i)) s⟫ / 2 +
    ∑ j ∈ Finset.range i, cavityDeterminantStep K H b j -
    ∑ j ∈ Finset.range n, cavityDeterminantStep K H b j

lemma measurable_cavityQuadraticValue {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ) (i : ℕ) :
    Measurable (cavityQuadraticValue n K H b i) := by
  unfold cavityQuadraticValue
  fun_prop

lemma cavityQuadraticValue_terminal {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (s : EuclideanSpace ℝ (Fin d)) :
    cavityQuadraticValue n K H b n s =
      ⟪s, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K (H n)) s⟫ / 2 := by
  unfold cavityQuadraticValue
  ring

lemma cavityQuadraticValue_root_integrable {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (S₀ : Matrix (Fin d) (Fin d) ℝ) :
    Integrable (cavityQuadraticValue n K H b 0) (multivariateGaussian 0 S₀) := by
  have he : cavityQuadraticValue n K H b 0 = fun s =>
      ⟪s, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K (H 0)) s⟫ / 2 -
        ∑ j ∈ Finset.range n, cavityDeterminantStep K H b j := by
    funext s
    simp only [cavityQuadraticValue, Finset.range_zero, Finset.sum_empty, add_zero]
  rw [he]
  exact (cavity_gaussian_root_integrable (cavityBackwardQuadratic K (H 0)) S₀).sub
    (integrable_const (∑ j ∈ Finset.range n, cavityDeterminantStep K H b j))

lemma cavityQuadraticValue_root_integral {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef) :
    (∫ s, cavityQuadraticValue n K H b 0 s ∂multivariateGaussian 0 S₀) =
      Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
        ∑ j ∈ Finset.range n, cavityDeterminantStep K H b j := by
  simp only [cavityQuadraticValue, Finset.range_zero, Finset.sum_empty, add_zero]
  rw [integral_sub (cavity_gaussian_root_integrable _ S₀) (integrable_const _),
    cavity_gaussian_root_integral _ S₀ hS₀, integral_const, probReal_univ, one_smul]

lemma cavityQuadraticStepWeight_telescoping {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (i : ℕ) (s a : EuclideanSpace ℝ (Fin d)) :
    cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i) (s, a) =
      Real.exp (cavityQuadraticValue n K H b (i + 1) (s + a) -
        cavityQuadraticValue n K H b i s) := by
  unfold cavityQuadraticStepWeight cavityQuadraticValue cavityDeterminantStep
  rw [Finset.sum_range_succ]
  congr 1
  ring

lemma cavity_quadratic_step_fractional_moment {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    (∫⁻ z, ENNReal.ofReal (cavityQuadraticStepWeight K P C ζ (u, z) ^ ζ)
      ∂multivariateGaussian 0 S) = 1 := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin d)) => μ Set.univ)
    (cavity_quadratic_step_weight_innovation_law K P C S hK hC hS ζ hζ
      hPdet hCdet hΔ hQ u)
  have hg : Measurable (fun z => cavityStepInnovation K P C (u, z)) :=
    (measurable_cavityStepInnovation K P C).comp (measurable_const.prodMk measurable_id)
  simp only [cavityStepInnovation] at hg
  rw [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, measure_univ] at h
  exact h

/-- Positivity, logarithmic integrability and the exact deterministic
mean of the finite quadratic cascade normalizer. -/
theorem cavity_quadratic_cascade_log_integral {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) :
    let μ := cavityGaussianMarks S
    let X := cavityQuadraticValue n K H b
    let u := fun (_ : ℕ) (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => p.1 + p.2
    let P := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)
    let L := fun T => Real.log
      ((noiseTreeFactor n b μ X u s T).toReal / (noiseTreeTotal _ n T).toReal)
    (∀ᵐ T ∂P, 0 < noiseTreeFactor n b μ X u s T ∧ noiseTreeFactor n b μ X u s T < ∞) ∧
      Integrable L P ∧ (∫ T, L T ∂P) = cavityQuadraticValue n K H b 0 s := by
  dsimp only
  let c := fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  have hc : ∀ i, Measurable (c i) := fun i => measurable_cavityQuadraticStepWeight _ _ _ _
  have hu : ∀ i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  have hm (i : ℕ) (u : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ a, ENNReal.ofReal (c i (u, a) ^ b i) ∂(cavityGaussianMarks S i : Measure _)) = 1 :=
    cavity_quadratic_step_fractional_moment K (H i) (H (i + 1)) (S i) hK (hH (i + 1))
      (hS i) (b i) (hb i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i) u
  have h := noiseCascade_log_integral n b hbCascade (cavityGaussianMarks S) hc hu
    (fun i u a => cavityQuadraticStepWeight_telescoping n K H b i u a) hm s
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end InvariantIsing

end

end OAI
