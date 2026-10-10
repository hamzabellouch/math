import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticNormalizer
import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-! Integrating the quadratic cascade normalizer over its common root. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_joint_integral_of_centered_square {E T : Type*}
    [MeasurableSpace E] [MeasurableSpace T]
    (μ : Measure E) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : E × T → ℝ) (X : E → ℝ) (hF : Measurable F) (hX : Measurable X)
    (hXi : Integrable X μ)
    (hsq : ∀ s, Integrable (fun t => (F (s, t) - X s) ^ 2) ν)
    (hbound : ∃ C : ℝ, ∀ s, (∫ t, (F (s, t) - X s) ^ 2 ∂ν) ≤ C)
    (hmean : ∀ s, (∫ t, F (s, t) ∂ν) = X s) :
    Integrable F (μ.prod ν) ∧ (∫ p, F p ∂μ.prod ν) = ∫ s, X s ∂μ := by
  let D : E × T → ℝ := fun p => F p - X p.1
  have hD : Measurable D := hF.sub (hX.comp measurable_fst)
  obtain ⟨C, hC⟩ := hbound
  have hDi := joint_integrable_square_of_uniform_conditionals (P := μ) (Q := ν) hD hsq hC
  have hDLp := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mpr hDi
  have hi : Integrable F (μ.prod ν) := by
    convert (hDLp.integrable (by norm_num)).add
      (hXi.comp_fst ν) using 1
    funext p
    simp [D]
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  simp_rw [hmean]

theorem cavity_quadratic_root_log_integral {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef) :
    let μ := cavityGaussianMarks S
    let X := cavityQuadraticValue n K H b
    let u := fun (_ : ℕ) (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => p.1 + p.2
    let P := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)
    let F := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      Real.log ((noiseTreeFactor n b μ X u p.1 p.2).toReal /
        (noiseTreeTotal _ n p.2).toReal)
    Integrable F ((multivariateGaussian 0 S₀).prod P) ∧
      (∫ p, F p ∂(multivariateGaussian 0 S₀).prod P) =
        Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
          ∑ j ∈ Finset.range n, cavityDeterminantStep K H b j := by
  dsimp only
  let μ := cavityGaussianMarks S
  let X := cavityQuadraticValue n K H b
  let u := fun (_ : ℕ) (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => p.1 + p.2
  let P : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) := noiseCascadeLaw _ n b μ
  have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let F := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
    Real.log ((noiseTreeFactor n b μ X u p.1 p.2).toReal /
      (noiseTreeTotal _ n p.2).toReal)
  let c := fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  have hc : ∀ i, Measurable (c i) := fun i => measurable_cavityQuadraticStepWeight _ _ _ _
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_cavityQuadraticValue _ _ _ _ _
  have hu : ∀ i, Measurable (u i) := fun _ => measurable_fst.add measurable_snd
  have hm (i : ℕ) (s : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ a, ENNReal.ofReal (c i (s, a) ^ b i) ∂(μ i : Measure _)) = 1 :=
    cavity_quadratic_step_fractional_moment K (H i) (H (i + 1)) (S i) hK (hH (i + 1))
      (hS i) (b i) (hb i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i) s
  have hcore (s : EuclideanSpace ℝ (Fin d)) :=
    noiseCascade_log_integral n b hbCascade μ hc hu
      (fun i s a => cavityQuadraticStepWeight_telescoping n K H b i s a) hm s
  have hF : Measurable F :=
    (((measurable_noiseTreeFactor n b μ hXm hu).ennreal_toReal).div
      (((measurable_noiseTreeTotal _ n).comp measurable_snd).ennreal_toReal)).log
  have h := cavity_joint_integral_of_centered_square (multivariateGaussian 0 S₀) P F (X 0)
    hF (hXm 0) (cavityQuadraticValue_root_integrable n K H b S₀)
    (fun s => (hcore s).2.2.2.1)
    ⟨_, fun s => (hcore s).2.2.2.2⟩ (fun s => (hcore s).2.2.1)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  exact cavityQuadraticValue_root_integral n K H b S₀ hS₀

end InvariantIsing

end

end OAI
