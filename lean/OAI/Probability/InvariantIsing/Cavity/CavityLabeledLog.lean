import OAI.Probability.InvariantIsing.Cavity.CavityLabeledPriorTransport
import OAI.Probability.InvariantIsing.Cavity.CavityLogNormalizerTransport

namespace OAI

/-! The labeled and common-root descriptions have the same logarithmic
normalizer, including its disorder expectation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_labeled_log_normalizer {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    (fun ω => Real.log (∫ x, Real.exp (cavityLabeledPotential n K L C (ω,x))
      ∂cavityLabeledPriorKernel n R π ω)) =ᵐ[cavityLabeledDisorderLaw n b S₀ S]
    (cavityRootedLogNormalizer n K R L C π) ∘ cavityLabeledNoiseDisorderMap n := by
  filter_upwards [cavity_labeled_disorder_good n b S₀ S hb] with ω hω
  have hp := cavity_labeled_model_prior_law n R π ω hω.1 hω.2
  have he := hp.hasLaw.integral_comp
    (measurable_cavityRootedLogFactor n K L C).exp.aestronglyMeasurable
  apply congrArg Real.log
  simpa only [Function.comp_def, cavityLabeledRootMap_potential,
    cavityRootedLogNormalizer] using he

theorem cavity_labeled_log_mean {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (hi : Integrable (cavityRootedLogNormalizer n K R L C π)
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _))) :
    Integrable (fun ω => Real.log (∫ x, Real.exp (cavityLabeledPotential n K L C (ω,x))
      ∂cavityLabeledPriorKernel n R π ω)) (cavityLabeledDisorderLaw n b S₀ S) ∧
    (∫ ω, Real.log (∫ x, Real.exp (cavityLabeledPotential n K L C (ω,x))
      ∂cavityLabeledPriorKernel n R π ω) ∂cavityLabeledDisorderLaw n b S₀ S) =
      ∫ ω, cavityRootedLogNormalizer n K R L C π ω
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _) := by
  have hp := cavity_labeled_noise_disorder_law n b S₀ S
  have he := cavity_labeled_log_normalizer n b hb S₀ R S K L C π
  refine ⟨(hp.integrable_comp_of_integrable hi).congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact hp.hasLaw.integral_comp hi.aestronglyMeasurable

end InvariantIsing

end

end OAI
