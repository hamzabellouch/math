import OAI.Probability.InvariantIsing.Cavity.CavityPosteriorPair
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledSpin

namespace OAI

/-! Projection and ordinary-residual removal for the full linear cavity
two-spin test, with its exponential moment derived from the field model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

lemma cavity_projected_spin_prior_law {A : Type*} [MeasurableSpace A]
    {d k : ℕ} (ν : Measure A) [IsProbabilityMeasure ν]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : L.transpose * S * L = (v : ℝ) • 1) :
    MeasurePreserving (cavityResidualFieldProjection (A := A) L)
      ((ν.prod (multivariateGaussian 0 S)).prod (uniformSpinPrior k))
      ((ν.prod (vectorGaussianLaw k v)).prod (uniformSpinPrior k)) := by
  have h1 := (MeasurePreserving.id ν).prod
    (cavity_scalar_projected_field_law S hS L v hcov)
  exact h1.prod (MeasurePreserving.id (uniformSpinPrior k : Measure (Spin k)))

theorem cavity_projected_spin_exp_integrable {A : Type*} [MeasurableSpace A]
    {d k : ℕ} (ν : Measure A) [IsProbabilityMeasure ν]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : L.transpose * S * L = (v : ℝ) • 1)
    (y : A → EuclideanSpace ℝ (Fin d)) (hy : Measurable y) (c : ℝ)
    (hI : Integrable (fun p : Spin k × A =>
      Real.exp (fieldEnergy (cavityProjectField L (y p.2)) p.1))
      ((uniformSpinPrior k : Measure (Spin k)).prod ν)) :
    Integrable (fun p : (A × EuclideanSpace ℝ (Fin d)) × Spin k =>
      Real.exp (cavityLogFactor 0 L (c • 1)
        (y p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2))
      ((ν.prod (multivariateGaussian 0 S)).prod (uniformSpinPrior k)) := by
  have hY := (measurable_cavityProjectField L).comp hy
  have hfull := cavity_residual_spin_exp_integrable ν
    (fun a => cavityProjectField L (y a)) hY v c hI.swap
  have hp := cavity_projected_spin_prior_law ν S hS L v hcov
  have hi := hp.hasLaw.integrable_comp hfull
  simpa only [Function.comp_def, cavityResidualFieldProjection,
    cavity_linear_factor_project, cavityProjectField_add] using hi

theorem cavity_projected_spin_pair_reduce {A : Type*} [MeasurableSpace A]
    {d k : ℕ} (ν : Measure A) [IsProbabilityMeasure ν]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : L.transpose * S * L = (v : ℝ) • 1)
    (y : A → EuclideanSpace ℝ (Fin d)) (hy : Measurable y) (c : ℝ)
    (hI : Integrable (fun p : Spin k × A =>
      Real.exp (fieldEnergy (cavityProjectField L (y p.2)) p.1))
      ((uniformSpinPrior k : Measure (Spin k)).prod ν))
    (D : (Fin 2 → Spin k × A) → ℝ) (hD : Measurable D) :
    referenceReplicaMean ((ν.prod (multivariateGaussian 0 S)).prod (uniformSpinPrior k))
      (fun p => cavityLogFactor 0 L (c • 1)
        (y p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)
      (fun σ => D (fun i => ((σ i).2, (σ i).1.1))) =
    referenceReplicaMean ((uniformSpinPrior k : Measure (Spin k)).prod ν)
      (fun p => fieldEnergy (cavityProjectField L (y p.2)) p.1) D := by
  have hY := (measurable_cavityProjectField L).comp hy
  have hfull := cavity_projected_spin_exp_integrable ν S hS L v hcov y hy c hI
  have hfield := cavity_residual_spin_exp_integrable ν
    (fun a => cavityProjectField L (y a)) hY v c hI.swap
  have hp := cavity_projected_linear_spin_law ν S hS L v hcov y hy c
    (uniformSpinPrior k : Measure (Spin k))
  have hD' : Measurable (fun σ : Fin 2 → (A × (Fin k → ℝ)) × Spin k =>
      D (fun i => ((σ i).2, (σ i).1.1))) :=
    hD.comp (Measurable.of_eval fun i =>
      ((measurable_pi_apply i).snd).prodMk (measurable_pi_apply i).fst.fst)
  calc
    _ = referenceReplicaMean ((ν.prod (vectorGaussianLaw k v)).prod (uniformSpinPrior k))
        (fun p => fieldEnergy (cavityProjectField L (y p.1.1) + p.1.2) p.2 +
          (k : ℝ) * c / 2)
        (fun σ => D (fun i => ((σ i).2, (σ i).1.1))) := by
      exact cavity_posterior_pair_map _ _ _ _ hfull hfield
        (cavityResidualFieldProjection L) (measurable_cavityResidualFieldProjection L) hp _ hD'
    _ = _ := cavity_residual_spin_pair_marginal ν _ hY v c hI D hD

end InvariantIsing

end

end OAI
