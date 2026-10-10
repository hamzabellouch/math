import OAI.Probability.InvariantIsing.Fields.PriorPosteriorPair
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledSpin

namespace OAI

/-! Euclidean Gaussian projection and residual removal for a finite spin prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

lemma prior_projected_spin_law {A : Type*} [MeasurableSpace A]
    {d k : ℕ} (ν : Measure A) [IsProbabilityMeasure ν] (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : L.transpose * S * L = (v : ℝ) • 1) :
    MeasurePreserving (cavityResidualFieldProjection (A := A) L)
      ((ν.prod (multivariateGaussian 0 S)).prod π)
      ((ν.prod (vectorGaussianLaw k v)).prod π) := by
  have h1 := (MeasurePreserving.id ν).prod
    (cavity_scalar_projected_field_law S hS L v hcov)
  exact h1.prod (MeasurePreserving.id π)

theorem prior_projected_spin_exp_integrable {A : Type*} [MeasurableSpace A]
    {d k : ℕ} (ν : Measure A) [IsProbabilityMeasure ν] (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : L.transpose * S * L = (v : ℝ) • 1)
    (y : A → EuclideanSpace ℝ (Fin d)) (hy : Measurable y) (c : ℝ)
    (hI : Integrable (fun p : Spin k × A =>
      Real.exp (fieldEnergy (cavityProjectField L (y p.2)) p.1))
      (π.prod ν)) :
    Integrable (fun p : (A × EuclideanSpace ℝ (Fin d)) × Spin k =>
      Real.exp (cavityLogFactor 0 L (c • 1)
        (y p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2))
      ((ν.prod (multivariateGaussian 0 S)).prod π) := by
  have hY := (measurable_cavityProjectField L).comp hy
  have hfull := prior_residual_spin_exp_integrable ν π
    (fun a => cavityProjectField L (y a)) hY v c hI.swap
  have hp := prior_projected_spin_law ν π S hS L v hcov
  have hi := hp.hasLaw.integrable_comp hfull
  simpa only [Function.comp_def, cavityResidualFieldProjection,
    cavity_linear_factor_project, cavityProjectField_add] using hi

theorem prior_projected_spin_pair_reduce {A : Type*} [MeasurableSpace A]
    {d k : ℕ} (ν : Measure A) [IsProbabilityMeasure ν] (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : L.transpose * S * L = (v : ℝ) • 1)
    (y : A → EuclideanSpace ℝ (Fin d)) (hy : Measurable y) (c : ℝ)
    (hI : Integrable (fun p : Spin k × A =>
      Real.exp (fieldEnergy (cavityProjectField L (y p.2)) p.1))
      (π.prod ν))
    (D : (Fin 2 → Spin k × A) → ℝ) (hD : Measurable D) :
    referenceReplicaMean ((ν.prod (multivariateGaussian 0 S)).prod π)
      (fun p => cavityLogFactor 0 L (c • 1)
        (y p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)
      (fun σ => D (fun i => ((σ i).2, (σ i).1.1))) =
    referenceReplicaMean (π.prod ν)
      (fun p => fieldEnergy (cavityProjectField L (y p.2)) p.1) D := by
  have hY := (measurable_cavityProjectField L).comp hy
  have hfull := prior_projected_spin_exp_integrable ν π S hS L v hcov y hy c hI
  have hfield := prior_residual_spin_exp_integrable ν π
    (fun a => cavityProjectField L (y a)) hY v c hI.swap
  have hp := cavity_projected_linear_spin_law ν S hS L v hcov y hy c
    π
  have hD' : Measurable (fun σ : Fin 2 → (A × (Fin k → ℝ)) × Spin k =>
      D (fun i => ((σ i).2, (σ i).1.1))) :=
    hD.comp (Measurable.of_eval fun i =>
      ((measurable_pi_apply i).snd).prodMk (measurable_pi_apply i).fst.fst)
  calc
    _ = referenceReplicaMean ((ν.prod (vectorGaussianLaw k v)).prod π)
        (fun p => fieldEnergy (cavityProjectField L (y p.1.1) + p.1.2) p.2 +
          (k : ℝ) * c / 2)
        (fun σ => D (fun i => ((σ i).2, (σ i).1.1))) := by
      exact cavity_posterior_pair_map _ _ _ _ hfull hfield
        (cavityResidualFieldProjection L) (measurable_cavityResidualFieldProjection L) hp _ hD'
    _ = _ := prior_residual_spin_pair_marginal ν π _ hY v c hI D hD

end InvariantIsing

end

end OAI
