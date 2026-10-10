import OAI.Probability.InvariantIsing.Fields.PriorResidualIntegrability
import OAI.Probability.InvariantIsing.Cavity.CavityPosteriorPair

namespace OAI

/-! Exact residual-free two-spin law with the constrained prior retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem prior_residual_spin_pair_marginal {A : Type*} [MeasurableSpace A] {N : ℕ}
    (ν : Measure A) [IsProbabilityMeasure ν] (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (Y : A → Fin N → ℝ) (hY : Measurable Y) (v : ℝ≥0) (c : ℝ)
    (hI : Integrable (fun p : Spin N × A => Real.exp (fieldEnergy (Y p.2) p.1))
      (π.prod ν))
    (D : (Fin 2 → Spin N × A) → ℝ) (hD : Measurable D) :
    referenceReplicaMean ((ν.prod (vectorGaussianLaw N v)).prod π)
      (fun p => fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2)
      (fun σ => D (fun i => ((σ i).2, (σ i).1.1))) =
    referenceReplicaMean (π.prod ν)
      (fun p => fieldEnergy (Y p.2) p.1) D := by
  have hI' : Integrable (fun p : A × Spin N => Real.exp (fieldEnergy (Y p.1) p.2))
      (ν.prod π) := hI.swap
  have hfull := prior_residual_spin_exp_integrable ν π Y hY v c hI'
  let f : (A × (Fin N → ℝ)) × Spin N → Spin N × A := fun p => (p.2, p.1.1)
  have hf : Measurable f := measurable_snd.prodMk measurable_fst.fst
  have hJ : Measurable (fun p : Spin N × A => fieldEnergy (Y p.2) p.1) := by
    unfold fieldEnergy
    fun_prop
  have hmap :
      ((((ν.prod (vectorGaussianLaw N v)).prod π).tilted
        (fun p => fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2)).map f) =
      (π.prod ν).tilted
        (fun p => fieldEnergy (Y p.2) p.1) := by
    change (((ν.prod (vectorGaussianLaw N v)).prod π).tilted
      (fun p => fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2)).map
      (Prod.swap ∘ (fun p : (A × (Fin N → ℝ)) × Spin N =>
      (p.1.1, p.2))) = _
    rw [← Measure.map_map measurable_swap (measurable_fst.fst.prodMk measurable_snd),
      prior_residual_leaf_spin_marginal ν π Y hY v c hfull]
    have h := cavity_tilt_map (ν.prod π) Prod.swap measurable_swap
      (fun p : Spin N × A => fieldEnergy (Y p.2) p.1) hJ
    simpa only [Function.comp_def, Prod.swap, Measure.prod_swap] using h
  exact cavity_posterior_pair_map _ _ _ _ hfull hI f hf hmap D hD

end InvariantIsing

end

end OAI
