import OAI.Probability.InvariantIsing.Cavity.CavityResidualIntegrability
import OAI.Probability.InvariantIsing.Cavity.CavityContinuousReplicaTilt

namespace OAI

/-! Two-replica observables under a marginal of the full spin tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma cavity_reference_pair_eq_tilted {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hI : Integrable (fun x => Real.exp (H x)) ν)
    (D : (Fin 2 → X) → ℝ) :
    referenceReplicaMean ν H D =
      ∫ σ, D σ ∂Measure.pi (fun _ : Fin 2 => ν.tilted H) := by
  rw [referenceReplicaMean_eq_ratio, ← cavity_continuous_replica_tilt ν H hI 2,
    integral_tilted_eq_div]

lemma cavity_posterior_pair_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : X → ℝ) (J : Y → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) μ)
    (hJ : Integrable (fun y => Real.exp (J y)) ν)
    (f : X → Y) (hf : Measurable f) (hmap : (μ.tilted H).map f = ν.tilted J)
    (D : (Fin 2 → Y) → ℝ) (hD : Measurable D) :
    referenceReplicaMean μ H (fun σ => D (fun i => f (σ i))) =
      referenceReplicaMean ν J D := by
  rw [cavity_reference_pair_eq_tilted μ H hH, cavity_reference_pair_eq_tilted ν J hJ]
  have hp : MeasurePreserving (fun σ : Fin 2 → X => fun i => f (σ i))
      (Measure.pi (fun _ : Fin 2 => μ.tilted H))
      (Measure.pi (fun _ : Fin 2 => ν.tilted J)) := by
    refine ⟨Measurable.of_eval (fun i => hf.comp (measurable_pi_apply i)), ?_⟩
    simpa only [hmap] using Measure.pi_map_pi
      (μ := fun _ : Fin 2 => μ.tilted H) (f := fun _ : Fin 2 => f)
      (fun _ => hf.aemeasurable)
  exact hp.hasLaw.integral_comp hD.aestronglyMeasurable

theorem cavity_residual_spin_pair_marginal {A : Type*} [MeasurableSpace A] {N : ℕ}
    (ν : Measure A) [IsProbabilityMeasure ν]
    (Y : A → Fin N → ℝ) (hY : Measurable Y) (v : ℝ≥0) (c : ℝ)
    (hI : Integrable (fun p : Spin N × A => Real.exp (fieldEnergy (Y p.2) p.1))
      ((uniformSpinPrior N : Measure (Spin N)).prod ν))
    (D : (Fin 2 → Spin N × A) → ℝ) (hD : Measurable D) :
    referenceReplicaMean ((ν.prod (vectorGaussianLaw N v)).prod (uniformSpinPrior N))
      (fun p => fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2)
      (fun σ => D (fun i => ((σ i).2, (σ i).1.1))) =
    referenceReplicaMean ((uniformSpinPrior N : Measure (Spin N)).prod ν)
      (fun p => fieldEnergy (Y p.2) p.1) D := by
  have hI' : Integrable (fun p : A × Spin N => Real.exp (fieldEnergy (Y p.1) p.2))
      (ν.prod (uniformSpinPrior N)) := hI.swap
  have hfull := cavity_residual_spin_exp_integrable ν Y hY v c hI'
  let f : (A × (Fin N → ℝ)) × Spin N → Spin N × A := fun p => (p.2, p.1.1)
  have hf : Measurable f := measurable_snd.prodMk measurable_fst.fst
  have hJ : Measurable (fun p : Spin N × A => fieldEnergy (Y p.2) p.1) := by
    unfold fieldEnergy
    fun_prop
  have hmap :
      ((((ν.prod (vectorGaussianLaw N v)).prod (uniformSpinPrior N)).tilted
        (fun p => fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2)).map f) =
      ((uniformSpinPrior N : Measure (Spin N)).prod ν).tilted
        (fun p => fieldEnergy (Y p.2) p.1) := by
    change (((ν.prod (vectorGaussianLaw N v)).prod (uniformSpinPrior N)).tilted
      (fun p => fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2)).map
      (Prod.swap ∘ (fun p : (A × (Fin N → ℝ)) × Spin N =>
      (p.1.1, p.2))) = _
    rw [← Measure.map_map measurable_swap (measurable_fst.fst.prodMk measurable_snd),
      cavity_residual_leaf_spin_marginal ν Y hY v c hfull]
    have h := cavity_tilt_map (ν.prod (uniformSpinPrior N)) Prod.swap measurable_swap
      (fun p : Spin N × A => fieldEnergy (Y p.2) p.1) hJ
    simpa only [Function.comp_def, Prod.swap, Measure.prod_swap] using h
  exact cavity_posterior_pair_map _ _ _ _ hfull hI f hf hmap D hD

end InvariantIsing

end

end OAI
