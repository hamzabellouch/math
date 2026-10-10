import OAI.Probability.InvariantIsing.Cavity.CavityResidualSpinMarginal

namespace OAI

/-! The residual marginal identity for a deterministic finite spin prior,
including the normalized constrained prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma prior_spin_residual_reorder_law {A : Type*} [MeasurableSpace A] {N : ℕ}
    (ν : Measure A) [IsProbabilityMeasure ν] (π : Measure (Spin N)) [IsProbabilityMeasure π] (v : ℝ≥0) :
    MeasurePreserving (cavitySpinResidualReorder (A := A) (N := N))
      ((ν.prod (vectorGaussianLaw N v)).prod π)
      ((ν.prod π).prod (vectorGaussianLaw N v)) := by
  let μ : Measure (Fin N → ℝ) := vectorGaussianLaw N v
  have hs : MeasurePreserving (Prod.swap : (Fin N → ℝ) × Spin N → _)
      (μ.prod π) (π.prod μ) := ⟨measurable_swap, Measure.prod_swap⟩
  have h1 := measurePreserving_prodAssoc ν μ π
  have h2 := (MeasurePreserving.id ν).prod hs
  have h3 := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc ν π μ)
  exact h3.comp (h2.comp h1)

theorem prior_residual_leaf_spin_marginal {A : Type*} [MeasurableSpace A] {N : ℕ}
    (ν : Measure A) [IsProbabilityMeasure ν] (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (Y : A → Fin N → ℝ) (hY : Measurable Y) (v : ℝ≥0) (c : ℝ)
    (hI : Integrable (fun p : (A × (Fin N → ℝ)) × Spin N =>
      Real.exp (fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2))
      ((ν.prod (vectorGaussianLaw N v)).prod π)) :
    (((ν.prod (vectorGaussianLaw N v)).prod π).tilted
      (fun p => fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2)).map
        (fun p => (p.1.1, p.2)) =
      (ν.prod π).tilted (fun p => fieldEnergy (Y p.1) p.2) := by
  let R := cavitySpinResidualReorder (A := A) (N := N)
  let F : (A × Spin N) × (Fin N → ℝ) → ℝ := fun p =>
    fieldEnergy (Y p.1.1 + p.2) p.1.2 + (N : ℝ) * c / 2
  have hp := prior_spin_residual_reorder_law (N := N) ν π v
  have hF : Measurable F := by unfold F fieldEnergy; fun_prop
  have hIR : Integrable (fun p => Real.exp (F p))
      ((ν.prod π).prod (vectorGaussianLaw N v)) := by
    rw [← hp.map_eq]
    exact (integrable_map_measure hF.exp.aestronglyMeasurable hp.measurable.aemeasurable).mpr hI
  have hR : Measurable R := hp.measurable
  have he : (fun p : (A × (Fin N → ℝ)) × Spin N =>
      fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2) = F ∘ R := rfl
  have hmap : (fun p : (A × (Fin N → ℝ)) × Spin N => (p.1.1, p.2)) = Prod.fst ∘ R := rfl
  rw [he, hmap, ← Measure.map_map measurable_fst hR,
    cavity_tilt_map _ R hR F hF, hp.map_eq]
  rw [cavity_field_residual_marginal (ν.prod π)
    (fun p => Y p.1) (hY.comp measurable_fst) Prod.snd measurable_snd v c hIR,
    cavity_tilt_add_constant]

end InvariantIsing

end

end OAI
