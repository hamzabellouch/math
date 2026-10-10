import OAI.Probability.InvariantIsing.Cavity.CavityResidualSpinMarginal

namespace OAI

/-! The full ordinary-residual exponential moment follows from the
residual-free spin/leaf exponential moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem cavity_residual_spin_exp_integrable {A : Type*} [MeasurableSpace A] {N : ℕ}
    (ν : Measure A) [IsProbabilityMeasure ν]
    (Y : A → Fin N → ℝ) (hY : Measurable Y) (v : ℝ≥0) (c : ℝ)
    (hI : Integrable (fun p : A × Spin N => Real.exp (fieldEnergy (Y p.1) p.2))
      (ν.prod (uniformSpinPrior N))) :
    Integrable (fun p : (A × (Fin N → ℝ)) × Spin N =>
      Real.exp (fieldEnergy (Y p.1.1 + p.1.2) p.2 + (N : ℝ) * c / 2))
      ((ν.prod (vectorGaussianLaw N v)).prod (uniformSpinPrior N)) := by
  let F : (A × Spin N) × (Fin N → ℝ) → ℝ := fun p =>
    fieldEnergy (Y p.1.1 + p.2) p.1.2 + (N : ℝ) * c / 2
  have hE : Measurable (fun p : (Fin N → ℝ) × Spin N => fieldEnergy p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact (measurable_pi_apply σ).comp (measurable_fieldEnergy_map N)
  have hY' : Measurable (fun p : (A × Spin N) × (Fin N → ℝ) => Y p.1.1 + p.2) :=
    (hY.comp measurable_fst.fst).add measurable_snd
  have hF : Measurable F :=
    (hE.comp (hY'.prodMk measurable_fst.snd)).add_const _
  have haug : Integrable (fun p => Real.exp (F p))
      ((ν.prod (uniformSpinPrior N)).prod (vectorGaussianLaw N v)) := by
    apply (integrable_prod_iff hF.exp.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun p => cavity_residual_spin_integrable v c (Y p.1) p.2
    · have h := hI.mul_const (Real.exp ((N : ℝ) * (c + v) / 2))
      convert h using 1
      funext p
      simp only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [cavity_residual_spin_integral, Real.exp_add]
  have hp := cavity_spin_residual_reorder_law (N := N) ν v
  simpa only [Function.comp_def, F, cavitySpinResidualReorder] using
    hp.hasLaw.integrable_comp haug

end InvariantIsing

end

end OAI
