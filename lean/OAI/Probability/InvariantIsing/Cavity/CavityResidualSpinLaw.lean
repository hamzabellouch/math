import OAI.Probability.InvariantIsing.Cavity.CavityResidualSpinSampling

namespace OAI

/-! The residual-integrated Gibbs spin marginal, as an equality of
probability measures, and its independent two-replica consequence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem cavity_residual_spin_gibbs_map {N : ℕ} (v : ℝ≥0) (c : ℝ)
    (z : Fin N → ℝ) :
    (gibbsProbability
      ((uniformSpinPrior N : Measure (Spin N)).prod (vectorGaussianLaw N v))
      (fun p => fieldEnergy (z + p.2) p.1 + (N : ℝ) * c / 2)).map Prod.fst =
        gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z) := by
  apply Measure.ext_of_singleton
  intro ε
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change Measure.real _ {ε} = Measure.real _ {ε}
  rw [← integral_indicator_one (measurableSet_singleton ε),
    ← integral_indicator_one (measurableSet_singleton ε)]
  let ν := gibbsProbability
    ((uniformSpinPrior N : Measure (Spin N)).prod (vectorGaussianLaw N v))
    (fun p => fieldEnergy (z + p.2) p.1 + (N : ℝ) * c / 2)
  let F : Spin N → ℝ := ({ε} : Set (Spin N)).indicator 1
  have hm : Measurable (Prod.fst : Spin N × (Fin N → ℝ) → Spin N) := measurable_fst
  have hf : Measurable F := measurable_of_finite F
  exact (integral_map (μ := ν) (φ := Prod.fst) (f := F)
    hm.aemeasurable hf.aestronglyMeasurable).trans (cavity_residual_spin_gibbs_test v c z F)

theorem cavity_residual_spin_pair_mean {N : ℕ} (v : ℝ≥0) (c : ℝ)
    (z₁ z₂ : Fin N → ℝ) (j : Fin N) :
    let ν₁ := gibbsProbability
      ((uniformSpinPrior N : Measure (Spin N)).prod (vectorGaussianLaw N v))
      (fun p => fieldEnergy (z₁ + p.2) p.1 + (N : ℝ) * c / 2)
    let ν₂ := gibbsProbability
      ((uniformSpinPrior N : Measure (Spin N)).prod (vectorGaussianLaw N v))
      (fun p => fieldEnergy (z₂ + p.2) p.1 + (N : ℝ) * c / 2)
    (∫ p, spinValue (p.1.1 j) * spinValue (p.2.1 j) ∂ν₁.prod ν₂) =
      Real.tanh (z₁ j) * Real.tanh (z₂ j) := by
  dsimp only
  rw [integral_prod_mul (fun p : Spin N × (Fin N → ℝ) => spinValue (p.1 j))
    (fun p : Spin N × (Fin N → ℝ) => spinValue (p.1 j)),
    cavity_residual_spin_coordinate_mean, cavity_residual_spin_coordinate_mean]

end InvariantIsing

end

end OAI
