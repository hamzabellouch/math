import OAI.Probability.InvariantIsing.Fields.FieldSpinSampling
import OAI.Probability.InvariantIsing.Fields.SpinFactorization

namespace OAI

/-! The finite Ising spin law with a scalar field at each site factors
into the actual one-site Gibbs kernels, including its two-spin tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal

namespace InvariantIsing

lemma uniformSpinPrior_eq_product (N : ℕ) :
    (uniformSpinPrior N : Measure (Spin N)) =
      Measure.pi (fun _ : Fin N => (PMF.uniformOfFintype Bool).toMeasure) := by
  apply Measure.ext_of_singleton
  intro σ
  rw [Measure.pi_singleton]
  simp only [uniformSpinPrior, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  simp [Spin, ENNReal.inv_pow]

theorem fieldSpinGibbs_eq_product {N : ℕ} (z : Fin N → ℝ) :
    gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z) =
      Measure.pi (fun i => scalarSpinKernel (z i)) := by
  let π : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
  have hz (i : Fin N) : 0 < ∫ σ, Real.exp (z i * spinValue σ) ∂π :=
    integral_exp_pos Integrable.of_finite
  have hZ : referencePartition (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z) =
      ∏ i, ∫ σ, Real.exp (z i * spinValue σ) ∂π := by
    rw [referencePartition, uniformSpinPrior_eq_product]
    simp only [fieldEnergy, Real.exp_sum]
    exact integral_fintype_prod_eq_prod (fun i σ => Real.exp (z i * spinValue σ))
  rw [gibbsProbability_eq_tilted _ _ Integrable.of_finite]
  apply Measure.ext_of_singleton
  intro σ
  rw [tilted_singleton, hZ, uniformSpinPrior_eq_product, Measure.pi_singleton,
    Measure.pi_singleton]
  have hi (i : Fin N) : scalarSpinKernel (z i) = π.tilted (fun σ => z i * spinValue σ) :=
    gibbsProbability_eq_tilted π _ Integrable.of_finite
  simp_rw [hi, tilted_singleton]
  simp only [referencePartition]
  rw [Finset.prod_mul_distrib,
    ← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => div_nonneg (Real.exp_pos _).le (hz i).le),
    Finset.prod_div_distrib, fieldEnergy, Real.exp_sum]

theorem fieldSpinGibbs_coordinate_mean {N : ℕ} (z : Fin N → ℝ) (j : Fin N) :
    (∫ σ, spinValue (σ j)
      ∂gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z)) =
        Real.tanh (z j) := by
  rw [fieldSpinGibbs_eq_product, integral_comp_eval]
  · exact scalarSpinKernel_mean (z j)
  · exact (measurable_of_finite spinValue).aestronglyMeasurable

theorem fieldSpinGibbs_pair_mean {N : ℕ} (z₁ z₂ : Fin N → ℝ) (j : Fin N) :
    (∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j)
      ∂(gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z₁)).prod
        (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z₂))) =
      Real.tanh (z₁ j) * Real.tanh (z₂ j) := by
  rw [integral_prod_mul (fun σ : Spin N => spinValue (σ j))
    (fun σ : Spin N => spinValue (σ j)),
    fieldSpinGibbs_coordinate_mean, fieldSpinGibbs_coordinate_mean]

end InvariantIsing

end

end OAI
