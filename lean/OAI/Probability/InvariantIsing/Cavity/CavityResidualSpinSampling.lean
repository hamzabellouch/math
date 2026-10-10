import OAI.Probability.InvariantIsing.Cavity.CavityScalarSpin
import OAI.Probability.InvariantIsing.Fields.FieldSpinProduct

namespace OAI

/-! Integrating the ordinary Gaussian residual in the actual joint Gibbs
law leaves the finite Ising Gibbs law of the effective scalar field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma cavity_residual_spin_weight_integrable {N : ℕ} (v : ℝ≥0) (c : ℝ)
    (z : Fin N → ℝ) (F : Spin N → ℝ) :
    Integrable (fun p : Spin N × (Fin N → ℝ) =>
      Real.exp (fieldEnergy (z + p.2) p.1 + (N : ℝ) * c / 2) * F p.1)
      ((uniformSpinPrior N : Measure (Spin N)).prod (vectorGaussianLaw N v)) := by
  apply (integrable_prod_iff (by
    apply Measurable.aestronglyMeasurable
    have hF : Measurable F := measurable_of_finite F
    unfold fieldEnergy
    fun_prop)).mpr
  constructor
  · exact ae_of_all _ fun ε => (cavity_residual_spin_integrable v c z ε).mul_const (F ε)
  · exact Integrable.of_finite

theorem cavity_residual_spin_weight_integral {N : ℕ} (v : ℝ≥0) (c : ℝ)
    (z : Fin N → ℝ) (F : Spin N → ℝ) :
    (∫ p : Spin N × (Fin N → ℝ),
      Real.exp (fieldEnergy (z + p.2) p.1 + (N : ℝ) * c / 2) * F p.1
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (vectorGaussianLaw N v))) =
        Real.exp ((N : ℝ) * (c + v) / 2) *
          ∫ ε, Real.exp (fieldEnergy z ε) * F ε ∂(uniformSpinPrior N : Measure (Spin N)) := by
  rw [integral_prod _ (cavity_residual_spin_weight_integrable v c z F)]
  simp_rw [integral_mul_const, cavity_residual_spin_integral, Real.exp_add]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun ε => by ring

theorem cavity_residual_spin_gibbs_test {N : ℕ} (v : ℝ≥0) (c : ℝ)
    (z : Fin N → ℝ) (F : Spin N → ℝ) :
    (∫ p : Spin N × (Fin N → ℝ), F p.1
      ∂gibbsProbability
        ((uniformSpinPrior N : Measure (Spin N)).prod (vectorGaussianLaw N v))
        (fun p => fieldEnergy (z + p.2) p.1 + (N : ℝ) * c / 2)) =
      ∫ ε, F ε ∂gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z) := by
  have hi := cavity_residual_spin_weight_integrable v c z (fun _ => 1)
  simp only [mul_one] at hi
  rw [gibbsProbability_eq_tilted _ _ hi,
    gibbsProbability_eq_tilted _ _ Integrable.of_finite,
    integral_tilted_eq_div, integral_tilted_eq_div,
    cavity_residual_spin_weight_integral]
  have hZ := cavity_residual_spin_weight_integral v c z (fun _ => 1)
  simp only [mul_one] at hZ
  rw [hZ, mul_div_mul_left _ _ (Real.exp_ne_zero _)]

theorem cavity_residual_spin_coordinate_mean {N : ℕ} (v : ℝ≥0) (c : ℝ)
    (z : Fin N → ℝ) (j : Fin N) :
    (∫ p : Spin N × (Fin N → ℝ), spinValue (p.1 j)
      ∂gibbsProbability
        ((uniformSpinPrior N : Measure (Spin N)).prod (vectorGaussianLaw N v))
        (fun p => fieldEnergy (z + p.2) p.1 + (N : ℝ) * c / 2)) =
      Real.tanh (z j) := by
  rw [cavity_residual_spin_gibbs_test v c z (fun ε => spinValue (ε j)),
    fieldSpinGibbs_coordinate_mean]

end InvariantIsing

end

end OAI
