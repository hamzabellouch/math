import OAI.Probability.DilutedSpin.CompoundSuperposition
import OAI.Probability.DilutedSpin.InsertionStability

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] in
lemma iid_energy_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) (n : ℕ) :
    Integrable id (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) := by
  rw [integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  change Integrable (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))
  exact integrable_finsetSum _ (fun i _ => integrable_eval (μ := fun _ : Fin n => μ) (i := i) hi)

omit [NormedSpace ℝ E] in
lemma iid_energy_norm_le (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) (n : ℕ) :
    (∫ x, ‖x‖ ∂Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) ≤
      n*(∫ x, ‖x‖ ∂μ) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  calc
    _ ≤ ∫ x : Fin n → E, ∑ i, ‖x i‖ ∂Measure.pi (fun _ : Fin n => μ) :=
      integral_mono (integrable_finsetSum _ (fun i _ => integrable_eval hi)).norm
        (integrable_finsetSum _ (fun i _ => integrable_comp_eval hi.norm))
        (fun x => norm_sum_le _ _)
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => integrable_comp_eval hi.norm)]
      have he (i : Fin n) : (∫ x : Fin n → E, ‖x i‖ ∂Measure.pi (fun _ : Fin n => μ)) = ∫ x,‖x‖ ∂μ :=
        integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) (by fun_prop)
      simp only [he,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

omit [NormedSpace ℝ E] in
lemma compoundPoisson_integrable_id (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) : Integrable id (compoundPoisson r μ) := by
  unfold compoundPoisson
  apply integrable_sum_measure
  · intro n
    exact (iid_energy_integrable μ hi n).smul_measure ENNReal.ofReal_ne_top
  · have hs := ((hasSum_integral_poissonMeasure (poisson_integrable_count r)).mul_right
      (∫ x, ‖x‖ ∂μ)).summable
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) _ hs
    intro n
    rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity)]
    change (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*_ ≤
      ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*(n:ℝ))*(∫ x,‖x‖ ∂μ)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (iid_energy_norm_le μ hi n) (by positivity)

omit [NormedSpace ℝ E] in
lemma compoundPoisson_norm_le (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) :
    (∫ x, ‖x‖ ∂compoundPoisson r μ) ≤ r*(∫ x, ‖x‖ ∂μ) := by
  have hc : Integrable (fun x : E => ‖x‖) (compoundPoisson r μ) :=
    (compoundPoisson_integrable_id r μ hi).norm
  rw [compoundPoisson,integral_sum_measure hc]
  have hs := (hasSum_integral_poissonMeasure (poisson_integrable_count r)).mul_right (∫ x,‖x‖ ∂μ)
  rw [poisson_mean] at hs
  rw [← hs.tsum_eq]
  apply Summable.tsum_le_tsum
  · intro n
    rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity)]
    change (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*_ ≤
      ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*(n:ℝ))*(∫ x,‖x‖ ∂μ)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (iid_energy_norm_le μ hi n) (by positivity)
  · exact (hasSum_integral_measure hc).summable
  · exact hs.summable

end DilutedSpinGlass

end

end OAI
