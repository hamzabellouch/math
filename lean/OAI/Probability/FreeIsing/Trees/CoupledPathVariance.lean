import OAI.Probability.FreeIsing.Trees.CoupledPathProducts
import OAI.Probability.FreeIsing.Trees.PathVariance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_weighted_path_log_sq_le_twice_unweighted
    {ι : Type*} (s : Finset ι) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ) :
    (∫ ω, ((∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2 +
      (∏ i ∈ s, responseAttenuation theta (Y i ω)) ^ 2) *
      (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ) ≤
      2 * ∫ ω, (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ := by
  have hQ := (integral_prod_responseAttenuation_sub_sq_le s hθ hX hY hInt).1
  have hZ := memLp_sum_log_responseAttenuation_sub s hθ hX hY hInt
  calc
    _ ≤ ∫ ω, 2 * (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ := by
      apply integral_mono hQ (hZ.integrable_sq.const_mul 2)
      intro ω
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
      have hp' := prod_responseAttenuation_pos s (fun i => Y i ω) hθ
      have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
      have hl' := prod_attenuation_le_one s (fun i => Y i ω) hθ
      nlinarith
    _ = _ := integral_const_mul _ _

theorem integral_weighted_path_log_sq_le_geometric_pair_bound
    (s : Finset ℤ) {theta q S : ℝ} (hθ : theta ^ 2 ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    {X Y : ℤ → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      |∫ ω, (Real.log (responseAttenuation theta (X i ω)) -
          Real.log (responseAttenuation theta (Y i ω))) *
        (Real.log (responseAttenuation theta (X j ω)) -
          Real.log (responseAttenuation theta (Y j ω))) ∂μ| ≤
        S * pathCorrelationKernel q (j - i)) :
    (∫ ω, ((∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2 +
      (∏ i ∈ s, responseAttenuation theta (Y i ω)) ^ 2) *
      (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ) ≤
      2 * (s.card : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  let D := fun i ω => Real.log (responseAttenuation theta (X i ω)) -
    Real.log (responseAttenuation theta (Y i ω))
  have hD : ∀ i ∈ s, MemLp (D i) 2 μ := by
    intro i hi
    have hm := (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
    exact (memLp_two_iff_integrable_sq
      (((hm.comp (hX i hi)).sub (hm.comp (hY i hi))).aestronglyMeasurable)).2
      (integrable_log_responseAttenuation_sub_sq hθ (hX i hi) (hY i hi) (hInt i hi))
  have hsum := integral_sum_sq_le_geometric_pair_bound s D hq0 hq1 hS hD hpair
  calc
    _ ≤ 2 * ∫ ω, (∑ i ∈ s, D i ω) ^ 2 ∂μ :=
      integral_weighted_path_log_sq_le_twice_unweighted s hθ hX hY hInt
    _ ≤ 2 * ((s.card : ℝ) * S * (2 / (1 - q) ^ 2 - 1)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

theorem integral_weighted_path_log_sq_le_of_marginals_and_covariance
    [IsProbabilityMeasure μ] (s : Finset ℤ)
    {theta q S : ℝ} (hθ : theta ^ 2 ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    {X Y : ℤ → Ω → ℝ}
    (hXm : ∀ i ∈ s, Measurable (X i)) (hYm : ∀ i ∈ s, Measurable (Y i))
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hlaw : ∀ i ∈ s, IdentDistrib (X i) (Y i) μ μ)
    (hcov : ∀ i ∈ s, ∀ j ∈ s,
      |covariance
        (fun ω => Real.log (responseAttenuation theta (X i ω)) -
          Real.log (responseAttenuation theta (Y i ω)))
        (fun ω => Real.log (responseAttenuation theta (X j ω)) -
          Real.log (responseAttenuation theta (Y j ω))) μ| ≤
        S * pathCorrelationKernel q (j - i)) :
    (∫ ω, ((∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2 +
      (∏ i ∈ s, responseAttenuation theta (Y i ω)) ^ 2) *
      (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ) ≤
      2 * (s.card : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ := by
    intro i hi
    exact ((hX i hi).sub ((hlaw i hi).memLp_snd (hX i hi))).integrable_sq
  apply integral_weighted_path_log_sq_le_geometric_pair_bound
    s hθ hq0 hq1 hS hXm hYm hInt
  intro i hi j hj
  have hDi := centered_log_response_discrepancy_of_identDistrib hθ (hX i hi) (hlaw i hi)
  have hDj := centered_log_response_discrepancy_of_identDistrib hθ (hX j hj) (hlaw j hj)
  have h := hcov i hi j hj
  rw [covariance_eq_sub hDi.1 hDj.1, hDi.2, hDj.2, zero_mul, sub_zero] at h
  exact h

end Problem367

end

end OAI
