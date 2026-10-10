import OAI.Analysis.LpDimension.PowerEstimates

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set
open scoped BigOperators Topology Matrix ENNReal NNReal
universe u

namespace SubpolynomialLp

lemma powerIntensity_scaling (p c : ℝ) (hp : 0 < p) (hc : 0 < c) (f : ℝ → ℝ) :
    (∫ r, f (c*r) ∂powerIntensity p) = c^p * ∫ r, f r ∂powerIntensity p := by
  rw [powerIntensity_integral p hp, powerIntensity_integral p hp]
  have he : (fun r : ℝ => (p*r^(-p-1)) • f (c*r)) =ᵐ[volume.restrict (Ioi 0)]
      fun r => c^(p+1)*((p*(c*r)^(-p-1)) • f (c*r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp only [smul_eq_mul, Real.mul_rpow hc.le (le_of_lt hr)]
    rw [show c^(p+1)*(p*(c^(-p-1)*r^(-p-1))*f (c*r)) =
      (c^(p+1)*c^(-p-1))*(p*r^(-p-1)*f (c*r)) by ring,
      ← Real.rpow_add hc, show p+1+(-p-1) = 0 by ring, Real.rpow_zero, one_mul]
  rw [integral_congr_ae he, integral_const_mul,
    integral_comp_mul_left_Ioi (fun r => (p*r^(-p-1)) • f r) 0 hc,
    mul_zero, smul_eq_mul, ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hc]
  congr 2
  ring

lemma powerIntensity_even_scaling (p c : ℝ) (hp : 0 < p) (f : ℝ → ℝ)
    (hf : ∀ x, f (-x) = f x) (hf0 : f 0 = 0) :
    (∫ r, f (c*r) ∂powerIntensity p) = |c|^p * ∫ r, f r ∂powerIntensity p := by
  rcases lt_trichotomy c 0 with hc|hc|hc
  · have he (r : ℝ) : f (c*r) = f ((-c)*r) := by rw [neg_mul, hf]
    simp_rw [he]
    rw [powerIntensity_scaling p (-c) hp (neg_pos.mpr hc) f, abs_of_neg hc]
  · subst c
    simp [hf0, Real.zero_rpow hp.ne']
  · rw [powerIntensity_scaling p c hp hc f, abs_of_pos hc]

def pareto (p : ℝ) : Measure ℝ := (powerIntensity p).restrict (Ioi 1)

lemma pareto_probability (p : ℝ) (hp : 0 < p) : IsProbabilityMeasure (pareto p) := by
  constructor
  simp only [pareto, Measure.restrict_apply_univ, powerIntensity_tail p 1 hp zero_lt_one, Real.one_rpow, ENNReal.ofReal_one]

lemma powerIntensity_supported_positive (p : ℝ) : ∀ᵐ r ∂powerIntensity p, 0 < r := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

lemma pareto_integral_eq_full (p c : ℝ) (hc : |c| ≤ 1) (f : ℝ → ℝ)
    (hf : ∀ x, |x| ≤ 1 → f x = 0) :
    (∫ r, f (c*r) ∂pareto p) = ∫ r, f (c*r) ∂powerIntensity p := by
  rw [pareto, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [powerIntensity_supported_positive p] with r hr
  by_cases h : r ∈ Ioi (1:ℝ)
  · simp only [indicator_of_mem h]
  · rw [indicator_of_notMem h]
    exact (hf (c*r) (by
      have hr1 : r ≤ 1 := le_of_not_gt h
      rw [abs_mul, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_right hc hr.le).trans (by linarith))).symm

lemma pareto_even_scaling (p c : ℝ) (hp : 0 < p) (hc : |c| ≤ 1) (f : ℝ → ℝ)
    (hf : ∀ x, f (-x) = f x) (hzero : ∀ x, |x| ≤ 1 → f x = 0) :
    (∫ r, f (c*r) ∂pareto p) = |c|^p * ∫ r, f r ∂pareto p := by
  rw [pareto_integral_eq_full p c hc f hzero,
    powerIntensity_even_scaling p c hp f hf (hzero 0 (by norm_num))]
  have h := pareto_integral_eq_full p 1 (by norm_num) f hzero
  simp only [one_mul] at h
  rw [h]

end SubpolynomialLp

end

end OAI
