import OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision

namespace OAI

open scoped BigOperators
open Complex Finset MeasureTheory Filter

namespace PiExponent.AnalyticCollision

theorem hasSum_rowTest {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {bound : ℕ → ℝ}
    (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n z, z ∈ Metric.sphere (0 : ℂ) (1 / 2) → ‖F n z‖ ≤ bound n)
    (hsum : Summable bound)
    (hpoint : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), HasSum (fun n => F n z) (f z))
    (ell : ℕ) : HasSum (fun n => rowTest ell (F n)) (rowTest ell f) := by
  simp only [rowTest, cauchyPowerSeries_apply]
  apply HasSum.const_smul
  change HasSum (fun n => ∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • F n (circleMap 0 (1 / 2) θ)))
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • f (circleMap 0 (1 / 2) θ)))
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => (2 : ℝ) ^ ell * bound n)
  · intro n
    apply Measurable.aestronglyMeasurable
    simp only [deriv_circleMap]
    exact (by fun_prop)
  · intro n
    apply Eventually.of_forall
    intro θ _
    have hb := hbound n (circleMap 0 (1 / 2) θ) (circleMap_mem_sphere 0 (by norm_num) θ)
    simp only [deriv_circleMap, norm_smul, norm_mul, norm_I, mul_one, sub_zero,
      norm_pow, norm_div, norm_one, norm_inv, norm_circleMap_zero]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), one_div, inv_div, div_one]
    calc
      _ = (2 : ℝ) ^ ell * ‖F n (circleMap 0 (1 / 2) θ)‖ := by ring
      _ ≤ (2 : ℝ) ^ ell * bound n := mul_le_mul_of_nonneg_left hb (by positivity)
  · exact Eventually.of_forall fun _ _ => hsum.mul_left _
  · simpa only [tsum_mul_left] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (2 : ℝ) ^ ell * ∑' n, bound n)
        volume 0 (2 * Real.pi))
  · apply Eventually.of_forall
    intro θ _
    exact (((hpoint _ (circleMap_mem_sphere 0 (by norm_num) θ)).const_smul _).const_smul _).const_smul _

theorem rowTest_const_mul (ell : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    rowTest ell (fun t => c * f t) = c * rowTest ell f := by
  simp only [rowTest, cauchyPowerSeries_apply, smul_eq_mul]
  have heq : (fun z : ℂ => (1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * (c * f z))) =
      (fun z : ℂ => c * ((1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * f z))) := by
    funext z
    ring
  rw [heq, circleIntegral.integral_const_mul]
  ring

theorem hasSum_translated_row {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : NNReal} (hR : 0 < R) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ), ‖f z‖ ≤ D)
    {center : ℂ} (hc : ‖center‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : ℕ) :
    HasSum (fun d => rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
      normalizedTaylorCoeff f R d)
      (rowTest ell (fun t => f (center + Complex.log (1 + t)))) := by
  have h := hasSum_rowTest
    (F := fun d t => normalizedTaylorCoeff f R d *
      ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)
    (f := fun t => f (center + Complex.log (1 + t)))
    (bound := fun d => D * (1 / 2 : ℝ) ^ d)
    (by intro d; fun_prop) ?_ ?_ ?_ ell
  · convert! h using 1
    funext d
    rw [rowTest_const_mul, mul_comm]
  · intro d t ht
    rw [norm_mul, norm_pow]
    apply mul_le_mul (norm_normalizedTaylorCoeff_le hR hfD d)
    · apply pow_le_pow_left₀ (norm_nonneg _) (norm_shifted_log_div_le_half hR hc _)
      simpa only [Metric.mem_sphere, dist_zero_right] using ht.le
    · positivity
    · exact hD
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left D
  · intro t _
    exact hasSum_normalizedTaylorCoeff hf hR _

end PiExponent.AnalyticCollision

end OAI
