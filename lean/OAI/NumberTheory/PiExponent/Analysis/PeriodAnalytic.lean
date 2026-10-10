import OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation

namespace OAI

open scoped BigOperators
open PiExponent.AnalyticCollision PiExponent.LogTailAnalytic

namespace PiExponent.PeriodAnalytic

noncomputable def periodSeries (b center : ℂ) (h d : ℕ) : PowerSeries ℂ :=
  PowerSeries.C b * (1 + PowerSeries.X) ^ h *
    (PowerSeries.C center + PowerSeries.log ℂ) ^ d

noncomputable def periodFunction (b center : ℂ) (h d : ℕ) (t : ℂ) : ℂ :=
  b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d

theorem hasSum_coeff_C (b z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.C b) * z ^ n) b := by
  convert hasSum_ite_eq 0 b using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

theorem hasSum_coeff_X (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ) * z ^ n) z := by
  convert hasSum_ite_eq 1 z using 1
  funext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem hasSum_coeff_add {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f + g) * z ^ n) (x + y) := by
  simpa only [map_add, add_mul] using hf.add hg

theorem hasSum_periodSeries (b center : ℂ) (h d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (periodSeries b center h d) * z ^ n)
      (periodFunction b center h d z) := by
  exact hasSum_coeff_mul
    (hasSum_coeff_mul (hasSum_coeff_C b z)
      (hasSum_coeff_pow (hasSum_coeff_add (hasSum_coeff_one z) (hasSum_coeff_X z)) h))
    (hasSum_coeff_pow (hasSum_coeff_add (hasSum_coeff_C center z) (hasSum_formal_log hz)) d)

theorem analyticAt_periodFunction (b center : ℂ) (h d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (periodFunction b center h d) z := by
  unfold periodFunction
  apply AnalyticAt.mul
  · fun_prop
  · exact (analyticAt_const.add ((analyticAt_const.add analyticAt_id).clog
      (Complex.mem_slitPlane_of_norm_lt_one hz))).pow d

theorem hasFPowerSeriesAt_periodFunction (b center : ℂ) (h d : ℕ) :
    HasFPowerSeriesAt (periodFunction b center h d)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n
        (periodSeries b center h d))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using
    hasSum_periodSeries b center h d hn

theorem rowTest_periodFunction_eq_coeff (b center : ℂ) (h d ell : ℕ) :
    rowTest ell (periodFunction b center h d) =
      PowerSeries.coeff ell (periodSeries b center h d) := by
  have hd : DifferentiableOn ℂ (periodFunction b center h d)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    apply (analyticAt_periodFunction b center h d ?_).differentiableAt.differentiableWithinAt
    have hz' : ‖z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  have hp := hd.hasFPowerSeriesOnBall (R := (1 / 2 : NNReal)) (by norm_num)
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesAt_periodFunction b center h d)
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p ell (fun _ => 1)) he
  simpa only [rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

theorem rowTest_congr_sphere {f g : ℂ → ℂ}
    (hfg : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), f z = g z) (ell : ℕ) :
    rowTest ell f = rowTest ell g := by
  simp only [rowTest, cauchyPowerSeries_apply]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  change (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • f z =
    (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • g z
  rw [hfg z hz]

theorem periodFunction_eq_exponentialMonomial (b center : ℂ) (h d : ℕ)
    (hcenter : Complex.exp center = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    periodFunction b center h d z =
      exponentialMonomial b (h : ℂ) d (center + Complex.log (1 + z)) := by
  have hz0 : 1 + z ≠ 0 := by
    intro heq
    have heq' : z = -1 := by linear_combination heq
    simp [heq'] at hz
  unfold periodFunction exponentialMonomial
  rw [Complex.exp_nat_mul, Complex.exp_add, hcenter, Complex.exp_log hz0, one_mul]

theorem exp_period_center (j : ℕ) :
    Complex.exp ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
  rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

theorem rowTest_exponentialMonomial_eq_coeff (b : ℂ) (j h d ell : ℕ) :
    rowTest ell (fun t => exponentialMonomial b (h : ℂ) d
      ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + Complex.log (1 + t))) =
    PowerSeries.coeff ell (periodSeries b ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) h d) := by
  rw [← rowTest_periodFunction_eq_coeff]
  apply rowTest_congr_sphere
  intro t ht
  symm
  apply periodFunction_eq_exponentialMonomial _ _ _ _ (exp_period_center j)
  have hn : ‖t‖ = (1 / 2 : ℝ) := by simpa only [Metric.mem_sphere, dist_zero_right] using ht
  rw [hn]
  norm_num

theorem periodMonomial_coeff_eq_rowTest {m : ℕ} (j h ell : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff ell ((MatrixTranslation.periodMonomial j
      (2 * (Real.pi : ℂ) * Complex.I) h a).coeff A) =
    rowTest ell (fun t => exponentialMonomial
      ((∏ i, (a i).choose (A i) : ℕ) : ℂ) (h : ℂ) (∑ i : Fin m, (a i - A i))
      ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + Complex.log (1 + t))) := by
  rw [rowTest_exponentialMonomial_eq_coeff, MatrixTranslation.periodMonomial_coeff]
  simp only [periodSeries, MatrixTranslation.periodCoordinate, map_natCast]

theorem norm_binomial_product_le {m : ℕ} (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ)‖ ≤ (2 : ℝ) ^ (∑ i, a i) := by
  rw [Complex.norm_natCast]
  have h : (∏ i, (a i).choose (A i) : ℕ) ≤ 2 ^ (∑ i, a i) := by
    calc
      _ ≤ ∏ i, 2 ^ a i := Finset.prod_le_prod (fun i _ => Nat.choose_le_two_pow _ _)
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  exact_mod_cast h

noncomputable def columnFunction {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) : ℂ → ℂ :=
  exponentialMonomial ((∏ i, (a i).choose (A i) : ℕ) : ℂ) (h : ℂ)
    (∑ i : Fin m, (a i - A i))

theorem differentiable_columnFunction {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) : Differentiable ℂ (columnFunction h a A) :=
  differentiable_exponentialMonomial _ _ _

theorem norm_columnFunction_le {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (w : Fin m → ℝ) {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hcol : w0 * h + ∑ i, w i * a i ≤ H)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖columnFunction h a A z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  have hwpos (i) : 0 ≤ w i := hws.le.trans (hw i)
  have hsum0 : 0 ≤ ∑ i, w i * a i := Finset.sum_nonneg fun i _ => mul_nonneg (hwpos i) (Nat.cast_nonneg _)
  have hh : ‖(h : ℂ)‖ ≤ H / w0 := by
    rw [Complex.norm_natCast, le_div_iff₀ hw0]
    nlinarith
  have htot : (((∑ i, a i : ℕ) : ℝ)) ≤ H / wstar := by
    rw [le_div_iff₀ hws]
    have hs : wstar * ∑ i, (a i : ℝ) ≤ ∑ i, w i * a i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
    have hcast : ((∑ i, a i : ℕ) : ℝ) = ∑ i, (a i : ℝ) := by push_cast; rfl
    rw [hcast]
    nlinarith
  exact norm_exponentialMonomial_le_exp_budget _ _ _ _ hR hH hw0 hws hz
    (norm_binomial_product_le a A) hh
    (Finset.sum_le_sum fun i _ => Nat.sub_le _ _) htot

end PiExponent.PeriodAnalytic

end OAI
