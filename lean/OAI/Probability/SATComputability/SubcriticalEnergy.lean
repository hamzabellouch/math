import OAI.Probability.SATComputability.PoissonSATProbability

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem relaxedPoissonMinimum_mean_sq (n : ℕ) [NeZero n] (a : ℝ≥0) :
    auxiliaryPoissonProbability n a * (relaxedPoissonMinimum n a)^2 ≤
      3/2 * (a : ℝ)*n := by
  have h := rootMinimum_mean_sq n (finiteUniform (RelaxedClause n)) (a*n)
  rw [rootSatisfiableProbability_eq_auxiliary, poissonRootAverage_minimum_eq] at h
  simpa only [auxiliaryPoissonProbability, NNReal.coe_mul, NNReal.coe_natCast, mul_assoc] using h

theorem relaxedPoissonMinimum_subcritical {a : ℝ≥0}
    (ha : (a : ℝ) < limitingCenter 3) :
    Tendsto (fun n : ℕ => relaxedPoissonMinimum n a / n) atTop (nhds 0) := by
  let c := transferFactor 3 / 4
  have hc : 0 < c := div_pos (transferFactor_pos 3) (by norm_num)
  let K := (3/2 : ℝ) * a / c
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (K/n)) atTop (nhds 0) := by
    have ht := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul K
    simpa only [Function.comp_apply, ← div_eq_mul_inv, mul_zero, Real.sqrt_zero] using ht.sqrt
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    div_nonneg (relaxedPoissonMinimum_nonneg n a) (Nat.cast_nonneg n))) _ hlim
  filter_upwards [auxiliaryPoissonProbability_subcritical ha, eventually_gt_atTop 0] with n hp hn
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hv := relaxedPoissonMinimum_mean_sq n a
  have hsq : (relaxedPoissonMinimum n a)^2 ≤ K*n := by
    dsimp only [K]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    rw [mul_comm _ c]
    exact (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans hv
  have hd := div_le_div_of_nonneg_right hsq (sq_nonneg (n : ℝ))
  have he : (relaxedPoissonMinimum n a/n)^2 ≤ K/n := by
    rw [div_pow]
    convert hd using 1
    field_simp
  have hnon := div_nonneg (relaxedPoissonMinimum_nonneg n a) hn'.le
  simpa only [Real.sqrt_sq hnon] using Real.sqrt_le_sqrt he

end FixedClauseThreshold.Computability

end OAI
