import OAI.Geometry.CylinderCovering.Nilpotent.CostDefinitions
import OAI.Geometry.CylinderCovering.Angular.Taylor

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace CylinderCovering.Nilpotent

lemma v_nonneg (p : ℝ) : 0 ≤ v p := by unfold v; positivity

lemma a_nonneg (p : ℝ) : 0 ≤ a p := by
  unfold a
  exact div_nonneg (mul_nonneg (sq_nonneg p) (v_nonneg p)) (by norm_num)

lemma speedSq_nonneg (p : ℝ) : 0 ≤ speedSq p := by unfold speedSq; positivity

lemma parameter_bounds {p : ℝ} (hp : |p| ≤ 1) :
    a p ≤ 1 / 8 ∧ speedSq p ≤ 3 / 4 := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith [sq_abs p, abs_nonneg p]
  have hp4 : p ^ 4 ≤ 1 := by nlinarith [sq_nonneg (p ^ 2 - 1)]
  constructor <;> dsimp [a, v, speedSq, w] <;> nlinarith [sq_nonneg p]

lemma sqrt_denominator_ge_one (k p : ℝ) :
    1 ≤ Real.sqrt (1 + k ^ 2 * speedSq p) := by
  have h := mul_nonneg (sq_nonneg k) (speedSq_nonneg p)
  apply (Real.le_sqrt (by norm_num) (by linarith : 0 ≤ 1 + k ^ 2 * speedSq p)).2
  nlinarith

lemma quadraticCoefficient_eq (p : ℝ) :
    quadraticCoefficient p = (-1 - 2 * p ^ 2 + 7 * p ^ 4) / 256 := by
  unfold quadraticCoefficient a speedSq v w
  ring

theorem integrand_remainder {k p : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hp : |p| ≤ 1) :
    |integrand k p - (1 / 8 + k ^ 2 * quadraticCoefficient p)| ≤ 2 * k ^ 3 := by
  have ha0 := a_nonneg p
  have hA0 := speedSq_nonneg p
  obtain ⟨ha1, hA1⟩ := parameter_bounds hp
  have hk2 : k ^ 2 ≤ 1 := pow_le_one₀ hk0 hk1
  have hk3 : k ^ 3 ≤ 1 := pow_le_one₀ hk0 hk1
  have hk30 : 0 ≤ k ^ 3 := pow_nonneg hk0 _
  have hk43 : k ^ 4 ≤ k ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_left hk1 hk30]
  have hka : k ^ 2 * a p ≤ 1 / 8 := by
    nlinarith only [mul_le_mul hk2 ha1 ha0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hTaylor := AngularTaylor.bounded_product_remainder
    (sq_nonneg k) hk2 ha0 (by linarith : a p ≤ 1 / 4)
    hA0 (by linarith : speedSq p ≤ 1)
  have hq := sqrt_denominator_ge_one k p
  have hqpos : 0 < Real.sqrt (1 + k ^ 2 * speedSq p) := by linarith
  let delta := height k p ^ 2 - (1 / 2 + k ^ 2 * a p) ^ 2
  have hdelta : delta = k ^ 3 * (1 + 2 * k ^ 2 * a p + k ^ 3) := by
    dsimp [delta, height]
    ring
  have hd0 : 0 ≤ delta := by rw [hdelta]; positivity
  have hd1 : delta ≤ (9 / 4) * k ^ 3 := by
    rw [hdelta]
    have h : 1 + 2 * k ^ 2 * a p + k ^ 3 ≤ 9 / 4 := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left h hk30]
  have hpert : |delta / Real.sqrt (1 + k ^ 2 * speedSq p)| ≤ (9 / 4) * k ^ 3 := by
    rw [abs_of_nonneg (div_nonneg hd0 hqpos.le)]
    exact (div_le_self hd0 hq).trans hd1
  have hid : integrand k p - (1 / 8 + k ^ 2 * quadraticCoefficient p) =
      (((1 / 2 + k ^ 2 * a p) ^ 2 / Real.sqrt (1 + k ^ 2 * speedSq p) -
        (1 / 4 + k ^ 2 * (a p - speedSq p / 8))) +
        delta / Real.sqrt (1 + k ^ 2 * speedSq p)) / 2 := by
    dsimp [integrand, quadraticCoefficient, delta]
    ring
  rw [hid, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsum := abs_add_le
    ((1 / 2 + k ^ 2 * a p) ^ 2 / Real.sqrt (1 + k ^ 2 * speedSq p) -
      (1 / 4 + k ^ 2 * (a p - speedSq p / 8)))
    (delta / Real.sqrt (1 + k ^ 2 * speedSq p))
  nlinarith only [hTaylor, hpert, hsum, hk43, hk30]

lemma continuous_a : Continuous a := by unfold a v; fun_prop

lemma continuous_speedSq : Continuous speedSq := by unfold speedSq v w; fun_prop

lemma continuous_quadraticCoefficient : Continuous quadraticCoefficient := by
  unfold quadraticCoefficient
  exact (continuous_a.div_const 2).sub (continuous_speedSq.div_const 16)

lemma continuous_integrand (k : ℝ) : Continuous (integrand k) := by
  have hH : Continuous (height k) := by unfold height a v; fun_prop
  have hq : Continuous (fun p => Real.sqrt (1 + k ^ 2 * speedSq p)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul continuous_speedSq))
  exact (hH.pow 2).div (continuous_const.mul hq) (fun p =>
    mul_ne_zero (by norm_num) (ne_of_gt (lt_of_lt_of_le zero_lt_one
      (sqrt_denominator_ge_one k p))))

theorem integral_a : (∫ p in (-1 : ℝ)..1, a p) = 1 / 15 := by
  have h2 : IntervalIntegrable (fun p : ℝ => p ^ 2) volume (-1) 1 :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun p : ℝ => p ^ 4) volume (-1) 1 :=
    (continuous_id.pow 4).intervalIntegrable _ _
  have heq : a = fun p : ℝ => (p ^ 2 + p ^ 4) / 16 := by
    funext p; unfold a v; ring
  rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_add h2 h4]
  norm_num [integral_pow]

theorem integral_speedSq : (∫ p in (-1 : ℝ)..1, speedSq p) = 17 / 30 := by
  have h2 : IntervalIntegrable (fun p : ℝ => p ^ 2) volume (-1) 1 :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun p : ℝ => p ^ 4) volume (-1) 1 :=
    (continuous_id.pow 4).intervalIntegrable _ _
  have heq : speedSq = fun p : ℝ => (1 + 10 * p ^ 2 + p ^ 4) / 16 := by
    funext p; unfold speedSq v w; ring
  rw [heq, intervalIntegral.integral_div,
    intervalIntegral.integral_add (intervalIntegrable_const.add (h2.const_mul 10)) h4,
    intervalIntegral.integral_add intervalIntegrable_const (h2.const_mul 10)]
  norm_num [intervalIntegral.integral_const_mul, integral_pow]

theorem integral_quadraticCoefficient :
    (∫ p in (-1 : ℝ)..1, quadraticCoefficient p) = -1 / 480 := by
  unfold quadraticCoefficient
  rw [intervalIntegral.integral_sub
    ((continuous_a.div_const 2).intervalIntegrable _ _)
    ((continuous_speedSq.div_const 16).intervalIntegrable _ _),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    integral_a, integral_speedSq]
  norm_num

theorem integral_quadraticApproximation (k : ℝ) :
    (∫ p in (-1 : ℝ)..1, (1 / 8 + k ^ 2 * quadraticCoefficient p)) =
      1 / 4 - k ^ 2 / 480 := by
  have hc : IntervalIntegrable (fun p : ℝ => k ^ 2 * quadraticCoefficient p)
      volume (-1) 1 := (continuous_quadraticCoefficient.const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegrable_const hc,
    intervalIntegral.integral_const_mul, integral_quadraticCoefficient]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem integral_remainder {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    |I k - (1 / 4 - k ^ 2 / 480)| ≤ 4 * k ^ 3 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 1)
    (f := fun p => integrand k p - (1 / 8 + k ^ 2 * quadraticCoefficient p))
    (C := 2 * k ^ 3) (by
      intro p hp
      have hp' : p ∈ Ioc (-1 : ℝ) 1 := by simpa using hp
      rw [Real.norm_eq_abs]
      exact integrand_remainder hk0 hk1 (abs_le.mpr ⟨hp'.1.le, hp'.2⟩))
  have hc : Continuous (fun p : ℝ => (1 : ℝ) / 8 + k ^ 2 * quadraticCoefficient p) :=
    continuous_const.add (continuous_quadraticCoefficient.const_mul _)
  rw [intervalIntegral.integral_sub
    ((continuous_integrand k).intervalIntegrable _ _)
    (hc.intervalIntegrable _ _),
    integral_quadraticApproximation, Real.norm_eq_abs] at hb
  change |I k - (1 / 4 - k ^ 2 / 480)| ≤ _ at hb
  norm_num at hb
  nlinarith only [hb]

theorem integral_lt_quarter {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1 / 1920) :
    I k < 1 / 4 := by
  have hr := (abs_le.mp (integral_remainder hk0.le (by linarith))).2
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk0
  have hs := mul_lt_mul_of_pos_right hk1 hk2
  nlinarith only [hr, hs]

theorem integral_expansion :
    (fun k : ℝ => I k - (1 / 4 - k ^ 2 / 480)) =O[𝓝[>] 0]
      (fun k : ℝ => k ^ 3) := by
  apply Asymptotics.IsBigO.of_bound 4
  have hsmall : ∀ᶠ k : ℝ in 𝓝[>] 0, k < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with k hk hk1
  have hk0 : 0 ≤ k := (show 0 < k from hk).le
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hk0 3)] using
    integral_remainder hk0 hk1.le

theorem eventually_integral_lt_quarter :
    ∀ᶠ k : ℝ in 𝓝[>] 0, I k < 1 / 4 := by
  have hsmall : ∀ᶠ k : ℝ in 𝓝[>] 0, k < 1 / 1920 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 1920)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with k hk hk1
  exact integral_lt_quarter hk hk1

theorem costSaving_result : CostSavingStatement :=
  ⟨integral_a, integral_speedSq, integral_expansion,
    fun _ hk0 hk1 => integral_remainder hk0 hk1,
    fun _ hk0 hk1 => integral_lt_quarter hk0 hk1,
    eventually_integral_lt_quarter⟩

end CylinderCovering.Nilpotent

end

end OAI
