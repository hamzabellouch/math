import OAI.Combinatorics.EditApproximation.Geometry.AccuracyCutoff

namespace OAI

/-!
# Growth of the computed parameters

These are scalar estimates for the literal integer parameters of Section 10.
They do not assert an evaluator cost: the recursive-input and charged local
work bounds must be connected to these estimates separately.
-/

namespace EditApproximation

open Filter
open scoped Topology

theorem heightExponent_tendsto : Tendsto heightExponent atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ b))] with N hN
  exact heightExponent_above_double_power N b hN

theorem inputSmallLog_tendsto : Tendsto inputSmallLog atTop atTop := by
  apply tendsto_atTop_mono' atTop _ heightExponent_tendsto
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (inputSmallLog_bounds N hN).1

theorem smallLogExponent_tendsto : Tendsto smallLogExponent atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ b))]
    with N hN
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hN

theorem inputSmallLog_log_two (N : ℕ) :
    Nat.log 2 (inputSmallLog N) = smallLogExponent N := by
  exact Nat.log_pow (by decide : 1 < (2 : ℕ)) _

theorem coarseExponent_tendsto :
    Tendsto (fun N => coarseExponent (inputSmallLog N)) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [smallLogExponent_tendsto.eventually (eventually_ge_atTop (b ^ 4))]
    with N hN
  exact coarseExponent_maximal _ b ((inputSmallLog_log_two N).symm ▸ hN)

theorem heightExponent_real_tendsto :
    Tendsto (fun N => (heightExponent N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp heightExponent_tendsto

theorem inputSmallLog_real_tendsto :
    Tendsto (fun N => (inputSmallLog N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp inputSmallLog_tendsto

theorem coarseExponent_real_tendsto :
    Tendsto (fun N => (coarseExponent (inputSmallLog N) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp coarseExponent_tendsto

theorem inputSmallLog_real_log (N : ℕ) :
    Real.log (inputSmallLog N : ℝ) = (smallLogExponent N : ℝ) * Real.log 2 := by
  simp only [inputSmallLog, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem shifted_square_log_bound (p f : ℝ) (hpR : 1 ≤ p) (hfour : p ^ 4 ≤ f) :
    (p + 1) ^ 2 / (f * Real.log 2) ≤ 4 / (Real.log 2 * p ^ 2) := by
  have hsquare : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by nlinarith
  have hproduct : (p + 1) ^ 2 * p ^ 2 ≤ 4 * f := by
    have hm := mul_le_mul_of_nonneg_right hsquare (sq_nonneg p)
    nlinarith
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf : 0 < f := by nlinarith [sq_nonneg (p ^ 2)]
  apply (div_le_div_iff₀ (mul_pos hf hlogtwo)
    (mul_pos hlogtwo (sq_pos_of_pos (by linarith : 0 < p)))).2
  nlinarith [mul_le_mul_of_nonneg_right hproduct hlogtwo.le]

theorem coarse_shifted_square_log_bound (N : ℕ)
    (hp : 1 ≤ coarseExponent (inputSmallLog N)) :
    ((coarseExponent (inputSmallLog N) : ℝ) + 1) ^ 2 /
        Real.log (inputSmallLog N : ℝ) ≤
      4 / (Real.log 2 * (coarseExponent (inputSmallLog N) : ℝ) ^ 2) := by
  rw [inputSmallLog_real_log]
  apply shifted_square_log_bound
  · exact_mod_cast hp
  · have hnat := coarseExponent_fourth_power (inputSmallLog N)
    rw [inputSmallLog_log_two] at hnat
    exact_mod_cast hnat

/-- The central earlier-index dependency exponent in Section 10 is sublinear. -/
theorem coarse_shifted_square_div_log_tendsto :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) ^ 2 /
      Real.log (inputSmallLog N : ℝ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N =>
      4 / (Real.log 2 * (coarseExponent (inputSmallLog N) : ℝ) ^ 2)) atTop (𝓝 0) := by
    have h := (coarseExponent_real_tendsto.inv_tendsto_atTop.pow 2).const_mul (4 / Real.log 2)
    convert h using 1
    · ext N
      simp only [Pi.inv_apply, div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    · simp
  apply squeeze_zero' _ _ hupper
  · filter_upwards [smallLogExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hN
    apply div_nonneg (sq_nonneg _)
    rw [inputSmallLog_real_log]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  · filter_upwards [coarseExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hN
    exact coarse_shifted_square_log_bound N hN

theorem inputSmallLog_div_height_tendsto :
    Tendsto (fun N => (inputSmallLog N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => 2 * (heightExponent N : ℝ) / (2 : ℝ) ^ heightExponent N)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, mul_zero, mul_div_assoc] using
      ((tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)).comp
        heightExponent_tendsto).const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbound : (inputSmallLog N : ℝ) ≤ 2 * (heightExponent N : ℝ) := by
    exact_mod_cast (inputSmallLog_bounds N hN).2.le
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat] using
    div_le_div_of_nonneg_right hbound (by positivity : (0 : ℝ) ≤ 2 ^ heightExponent N)

theorem log_smallLog_div_smallLog_tendsto :
    Tendsto (fun N => Real.log (inputSmallLog N : ℝ) / inputSmallLog N) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputSmallLog_real_tendsto

end EditApproximation

end OAI
