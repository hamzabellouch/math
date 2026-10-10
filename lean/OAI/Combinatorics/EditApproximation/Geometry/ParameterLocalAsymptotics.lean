import OAI.Combinatorics.EditApproximation.Geometry.ParameterAsymptotics

namespace OAI

/-! Scalar bounds for the local enumeration exponent. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem inputHeight_real_tendsto :
    Tendsto (fun N => (inputHeight N : ℝ)) atTop atTop := by
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Function.comp_def] using
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp heightExponent_tendsto

/-- Every fixed polynomial in the computed small logarithm is negligible
relative to the computed height. -/
theorem smallLog_polynomial_div_height_tendsto (k : ℕ) :
    Tendsto (fun N => (inputSmallLog N : ℝ) ^ k / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => (2 : ℝ) ^ k *
      ((heightExponent N : ℝ) ^ k / (2 : ℝ) ^ heightExponent N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).comp
        heightExponent_tendsto).const_mul ((2 : ℝ) ^ k)
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbound : (inputSmallLog N : ℝ) ≤ 2 * (heightExponent N : ℝ) := by
    exact_mod_cast (inputSmallLog_bounds N hN).2.le
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (inputSmallLog N)) hbound k
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, mul_pow, mul_div_assoc] using
    div_le_div_of_nonneg_right hpower (by positivity : (0 : ℝ) ≤ 2 ^ heightExponent N)

theorem computed_branching_square_le_height (N : ℕ) :
    ((integerParameters N).M : ℝ) ^ 2 ≤ inputHeight N := by
  have hexponent : heightExponent N / 20 * 2 ≤ heightExponent N := by omega
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [integerParameters, inputHeight, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul] using h

/-- This directly controls the scalar exponent `M q ell` occurring in the
local wide-action enumeration. -/
theorem branching_smallLog_polynomial_div_height_tendsto (k : ℕ) :
    Tendsto (fun N => ((integerParameters N).M : ℝ) *
      (inputSmallLog N : ℝ) ^ k / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => Real.sqrt
      ((inputSmallLog N : ℝ) ^ (2 * k) / inputHeight N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (smallLog_polynomial_div_height_tendsto (2 * k)).sqrt
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)) _ hupper
  apply Eventually.of_forall
  intro N
  apply Real.le_sqrt_of_sq_le
  have hH : (0 : ℝ) < inputHeight N := by
    exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hM := computed_branching_square_le_height N
  have hproduct := mul_le_mul_of_nonneg_right hM
    (pow_nonneg (Nat.cast_nonneg (inputSmallLog N)) (2 * k))
  rw [div_pow, mul_pow, ← pow_mul, Nat.mul_comm k 2]
  apply (div_le_iff₀ (sq_pos_of_pos hH)).2
  calc
    ((integerParameters N).M : ℝ) ^ 2 * (inputSmallLog N : ℝ) ^ (2 * k) ≤
        (inputHeight N : ℝ) * (inputSmallLog N : ℝ) ^ (2 * k) := hproduct
    _ = ((inputSmallLog N : ℝ) ^ (2 * k) / inputHeight N) *
        (inputHeight N : ℝ) ^ 2 := by field_simp [hH.ne']

theorem coarseExponent_le_smallLog (N : ℕ) :
    coarseExponent (inputSmallLog N) ≤ inputSmallLog N := by
  have h := coarseExponent_fourth_power (inputSmallLog N)
  have hp : coarseExponent (inputSmallLog N) ≤ coarseExponent (inputSmallLog N) ^ 4 := by
    exact Nat.le_pow (by decide : 0 < 4)
  exact hp.trans (h.trans (Nat.log_le_self 2 _))

theorem local_enumeration_exponent_div_height_tendsto :
    Tendsto (fun N => ((integerParameters N).M : ℝ) *
      ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N / inputHeight N)
      atTop (𝓝 0) := by
  have hupper := (branching_smallLog_polynomial_div_height_tendsto 2).const_mul 2
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hupper
  apply Eventually.of_forall
  intro N
  have hell : (1 : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
  have hp : (coarseExponent (inputSmallLog N) : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast coarseExponent_le_smallLog N
  have hq : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by linarith
  have hprod := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (inputSmallLog N)))
    (Nat.cast_nonneg (integerParameters N).M)
  have hdiv := div_le_div_of_nonneg_right hprod (Nat.cast_nonneg (inputHeight N))
  convert hdiv using 1 <;> ring

theorem inputHeight_real_log (N : ℕ) :
    Real.log (inputHeight N : ℝ) = (heightExponent N : ℝ) * Real.log 2 := by
  simp only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem encoding_exponent_div_height_tendsto :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) *
      Real.log (inputHeight N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  have hupper := (smallLog_polynomial_div_height_tendsto 2).const_mul (2 * Real.log 2)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := heightExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hp : (coarseExponent (inputSmallLog N) : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast coarseExponent_le_smallLog N
  have hell : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
  have hq : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by linarith
  have he : (heightExponent N : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast (inputSmallLog_bounds N hN).1
  have hprod := mul_le_mul hq he (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * inputSmallLog N)
  have hlog := mul_le_mul_of_nonneg_right hprod (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  rw [inputHeight_real_log]
  have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (inputHeight N))
  convert hdiv using 1 <;> ring

theorem height_log_sandwich (N : ℕ) (hN : 0 < N) :
    Real.log (N + 2 : ℝ) / Real.log 2 ≤ inputHeight N ∧
      (inputHeight N : ℝ) ≤ (4 / Real.log 2) * Real.log (N + 2 : ℝ) := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcover : (N + 2 : ℝ) ≤ (2 : ℝ) ^ inputHeight N := by
    exact_mod_cast inputHeight_covers_length N
  have hlower := Real.log_le_log (by positivity : (0 : ℝ) < N + 2) hcover
  rw [Real.log_pow] at hlower
  have hL : 1 < Nat.clog 2 (N + 2) := by
    exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by norm_num; omega)
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ))
    (by omega : 1 < N + 2)
  have hpredR : (2 : ℝ) ^ (Nat.clog 2 (N + 2)).pred < N + 2 := by exact_mod_cast hpred
  have hpredlog := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ (Nat.clog 2 (N + 2)).pred) hpredR
  rw [Real.log_pow] at hpredlog
  have hpredcast : ((Nat.clog 2 (N + 2)).pred : ℝ) = (Nat.clog 2 (N + 2) : ℝ) - 1 := by
    have hnat : (Nat.clog 2 (N + 2)).pred + 1 = Nat.clog 2 (N + 2) :=
      Nat.succ_pred_eq_of_pos (by omega)
    have hcast : ((Nat.clog 2 (N + 2)).pred : ℝ) + 1 = (Nat.clog 2 (N + 2) : ℝ) := by
      exact_mod_cast hnat
    linarith
  rw [hpredcast] at hpredlog
  have hH : (inputHeight N : ℝ) < 2 * (Nat.clog 2 (N + 2) : ℝ) := by
    have h := (rejectionWord_range (Nat.clog 2 (N + 2)) (by omega)).2
    simpa only [inputHeight, heightExponent, rejectionBitCount, Nat.cast_pow,
      Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_lt.mpr h :
      ((2 ^ rejectionBitCount (Nat.clog 2 (N + 2)) : ℕ) : ℝ) <
        ((2 * Nat.clog 2 (N + 2) : ℕ) : ℝ))
  have hlogN : Real.log 2 ≤ Real.log (N + 2 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N + 2))
  constructor
  · exact (div_le_iff₀ hlogtwo).2 hlower
  · have hproduct : (inputHeight N : ℝ) * Real.log 2 ≤ 4 * Real.log (N + 2 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hH.le hlogtwo.le
      nlinarith
    calc
      (inputHeight N : ℝ) ≤ (4 * Real.log (N + 2 : ℝ)) / Real.log 2 :=
        (le_div_iff₀ hlogtwo).2 hproduct
      _ = (4 / Real.log 2) * Real.log (N + 2 : ℝ) := by ring

end EditApproximation

end OAI
