import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeSmallRange
import OAI.NumberTheory.CubicMoment.Estimates.TripleKernelScale

namespace OAI

/-! The original logarithmic and power height thresholds meet the group
estimates, with every fixed support constant retained. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma tailPrime_height_cube {X B η : ℝ} (hX : 1 ≤ X) (hη : η ≤ 1/1500)
    (hB : X^(1/4:ℝ) ≤ B) : X^(1/6+η) ≤ B^3 := by
  calc
    _ ≤ X^((1/4:ℝ)*3) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = (X^(1/4:ℝ))^3 := (Real.rpow_mul_natCast (zero_le_one.trans hX) _ _)
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hB 3

theorem eventually_tailPrime_large_height_cap {η : ℝ} (hη : η ≤ 1/1500) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, X^(12/25:ℝ) ≤ B →
      2*Real.pi*X^(1/6+η) ≤ B^(7/20:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (1/6+η:ℝ) < (12/25)*(7/20) by linarith)
      (2*Real.pi)] with X hX hgap
  intro B hB
  apply hgap.trans
  rw [Real.rpow_mul (zero_le_one.trans hX)]
  exact Real.rpow_le_rpow (by positivity) hB (by norm_num)

theorem eventually_tailPrime_power_height_log (m : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, 1 ≤ B → B ≤ 3*X →
      (1+Real.log B)^m ≤ X^(1/100:ℝ) := by
  let C : ℝ := (1+Real.log 3)^m
  filter_upwards [eventually_ge_atTop (1:ℝ),
    overlap_power_log_saving (by norm_num : (0:ℝ) < 1/200) m 0,
    eventually_const_mul_rpow_le (show (1/200:ℝ) < 1/100 by norm_num) C]
    with X hX hlog hgap
  intro B hB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hblog := Real.log_le_log (zero_lt_one.trans_le hB) hBX
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hXp.ne'] at hblog
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hb : 1+Real.log B ≤ (1+Real.log 3)*(1+Real.log X) := by
    nlinarith [Real.log_nonneg hX,mul_nonneg hlog3 (Real.log_nonneg hX)]
  have hh : (1+Real.log X)^m ≤ X^(1/200:ℝ) := by
    simp only [Nat.mul_zero,pow_zero,div_one] at hlog
    exact (div_le_one (Real.rpow_pos_of_pos hXp (1/200:ℝ))).mp hlog
  calc
    _ ≤ ((1+Real.log 3)*(1+Real.log X))^m :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hB]) hb m
    _ = C*(1+Real.log X)^m := by rw [mul_pow]
    _ ≤ C*X^(1/200:ℝ) := mul_le_mul_of_nonneg_left hh (by dsimp [C]; positivity)
    _ ≤ _ := hgap

theorem eventually_tailPrime_fixed_width_log {C : ℝ} (hC : 1 ≤ C) (m : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, 1 ≤ B → B ≤ 3*X →
      (1+Real.log (C*B))^m ≤ (1+Real.log X)^(m+1) := by
  let D : ℝ := 2+|Real.log (3*C)|
  have hD : 1 ≤ D := by dsimp [D]; linarith [abs_nonneg (Real.log (3*C))]
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (D^m)] with X hX hlarge
  intro B hB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hCB : 1 ≤ C*B := one_le_mul_of_one_le_of_one_le hC hB
  have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hb := Real.log_le_log (zero_lt_one.trans_le hCB)
    (mul_le_mul_of_nonneg_left hBX hCp.le)
  rw [show C*(3*X) = (3*C)*X by ring,
    Real.log_mul (by positivity : (3*C) ≠ 0) hXp.ne'] at hb
  have hmajor : 1+Real.log (C*B) ≤ D*(1+Real.log X) := by
    have hd := le_abs_self (Real.log (3*C))
    have hn := abs_nonneg (Real.log (3*C))
    have hm := mul_nonneg hn (Real.log_nonneg hX)
    dsimp [D]
    nlinarith
  calc
    _ ≤ (D*(1+Real.log X))^m :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hCB]) hmajor m
    _ = D^m*(1+Real.log X)^m := mul_pow _ _ _
    _ ≤ (1+Real.log X)*(1+Real.log X)^m :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end CubicFirstMoment

end

end OAI
