import OAI.NumberTheory.Ostmann.QuadraticCenter.LargeKernelNorm

namespace OAI

/-! # Passing from the real analytic scale to the manuscript's integer K -/

namespace Ostmann

open Filter

noncomputable def integerKernelScale (K : ℝ) : ℝ := K ^ (10000000 / 9999999 : ℝ)

theorem integerKernelScale_power (K : ℝ) (hK : 0 ≤ K) :
    integerKernelScale K ^ (9999999 / 10000000 : ℝ) = K := by
  rw [integerKernelScale, ← Real.rpow_mul hK]
  rw [show (10000000 / 9999999 : ℝ) * (9999999 / 10000000) = 1 by norm_num,
    Real.rpow_one]

theorem integerKernelScale_lower (T K : ℝ) (hT : 1 ≤ T)
    (hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K) :
    T / 1000000 ≤ integerKernelScale K := by
  have hT0 : 0 ≤ T := by linarith
  have hd : (1000 : ℝ) ^ (10000000 / 9999999 : ℝ) ≤ 1000000 := by
    calc
      _ ≤ (1000 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by rw [Real.rpow_two]; norm_num
  calc
    _ ≤ T / (1000 : ℝ) ^ (10000000 / 9999999 : ℝ) :=
      div_le_div_of_nonneg_left hT0 (Real.rpow_pos_of_pos (by norm_num) _) hd
    _ = (T ^ (9999999 / 10000000 : ℝ) / 1000) ^ (10000000 / 9999999 : ℝ) := by
      rw [Real.div_rpow (Real.rpow_nonneg hT0 _) (by norm_num), ← Real.rpow_mul hT0]
      rw [show (9999999 / 10000000 : ℝ) * (10000000 / 9999999) = 1 by norm_num,
        Real.rpow_one]
    _ ≤ integerKernelScale K := Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hT0 _) (by norm_num)) hK (by norm_num)

theorem integerKernelScale_moment (T K u : ℝ) (hT : 1 ≤ T)
    (hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K)
    (hu : u ≤ 2 * T ^ (1 / 1000000 : ℝ)) :
    u ≤ 4 * integerKernelScale K ^ (1 / 1000000 : ℝ) := by
  have hT0 : 0 ≤ T := by linarith
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hS : 0 < integerKernelScale K := Real.rpow_pos_of_pos hK0 _
  have hlo := integerKernelScale_lower T K hT hK
  have hTS : T ≤ 1000000 * integerKernelScale K := by linarith
  have hc : (1000000 : ℝ) ^ (1 / 1000000 : ℝ) ≤ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ (20 : ℕ)) ^ (1 / 1000000 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = (2 : ℝ) ^ ((20 : ℝ) * (1 / 1000000 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        simp only [Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  apply hu.trans
  calc
    _ ≤ 2 * (1000000 * integerKernelScale K) ^ (1 / 1000000 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hT0 hTS (by norm_num)) (by norm_num)
    _ = 2 * ((1000000 : ℝ) ^ (1 / 1000000 : ℝ) *
        integerKernelScale K ^ (1 / 1000000 : ℝ)) := by rw [Real.mul_rpow (by norm_num) hS.le]
    _ ≤ 4 * integerKernelScale K ^ (1 / 1000000 : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 2 by norm_num))
        (Real.rpow_nonneg hS.le (1 / 1000000 : ℝ))
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num, mul_assoc] using hh

theorem eventually_at_integerKernelScale (Q : ℝ → Prop) (hQ : ∀ᶠ x : ℝ in atTop, Q x) :
    ∀ᶠ T : ℝ in atTop, ∀ K : ℝ,
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K → Q (integerKernelScale K) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp hQ
  filter_upwards [eventually_ge_atTop (1000000 * max 1 B), eventually_ge_atTop (1 : ℝ)] with T ht hT K hK
  apply hB
  have hh := integerKernelScale_lower T K hT hK
  have hBB := le_max_right (1 : ℝ) B
  linarith

end Ostmann

end OAI
