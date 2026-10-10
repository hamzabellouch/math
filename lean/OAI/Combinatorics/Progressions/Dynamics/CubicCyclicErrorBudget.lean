import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

theorem cubic_cyclic_error_bound {d u e N : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hdu : d ≤ Real.exp u) (hN : Real.exp (e + 500) ≤ N) :
    (d ^ 9 + 1) * (81 * d ^ 335 * (2 * d ^ 18 + 1) *
      Real.exp (-(e + 362 * u + 500))) +
        12 * Real.exp (-(e + 500)) + 2 / N ≤ Real.exp (-e) := by
  have hp (n : ℕ) : d ^ n ≤ Real.exp ((n : ℝ) * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hd hdu n
  have h9 : d ^ 9 + 1 ≤ 2 * Real.exp (9 * u) := by
    have h := hp 9
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.one_le_exp (show 0 ≤ 9 * u by positivity)]
  have h18 : 2 * d ^ 18 + 1 ≤ 3 * Real.exp (18 * u) := by
    have h := hp 18
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.one_le_exp (show 0 ≤ 18 * u by positivity)]
  have h335 : d ^ 335 ≤ Real.exp (335 * u) := by
    simpa only [Nat.cast_ofNat] using hp 335
  have hcoef : (d ^ 9 + 1) * (81 * d ^ 335 * (2 * d ^ 18 + 1)) ≤
      486 * Real.exp (362 * u) := by
    calc
      _ ≤ (2 * Real.exp (9 * u)) *
          (81 * Real.exp (335 * u) * (3 * Real.exp (18 * u))) :=
        mul_le_mul h9
          (mul_le_mul (mul_le_mul_of_nonneg_left h335 (by norm_num)) h18
            (by positivity) (by positivity)) (by positivity) (by positivity)
      _ = _ := by
        rw [show (2 * Real.exp (9 * u)) *
          (81 * Real.exp (335 * u) * (3 * Real.exp (18 * u))) =
            486 * (Real.exp (9 * u) * Real.exp (335 * u) * Real.exp (18 * u)) by ring,
          ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  have hfirst : (d ^ 9 + 1) * (81 * d ^ 335 * (2 * d ^ 18 + 1) *
      Real.exp (-(e + 362 * u + 500))) ≤ 486 * Real.exp (-(e + 500)) := by
    calc
      _ = ((d ^ 9 + 1) * (81 * d ^ 335 * (2 * d ^ 18 + 1))) *
          Real.exp (-(e + 362 * u + 500)) := by ring
      _ ≤ (486 * Real.exp (362 * u)) * Real.exp (-(e + 362 * u + 500)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hrecip : 1 / N ≤ Real.exp (-(e + 500)) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hN
    simpa only [one_div, ← Real.exp_neg] using h
  have hthird : 2 / N ≤ 2 * Real.exp (-(e + 500)) := by
    calc
      _ = 2 * (1 / N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  calc
    _ ≤ 500 * Real.exp (-(e + 500)) := by linarith
    _ ≤ Real.exp 500 * Real.exp (-(e + 500)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (500 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
