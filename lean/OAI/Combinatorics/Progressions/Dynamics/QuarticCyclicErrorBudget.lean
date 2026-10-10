import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

theorem quartic_cyclic_error_bound {d u e N : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hdu : d ≤ Real.exp u) (hN : Real.exp (e + 31000) ≤ N) :
    (d ^ 64 + 1) * (15360 * d ^ 5058 * Real.exp (-(e + 5122 * u + 31000))) +
      12 * Real.exp (-(e + 31000)) + 2 / N ≤ Real.exp (-e) := by
  have hp (n : ℕ) : d ^ n ≤ Real.exp ((n : ℝ) * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hd hdu n
  have h64 : d ^ 64 + 1 ≤ 2 * Real.exp (64 * u) := by
    have h := hp 64
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.one_le_exp (show 0 ≤ 64 * u by positivity)]
  have h5058 : d ^ 5058 ≤ Real.exp (5058 * u) := by
    simpa only [Nat.cast_ofNat] using hp 5058
  have hcoef : (d ^ 64 + 1) * (15360 * d ^ 5058) ≤
      30720 * Real.exp (5122 * u) := by
    calc
      _ ≤ (2 * Real.exp (64 * u)) * (15360 * Real.exp (5058 * u)) :=
        mul_le_mul h64 (mul_le_mul_of_nonneg_left h5058 (by norm_num))
          (by positivity) (by positivity)
      _ = _ := by
        rw [show (2 * Real.exp (64 * u)) * (15360 * Real.exp (5058 * u)) =
          30720 * (Real.exp (64 * u) * Real.exp (5058 * u)) by ring, ← Real.exp_add]
        congr 2
        ring
  have hfirst : (d ^ 64 + 1) * (15360 * d ^ 5058 *
      Real.exp (-(e + 5122 * u + 31000))) ≤ 30720 * Real.exp (-(e + 31000)) := by
    calc
      _ = ((d ^ 64 + 1) * (15360 * d ^ 5058)) *
          Real.exp (-(e + 5122 * u + 31000)) := by ring
      _ ≤ (30720 * Real.exp (5122 * u)) * Real.exp (-(e + 5122 * u + 31000)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hrecip : 1 / N ≤ Real.exp (-(e + 31000)) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hN
    simpa only [one_div, ← Real.exp_neg] using h
  have hthird : 2 / N ≤ 2 * Real.exp (-(e + 31000)) := by
    calc
      _ = 2 * (1 / N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  calc
    _ ≤ 31000 * Real.exp (-(e + 31000)) := by linarith [Real.exp_pos (-(e + 31000))]
    _ ≤ Real.exp 31000 * Real.exp (-(e + 31000)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (31000 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
