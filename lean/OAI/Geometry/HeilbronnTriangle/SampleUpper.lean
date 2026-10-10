import Mathlib

namespace OAI


namespace Problem355.Parameters

lemma sqrt_cube_div_le_square {N tau : ℝ} (hN : 1 ≤ N) (htau : 1 ≤ tau) :
    Real.sqrt (N ^ 3 / tau) ≤ N ^ 2 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨sq_nonneg N, ?_⟩
  calc
    N ^ 3 / tau ≤ N ^ 3 := div_le_self (by positivity) htau
    _ ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
    _ = (N ^ 2) ^ 2 := by ring

lemma sample_size_le_nat_power {n r N tau : ℝ} {k : ℕ}
    (hr : 1 ≤ r) (hN : 1 ≤ N) (htau : 1 ≤ tau) (hk : 1 ≤ k)
    (hbox : N ≤ r ^ (31620 * k))
    (hsample : n ≤ r * Real.sqrt (N ^ 3 / tau)) :
    n ≤ r ^ (100000 * k) := by
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  calc
    n ≤ r * Real.sqrt (N ^ 3 / tau) := hsample
    _ ≤ r * N ^ 2 := mul_le_mul_of_nonneg_left (sqrt_cube_div_le_square hN htau) hr0
    _ ≤ r * (r ^ (31620 * k)) ^ 2 := by gcongr
    _ = r ^ (63240 * k + 1) := by
      rw [← pow_mul]
      have he : 31620 * k * 2 = 63240 * k := by omega
      rw [he, pow_succ]
      ring
    _ ≤ r ^ (100000 * k) := pow_le_pow_right₀ hr (by omega)

lemma sample_size_le_real_power {n r N tau : ℝ} {k : ℕ}
    (hr : 1 ≤ r) (hN : 1 ≤ N) (htau : 1 ≤ tau) (hk : 1 ≤ k)
    (hbox : N ≤ r ^ (31620 * k))
    (hsample : n ≤ r * Real.sqrt (N ^ 3 / tau)) :
    n ≤ Real.rpow r (100000 * (k : ℝ)) := by
  have he : (100000 : ℝ) * (k : ℝ) = ((100000 * k : ℕ) : ℝ) := by norm_cast
  simp only [Real.rpow_eq_pow]
  rw [he, Real.rpow_natCast]
  exact sample_size_le_nat_power hr hN htau hk hbox hsample

end Problem355.Parameters

end OAI
