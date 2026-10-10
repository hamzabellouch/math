import Mathlib

namespace OAI


noncomputable section

namespace Problem355

theorem scaled_area_implies_power_bound
    {n r a A : ℝ} (hn : 0 < n) (hr : 64 ≤ r) (hA : 0 < A)
    (hnA : n ≤ Real.rpow r A) (harea : r ^ 2 / 64 ≤ n ^ 2 * a) :
    Real.rpow n (-2 + 1 / A) ≤ a := by
  simp only [Real.rpow_eq_pow] at hnA ⊢
  have hr0 : 0 ≤ r := by linarith
  have hroot : n ^ (1 / A) ≤ r := by
    have h := Real.rpow_le_rpow (le_of_lt hn) hnA (le_of_lt (one_div_pos.mpr hA))
    rw [← Real.rpow_mul hr0, mul_one_div_cancel (ne_of_gt hA), Real.rpow_one] at h
    exact h
  have hrsq : r ≤ r ^ 2 / 64 := by nlinarith
  rw [show -2 + 1 / A = 1 / A - 2 by ring,
    Real.rpow_sub hn, Real.rpow_two]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  calc
    n ^ (1 / A) ≤ r := hroot
    _ ≤ r ^ 2 / 64 := hrsq
    _ ≤ n ^ 2 * a := harea
    _ = a * n ^ 2 := mul_comm _ _

theorem scaled_area_implies_heilbronn_power
    {n r a K : ℝ} (hn : 0 < n) (hr : 64 ≤ r) (hK : 0 < K)
    (hnK : n ≤ Real.rpow r (100000 * K))
    (harea : r ^ 2 / 64 ≤ n ^ 2 * a) :
    Real.rpow n (-2 + 1 / (100000 * K)) ≤ a := by
  apply scaled_area_implies_power_bound hn hr (mul_pos (by norm_num) hK) hnK harea

theorem sample_size_scaled_area
    {n r N τ a : ℝ} (hr : 0 ≤ r) (hN : 0 < N) (hτ : 0 < τ)
    (hsample : r * Real.sqrt (N ^ 3 / τ) / 2 ≤ n)
    (harea : τ / (16 * N ^ 3) ≤ a) :
    r ^ 2 / 64 ≤ n ^ 2 * a := by
  have hsize : 0 ≤ r * Real.sqrt (N ^ 3 / τ) / 2 := by positivity
  have hsq : (r * Real.sqrt (N ^ 3 / τ) / 2) ^ 2 ≤ n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsample) (add_nonneg hsize (hsize.trans hsample))]
  have hscale : 0 ≤ τ / (16 * N ^ 3) := by positivity
  calc
    r ^ 2 / 64 = (r * Real.sqrt (N ^ 3 / τ) / 2) ^ 2 *
        (τ / (16 * N ^ 3)) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ N ^ 3 / τ)]
      field_simp
      ring
    _ ≤ n ^ 2 * (τ / (16 * N ^ 3)) := mul_le_mul_of_nonneg_right hsq hscale
    _ ≤ n ^ 2 * a := mul_le_mul_of_nonneg_left harea (sq_nonneg n)

end Problem355

end

end OAI
