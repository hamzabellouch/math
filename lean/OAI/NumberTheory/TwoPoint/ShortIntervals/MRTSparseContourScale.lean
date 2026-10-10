import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKScale

namespace OAI

/-! Numerical compatibility of the narrower sparse-prime contour with the
weak VK strip, uniformly over its full finite height. -/

namespace TwoPointCorrelations

open Filter
open scoped Topology

lemma mrt_sparse_contour_height {L t : ℝ} (hL : Real.log 11 ≤ L) (hL0 : 0 ≤ L)
    (ht : |t| ≤ 4 * Real.exp (2 * L)) : mrtVKLog (2 * t) ≤ 3 * L := by
  have hE : 1 ≤ Real.exp (2 * L) := Real.one_le_exp_iff.mpr (by linarith)
  have hh : |2 * t| + 3 ≤ 11 * Real.exp (2 * L) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have he := Real.log_le_log (by positivity : 0 < |2 * t| + 3) hh
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at he
  exact he.trans (by linarith)

lemma mrt_sparse_contour_budget {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, |t| ≤ 4 * Real.exp (2 * L) →
      L ^ (-(3 / 4 : ℝ)) ≤ c * mrtVKRadius (2 * t) / mrtVKWeight 1 (2 * t) ∧
      (mrtVKWeight 1 (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤ L ^ 2 := by
  have he := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).bound
    (show 0 < c / 12 by positivity)
  have hd := mrt_VK_log_square_decay (a := 2) (by norm_num)
  filter_upwards [he, hd, eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop (Real.log 11)] with L he hd hL1 hL11
  intro t ht
  have hL : 0 < L := (Real.exp_pos 1).trans_le hL1
  have hLge : 1 ≤ L := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hL).mpr hL1
  have hH : 1 ≤ mrtVKLog (2 * t) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < |2 * t| + 3)).mpr
    linarith [Real.exp_one_lt_d9, abs_nonneg (2 * t)]
  have hHp := mrt_VKLog_pos (2 * t)
  have hHup := mrt_sparse_contour_height hL11 hL.le ht
  have hW : mrtVKWeight 1 (2 * t) ≤ 4 * Real.log L := by
    have hh := Real.log_le_log hHp hHup
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hL.ne'] at hh
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    simp only [mrtVKWeight, Nat.cast_one, Real.log_one, add_zero]
    linarith
  have hW0 : 0 < mrtVKWeight 1 (2 * t) :=
    zero_lt_one.trans_le (mrt_VKWeight_ge_one (q := 1) hH)
  have hpow : (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) ≤ 3 * L ^ (2 / 3 : ℝ) := by
    apply (Real.rpow_le_rpow hHp.le hHup (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hL.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (show (2 / 3 : ℝ) ≤ 1 by norm_num)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hLge), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL _)] at he
  have hp : (L ^ (-(3 / 4 : ℝ)) * (4 * Real.log L)) * (3 * L ^ (2 / 3 : ℝ)) ≤ c := by
    have hid : L ^ (-(3 / 4 : ℝ)) * L ^ (2 / 3 : ℝ) = (L ^ (1 / 12 : ℝ))⁻¹ := by
      rw [← Real.rpow_add hL, ← Real.rpow_neg hL.le]
      congr 1
      norm_num
    calc
      _ = 12 * Real.log L * (L ^ (1 / 12 : ℝ))⁻¹ := by rw [← hid]; ring
      _ ≤ 12 * ((c / 12) * L ^ (1 / 12 : ℝ)) * (L ^ (1 / 12 : ℝ))⁻¹ := by gcongr
      _ = c := by field_simp
  refine ⟨?_, ?_⟩
  · apply (le_div_iff₀ hW0).mpr
    rw [mrtVKRadius, Real.rpow_neg hHp.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hHp _)).mpr
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hW (Real.rpow_nonneg hL.le _))
      hpow (Real.rpow_nonneg hHp.le _) (by positivity)).trans hp
  · have hs : (mrtVKWeight 1 (2 * t)) ^ 2 ≤ 16 * (Real.log L) ^ 2 := by nlinarith
    have hh := mul_le_mul hs hpow (Real.rpow_nonneg hHp.le _) (by positivity)
    have hd' : 512 * (Real.log L) ^ 2 * L ^ (2 / 3 : ℝ) ≤ (1 / 2 : ℝ) * L ^ (2 : ℕ) := by
      simpa only [Real.rpow_two] using hd
    apply hh.trans
    calc
      16 * (Real.log L) ^ 2 * (3 * L ^ (2 / 3 : ℝ)) =
          (3 / 32 : ℝ) * (512 * (Real.log L) ^ 2 * L ^ (2 / 3 : ℝ)) := by ring
      _ ≤ (3 / 32 : ℝ) * ((1 / 2 : ℝ) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hd' (by norm_num)
      _ ≤ L ^ 2 := by nlinarith [sq_nonneg L]

end TwoPointCorrelations

end OAI
