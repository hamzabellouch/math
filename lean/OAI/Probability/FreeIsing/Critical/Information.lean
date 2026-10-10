import Mathlib

namespace OAI

namespace Problem367

theorem critical_estimator_cutoff {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ n : ℕ, Real.sqrt t / 5 ≤
      t * ((n : ℝ) + 1) / (1 + t * ((n : ℝ) + 1) ^ 2) := by
  let n : ℕ := ⌊1 / Real.sqrt t⌋₊
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hinv : 1 ≤ 1 / Real.sqrt t := (le_div_iff₀ hs).mpr (by simpa using hs1)
  have hnlow : 1 / Real.sqrt t ≤ (n : ℝ) + 1 :=
    (Nat.lt_floor_add_one (1 / Real.sqrt t)).le
  have hnhigh : (n : ℝ) + 1 ≤ 2 / Real.sqrt t := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ 1 / Real.sqrt t)
    change (n : ℝ) ≤ 1 / Real.sqrt t at hfloor
    calc
      (n : ℝ) + 1 ≤ 1 / Real.sqrt t + 1 := by linarith
      _ ≤ 1 / Real.sqrt t + 1 / Real.sqrt t := by linarith
      _ = 2 / Real.sqrt t := by ring
  have hmul_low : 1 ≤ Real.sqrt t * ((n : ℝ) + 1) := by
    have h := (div_le_iff₀ hs).mp hnlow
    nlinarith
  have hmul_high : Real.sqrt t * ((n : ℝ) + 1) ≤ 2 := by
    have h := (le_div_iff₀ hs).mp hnhigh
    nlinarith
  have hnum : Real.sqrt t ≤ t * ((n : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_left hmul_low hs.le
    nlinarith [hsq]
  have hprod_sq : (Real.sqrt t * ((n : ℝ) + 1)) ^ 2 =
      t * ((n : ℝ) + 1) ^ 2 := by rw [mul_pow, hsq]
  have hden : 1 + t * ((n : ℝ) + 1) ^ 2 ≤ 5 := by
    have h := mul_self_le_mul_self (by positivity :
      0 ≤ Real.sqrt t * ((n : ℝ) + 1)) hmul_high
    nlinarith [hprod_sq]
  have hdenpos : 0 < 1 + t * ((n : ℝ) + 1) ^ 2 := by positivity
  refine ⟨n, (le_div_iff₀ hdenpos).mpr ?_⟩
  calc
    Real.sqrt t / 5 * (1 + t * ((n : ℝ) + 1) ^ 2) ≤
        Real.sqrt t / 5 * 5 :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ t * ((n : ℝ) + 1) := by nlinarith

theorem critical_information_lower_of_estimators {t M : ℝ} (ht : 0 < t)
    (h : ∀ n : ℕ,
      t * ((n : ℝ) + 1) / (1 + t * ((n : ℝ) + 1) ^ 2) ≤ M) :
    min (Real.sqrt t) 1 / 5 ≤ M := by
  by_cases ht1 : t ≤ 1
  · obtain ⟨n, hn⟩ := critical_estimator_cutoff ht ht1
    rw [min_eq_left (Real.sqrt_le_one.mpr ht1)]
    exact hn.trans (h n)
  · have ht1' : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    rw [min_eq_right (Real.one_le_sqrt.mpr ht1')]
    have h0 : t / (1 + t) ≤ M := by simpa using h 0
    have hhalf : (1 / 2 : ℝ) ≤ t / (1 + t) := by
      apply (le_div_iff₀ (by positivity : 0 < 1 + t)).mpr
      linarith
    linarith

theorem sqrt_bound_of_quadratic_information_loss {M c K t : ℝ}
    (hc : 0 < c) (hK : 0 ≤ K)
    (h : M ≤ M - c * M ^ 2 + K * t) :
    M ≤ Real.sqrt (K / c) * Real.sqrt t := by
  have hquad : M ^ 2 ≤ K * t / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  calc
    M ≤ Real.sqrt (K * t / c) := Real.le_sqrt_of_sq_le hquad
    _ = Real.sqrt (K / c) * Real.sqrt t := by
      rw [show K * t / c = (K / c) * t by ring,
        Real.sqrt_mul (div_nonneg hK hc.le)]

theorem critical_information_upper_of_fusion {b theta M t : ℝ}
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hcritical : b * theta ^ 2 = 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h : M ≤ b * theta ^ 2 * M -
      2 * (1 - theta ^ 2) * theta ^ 4 * M ^ 2 + (t + t ^ 2)) :
    M ≤ Real.sqrt (1 / ((1 - theta ^ 2) * theta ^ 4)) * Real.sqrt t := by
  have hθsq : theta ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one theta).mpr (abs_lt.mpr ⟨by linarith, hθ1⟩)
  have hc : 0 < (1 - theta ^ 2) * theta ^ 4 :=
    mul_pos (sub_pos.mpr hθsq) (pow_pos hθ0 4)
  have htsq : t ^ 2 ≤ t := by nlinarith
  rw [hcritical, one_mul] at h
  have hrec : M ≤ M - (2 * ((1 - theta ^ 2) * theta ^ 4)) * M ^ 2 + 2 * t := by
    nlinarith
  have hbound := sqrt_bound_of_quadratic_information_loss
    (mul_pos (by norm_num : (0 : ℝ) < 2) hc) (by norm_num : (0 : ℝ) ≤ 2) hrec
  have hratio : (2 : ℝ) / (2 * ((1 - theta ^ 2) * theta ^ 4)) =
      1 / ((1 - theta ^ 2) * theta ^ 4) := by field_simp
  simpa only [hratio] using hbound

end Problem367

end OAI
