import Mathlib

namespace OAI

noncomputable section

open Real

namespace Problem367

theorem min_linear_exp_le_log_interpolation {A B c J K u : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hJ : 0 < J)
    (hK : 1 ≤ K) (hu : 0 < u) (huK : u ≤ K) :
    min (A * u) (B * Real.exp (-c * J)) ≤
      (2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J := by
  let I : ℝ := 1 + Real.log (K / u)
  let q : ℝ := c * J / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hI : 1 ≤ I := by
    have hratio : 1 ≤ K / u := (one_le_div hu).2 huK
    have := Real.log_nonneg hratio
    dsimp [I]
    linarith
  change min (A * u) (B * Real.exp (-c * J)) ≤
    (2 * (A + B) / c) * u * I / J
  by_cases hsmall : u ≤ Real.exp (-q)
  · have hlogu : Real.log u ≤ -q := (Real.log_le_iff_le_exp hu).2 hsmall
    have hqI : q ≤ I := by
      dsimp [I]
      rw [Real.log_div (ne_of_gt hKpos) (ne_of_gt hu)]
      have := Real.log_nonneg hK
      linarith
    calc
      min (A * u) (B * Real.exp (-c * J)) ≤ A * u := min_le_left _ _
      _ ≤ (A + B) * u := by gcongr; linarith
      _ = (2 * (A + B) / c) * u * q / J := by
        dsimp [q]
        field_simp
      _ ≤ (2 * (A + B) / c) * u * I / J := by gcongr
  · have hlarge : Real.exp (-q) ≤ u := le_of_not_ge hsmall
    have hqexp : q ≤ Real.exp q := by
      have := Real.add_one_le_exp q
      linarith
    have hexp : Real.exp (-q) ≤ 1 / q := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hq hqexp
    have hexps : Real.exp (-c * J) = Real.exp (-q) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [q]
      ring
    calc
      min (A * u) (B * Real.exp (-c * J)) ≤ B * Real.exp (-c * J) := min_le_right _ _
      _ = B * Real.exp (-q) * Real.exp (-q) := by rw [hexps]; ring
      _ ≤ B * u * Real.exp (-q) := by gcongr
      _ ≤ (A + B) * u * (1 / q) := by gcongr; linarith
      _ ≤ ((A + B) * u * (1 / q)) * I := by
        have hnonneg : 0 ≤ (A + B) * u * (1 / q) := by positivity
        simpa using mul_le_mul_of_nonneg_left hI hnonneg
      _ = (2 * (A + B) / c) * u * I / J := by
        dsimp [q]
        field_simp

theorem small_log_loss_of_minimum {S A B c J K u R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hJ : 0 < J)
    (hK : 1 ≤ K) (hu : 0 < u) (huK : u ≤ K) (hR : 0 ≤ R)
    (hS : S ≤ A * R * u + min (A * u) (B * Real.exp (-c * J))) :
    S ≤ (A + 2 * (A + B) / c) * u *
      (R + (1 + Real.log (K / u)) / J) := by
  have hI : 0 ≤ 1 + Real.log (K / u) := by
    have := Real.log_nonneg ((one_le_div hu).2 huK)
    linarith
  have hC : 0 ≤ 2 * (A + B) / c := by positivity
  calc
    S ≤ A * R * u + (2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J :=
      hS.trans (add_le_add le_rfl (min_linear_exp_le_log_interpolation hA hB hc hJ hK hu huK))
    _ ≤ (A + 2 * (A + B) / c) * R * u +
        (2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J := by
      gcongr
      linarith
    _ ≤ (A + 2 * (A + B) / c) * R * u +
        (A + 2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J := by
      gcongr
      linarith
    _ = (A + 2 * (A + B) / c) * u *
        (R + (1 + Real.log (K / u)) / J) := by ring

theorem small_time_log_loss_of_minimum {S A B c K u t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c)
    (hK : 1 ≤ K) (hu : 0 < u) (huK : u ≤ K)
    (ht : 0 < t) (ht1 : t < 1)
    (hS : S ≤ A * t ^ ((1 : ℝ) / 4) * u +
      min (A * u) (B * Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    S ≤ (A + 2 * (A + B) / c) * u *
      (t ^ ((1 : ℝ) / 4) + (1 + Real.log (K / u)) / (Real.log (1 / t)) ^ 2) := by
  have hlog : 0 < Real.log (1 / t) := Real.log_pos ((one_lt_div ht).2 ht1)
  exact small_log_loss_of_minimum hA hB hc (sq_pos_of_pos hlog) hK hu huK
    (Real.rpow_nonneg ht.le _) hS

end Problem367

end

end OAI
