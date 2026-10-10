import OAI.Combinatorics.Ryser.LineCover.TailNumerics
import Mathlib.Tactic.FieldSimp

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

theorem count_variance_ratio {q D ε k : ℝ} (hq : 0 < q) (hD : D ≠ 0) :
    (q ^ (k + 1 / 2 + ε)) ^ 2 / (4 * D ^ 5 * q ^ (2 * k + 1)) =
      q ^ (2 * ε) / (4 * D ^ 5) := by
  have hp : (q ^ (k + 1 / 2 + ε)) ^ 2 =
      q ^ (2 * ε) * q ^ (2 * k + 1) := by
    calc
      _ = q ^ ((k + 1 / 2 + ε) * (2 : ℝ)) := by
        rw [Real.rpow_mul hq.le, Real.rpow_two]
      _ = q ^ (2 * ε + (2 * k + 1)) := by congr 1; ring
      _ = _ := Real.rpow_add hq _ _
  rw [hp]
  have hpow : q ^ (2 * k + 1) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  field_simp [hD, hpow]

theorem count_coordinate_ratio {q D ε k : ℝ} (hq : 0 < q) (hD : D ≠ 0) :
    q ^ (k + 1 / 2 + ε) / (2 * D ^ 2 * q ^ k) =
      q ^ (1 / 2 + ε) / (2 * D ^ 2) := by
  rw [show k + 1 / 2 + ε = (1 / 2 + ε) + k by ring, Real.rpow_add hq]
  have hpow : q ^ k ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  field_simp [hD, hpow]

theorem count_variance_ratio_le_coordinate {q D ε : ℝ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    q ^ (2 * ε) / (4 * D ^ 5) ≤ q ^ (1 / 2 + ε) / (2 * D ^ 2) := by
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hp : q ^ (2 * ε) ≤ q ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hDpow : D ^ 2 ≤ D ^ 5 := by
    calc
      D ^ 2 = D ^ 2 * 1 := by ring
      _ ≤ D ^ 2 * D ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hD) (sq_nonneg D)
      _ = D ^ 5 := by ring
  have hden : 2 * D ^ 2 ≤ 4 * D ^ 5 := by nlinarith [sq_nonneg D]
  exact div_le_div₀ (Real.rpow_nonneg hq0 _) hp (by positivity) hden

theorem count_tail_le_stretched_exp {q D ε k : ℝ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (k + 1 / 2 + ε)) ^ 2 / (4 * D ^ 5 * q ^ (2 * k + 1)))
        (q ^ (k + 1 / 2 + ε) / (2 * D ^ 2 * q ^ k))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * D ^ 5)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hD0 : D ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hD)
  rw [count_variance_ratio hq0 hD0, count_coordinate_ratio hq0 hD0,
    min_eq_left (count_variance_ratio_le_coordinate hq hD hε)]
  have hexponent : -(1 / 4 : ℝ) * (q ^ (2 * ε) / (4 * D ^ 5)) =
      -q ^ (2 * ε) / (16 * D ^ 5) := by
    field_simp [hD0]
    ring
  rw [hexponent]

theorem total_count_tail_le_stretched_exp {q ε : ℝ} {D : ℕ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (3 / 2 + ε)) ^ 2 / (4 * (D : ℝ) ^ 5 * q ^ 3))
        (q ^ (3 / 2 + ε) / (2 * (D : ℝ) ^ 2 * q))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  simpa only [one_add_one_eq_two, mul_one, Real.rpow_one,
    show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
    show (2 : ℝ) + 1 = (3 : ℕ) by norm_num, Real.rpow_natCast] using
    (count_tail_le_stretched_exp (q := q) (D := (D : ℝ)) (ε := ε) (k := 1) hq hDr hε)

theorem line_count_tail_le_stretched_exp {q ε : ℝ} {D : ℕ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (1 / 2 + ε)) ^ 2 / (4 * (D : ℝ) ^ 5 * q))
        (q ^ (1 / 2 + ε) / (2 * (D : ℝ) ^ 2))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  simpa only [mul_zero, zero_add, Real.rpow_zero, Real.rpow_one, mul_one] using
    (count_tail_le_stretched_exp (q := q) (D := (D : ℝ)) (ε := ε) (k := 0) hq hDr hε)

end RyserCoveringCounterexample.LineCover

end

end OAI
