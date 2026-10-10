import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Scalar cutoffs for the Hilbert displacement construction

The inner cutoff `beta` is one through radius `ρ / 4` and vanishes from
`ρ / 2`. The outer cutoff `chi` is one through radius `ρ / 2` and vanishes
from `ρ`. Both formulas take values in `[0, 1]` even outside this domain.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

/-- The cutoff supported inside the half-radius ball. -/
def beta (ρ r : ℝ) : ℝ := min 1 (max 0 (2 - 4 * r / ρ))

/-- The cutoff supported inside the full-radius ball. -/
def chi (ρ r : ℝ) : ℝ := min 1 (max 0 (2 - 2 * r / ρ))

theorem beta_nonneg (ρ r : ℝ) : 0 ≤ beta ρ r :=
  le_min zero_le_one (le_max_left _ _)

theorem beta_le_one (ρ r : ℝ) : beta ρ r ≤ 1 :=
  min_le_left _ _

theorem chi_nonneg (ρ r : ℝ) : 0 ≤ chi ρ r :=
  le_min zero_le_one (le_max_left _ _)

theorem chi_le_one (ρ r : ℝ) : chi ρ r ≤ 1 :=
  min_le_left _ _

theorem beta_eq_one {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : r ≤ ρ / 4) :
    beta ρ r = 1 := by
  have hdiv : 4 * r / ρ ≤ 1 := (div_le_iff₀ hρ).2 (by nlinarith)
  have harg : 1 ≤ 2 - 4 * r / ρ := by linarith
  exact min_eq_left (harg.trans (le_max_right _ _))

theorem beta_eq_zero {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : ρ / 2 ≤ r) :
    beta ρ r = 0 := by
  have hdiv : 2 ≤ 4 * r / ρ := (le_div_iff₀ hρ).2 (by nlinarith)
  have harg : 2 - 4 * r / ρ ≤ 0 := by linarith
  simp only [beta, max_eq_left harg, min_eq_right zero_le_one]

theorem chi_eq_one {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : r ≤ ρ / 2) :
    chi ρ r = 1 := by
  have hdiv : 2 * r / ρ ≤ 1 := (div_le_iff₀ hρ).2 (by nlinarith)
  have harg : 1 ≤ 2 - 2 * r / ρ := by linarith
  exact min_eq_left (harg.trans (le_max_right _ _))

theorem chi_eq_zero {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : ρ ≤ r) :
    chi ρ r = 0 := by
  have hdiv : 2 ≤ 2 * r / ρ := (le_div_iff₀ hρ).2 (by nlinarith)
  have harg : 2 - 2 * r / ρ ≤ 0 := by linarith
  simp only [chi, max_eq_left harg, min_eq_right zero_le_one]

private theorem clamp_abs_sub_le (x y : ℝ) :
    |min 1 (max 0 x) - min 1 (max 0 y)| ≤ |x - y| := by
  have hmin : |min 1 (max 0 x) - min 1 (max 0 y)| ≤
      |max 0 x - max 0 y| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (max (0 : ℝ) x - max 0 y))] using
      abs_min_sub_min_le_max (1 : ℝ) (max 0 x) 1 (max 0 y)
  have hmax : |max 0 x - max 0 y| ≤ |x - y| := by
    rw [max_comm 0 x, max_comm 0 y]
    exact abs_max_sub_max_le_abs x y 0
  exact hmin.trans hmax

theorem beta_abs_sub_le {ρ : ℝ} (hρ : 0 < ρ) (r s : ℝ) :
    |beta ρ r - beta ρ s| ≤ (4 / ρ) * |r - s| := by
  have h := clamp_abs_sub_le (2 - 4 * r / ρ) (2 - 4 * s / ρ)
  have heq : (2 - 4 * r / ρ) - (2 - 4 * s / ρ) =
      -(4 / ρ * (r - s)) := by ring
  have hc : 0 ≤ (4 : ℝ) / ρ := div_nonneg (by norm_num) hρ.le
  rw [heq, abs_neg, abs_mul, abs_of_nonneg hc] at h
  exact h

theorem chi_abs_sub_le {ρ : ℝ} (hρ : 0 < ρ) (r s : ℝ) :
    |chi ρ r - chi ρ s| ≤ (2 / ρ) * |r - s| := by
  have h := clamp_abs_sub_le (2 - 2 * r / ρ) (2 - 2 * s / ρ)
  have heq : (2 - 2 * r / ρ) - (2 - 2 * s / ρ) =
      -(2 / ρ * (r - s)) := by ring
  have hc : 0 ≤ (2 : ℝ) / ρ := div_nonneg (by norm_num) hρ.le
  rw [heq, abs_neg, abs_mul, abs_of_nonneg hc] at h
  exact h

theorem beta_le_chi {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : 0 ≤ r) :
    beta ρ r ≤ chi ρ r := by
  have hrdiv : 0 ≤ r / ρ := div_nonneg hr hρ.le
  have harg : 2 - 4 * r / ρ ≤ 2 - 2 * r / ρ := by
    simp only [mul_div_assoc]
    linarith
  exact min_le_min_left 1 (max_le_max_left 0 harg)

theorem chi_le_tail {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (_hr : 0 ≤ r) (hrρ : r ≤ ρ) :
    chi ρ r ≤ 2 * (ρ - r) / ρ := by
  have hdiv : 2 * r / ρ ≤ 2 := (div_le_iff₀ hρ).2 (by nlinarith)
  have harg : 0 ≤ 2 - 2 * r / ρ := by linarith
  calc
    chi ρ r ≤ 2 - 2 * r / ρ := by
      simp only [chi, max_eq_right harg]
      exact min_le_right _ _
    _ = 2 * (ρ - r) / ρ := by
      field_simp [ne_of_gt hρ]

theorem beta_le_tail {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : 0 ≤ r) (hrρ : r ≤ ρ) :
    beta ρ r ≤ 2 * (ρ - r) / ρ :=
  (beta_le_chi hρ r hr).trans (chi_le_tail hρ r hr hrρ)

end ThompsonNonamenability.Analytic

end

end OAI
