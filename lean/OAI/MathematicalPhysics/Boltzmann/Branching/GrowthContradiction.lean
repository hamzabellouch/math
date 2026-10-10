import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace OAI

/-!
# The scalar contradiction in the branching argument

At the end of Section 9 of the supplied manuscript, the mass in the moving box is bounded
below by `3^n * m₀` and above by `C * (1 + (1+a)^n * t₀)^4`. The following argument proves
that those estimates cannot both hold when `(1+a)^4 < 3`. It assumes no kinetic equation,
branching kernel, or existence statement.
-/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GrowthContradiction

/-- The fourth-power cap along a geometric sequence of times is itself bounded by a geometric
sequence, with growth ratio `r^4`. -/
theorem fourth_power_cap_le {r t₀ : ℝ} (hr : 1 ≤ r) (ht₀ : 0 ≤ t₀) (n : ℕ) :
    (1 + r ^ n * t₀) ^ 4 ≤ (1 + t₀) ^ 4 * (r ^ 4) ^ n := by
  have hpow : 1 ≤ r ^ n := one_le_pow₀ hr
  have hbase : 1 + r ^ n * t₀ ≤ (1 + t₀) * r ^ n := by nlinarith only [hpow]
  calc
    (1 + r ^ n * t₀) ^ 4 ≤ ((1 + t₀) * r ^ n) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = (1 + t₀) ^ 4 * (r ^ 4) ^ n := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm n 4]

/-- The simultaneous branching lower bound and fourth-power cap bound are impossible. -/
theorem no_uniform_branching_cap {a t₀ m₀ C : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t₀) (hm₀ : 0 < m₀) (hC : 0 ≤ C)
    (hgrowth : (1 + a) ^ 4 < 3) :
    ¬ ∀ n : ℕ, (3 : ℝ) ^ n * m₀ ≤ C * (1 + (1 + a) ^ n * t₀) ^ 4 := by
  intro hcap
  let r : ℝ := 1 + a
  let D : ℝ := C * (1 + t₀) ^ 4
  have hr : 1 ≤ r := by dsimp only [r]; linarith
  have hq0 : 0 ≤ r ^ 4 / 3 := by positivity
  have hq1 : r ^ 4 / 3 < 1 := (div_lt_one (by norm_num)).mpr hgrowth
  have hupper (n : ℕ) : (3 : ℝ) ^ n * m₀ ≤ D * (r ^ 4) ^ n := by
    calc
      (3 : ℝ) ^ n * m₀ ≤ C * (1 + r ^ n * t₀) ^ 4 := hcap n
      _ ≤ C * ((1 + t₀) ^ 4 * (r ^ 4) ^ n) :=
        mul_le_mul_of_nonneg_left (fourth_power_cap_le hr ht₀.le n) hC
      _ = D * (r ^ 4) ^ n := by dsimp only [D]; ring
  have hnormalized (n : ℕ) : m₀ ≤ D * (r ^ 4 / 3) ^ n := by
    calc
      m₀ ≤ D * (r ^ 4) ^ n / (3 : ℝ) ^ n := by
        apply (le_div_iff₀ (by positivity : 0 < (3 : ℝ) ^ n)).mpr
        simpa only [mul_comm] using hupper n
      _ = D * (r ^ 4 / 3) ^ n := by rw [div_pow, mul_div_assoc]
  have hlimit : Tendsto (fun n : ℕ => D * (r ^ 4 / 3) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul D
  have hzero : m₀ ≤ 0 := ge_of_tendsto' hlimit hnormalized
  exact (not_le_of_gt hm₀) hzero

/-- Consequently some generation has branching mass strictly larger than the cap permits. -/
theorem exists_generation_exceeding_cap {a t₀ m₀ C : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t₀) (hm₀ : 0 < m₀) (hC : 0 ≤ C)
    (hgrowth : (1 + a) ^ 4 < 3) :
    ∃ n : ℕ, C * (1 + (1 + a) ^ n * t₀) ^ 4 < (3 : ℝ) ^ n * m₀ := by
  have h := no_uniform_branching_cap ha ht₀ hm₀ hC hgrowth
  push Not at h
  exact h

end BoltzmannNonuniqueness.GrowthContradiction

end

end OAI
