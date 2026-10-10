import OAI.NumberTheory.Ostmann.Construction.InitialHalfListWeights
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale
import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget

namespace OAI

/-! # The initial logarithmic cutoff centers lie below the giant scale -/

namespace Ostmann
open Filter

theorem eventually_logSumCenter_negligible (k : ℕ) (a b ε : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, n ≤ spectatorBulkCount k L →
      (⌈(n : ℝ) * Real.exp (a * L)⌉₊ : ℝ) ≤ ε * Real.exp (b * L) := by
  filter_upwards [eventual_polynomial_log_budget 1 ((k : ℝ) ^ 4) (b - a) ε 1
    (by norm_num) (by positivity) (sub_pos.mpr hab) hε,
    eventually_ge_atTop (0 : ℝ)] with L hp hL n hn
  have hm : (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L :=
    spectatorBulkCount_upper k L hL
  have hn' : (n : ℝ) ≤ spectatorBulkCount k L := by exact_mod_cast hn
  have he : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha hL)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) * Real.exp (a * L) by positivity)
  have hp' : 1 + (spectatorBulkCount k L : ℝ) ≤ ε * Real.exp ((b - a) * L) := by
    simpa only [pow_one, one_mul] using hp (spectatorBulkCount k L) (by positivity) hm
  calc
    _ ≤ (n : ℝ) * Real.exp (a * L) + 1 := hc.le
    _ ≤ (1 + (spectatorBulkCount k L : ℝ)) * Real.exp (a * L) := by
      nlinarith [mul_le_mul_of_nonneg_right hn' (Real.exp_nonneg (a * L))]
    _ ≤ (ε * Real.exp ((b - a) * L)) * Real.exp (a * L) :=
      mul_le_mul_of_nonneg_right hp' (Real.exp_nonneg _)
    _ = ε * Real.exp (b * L) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem initialLogSumWeight_support {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A)
    (h : initialLogSumWeight value c x ≠ 0) :
    |(∑ i, Real.log (value (x i) : ℝ)) - c| < 1 := by
  by_contra hn
  exact h (logCellProfile_zero_outside _ (le_of_not_gt hn))

end Ostmann

end OAI
