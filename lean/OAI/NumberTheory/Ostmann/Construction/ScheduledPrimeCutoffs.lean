import OAI.NumberTheory.Ostmann.Construction.SelectedScheduledCutoffs
import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget

namespace OAI

/-! # Every finite scheduled frequency stays below the live prime bands -/
namespace Ostmann
open Filter
open scoped BigOperators

theorem eventual_finite_frequency_band (k N : ℕ) (A : ℕ → ℝ) (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ n ≤ N,
      Real.exp (A n * spectatorBulkCount k L) < Real.exp (Real.exp (β * L)) := by
  have hi (i : Fin (N + 1)) : ∀ᶠ L : ℝ in atTop,
      A i * spectatorBulkCount k L < Real.exp (β * L) := by
    filter_upwards [eventual_polynomial_log_budget (|A i| + 1) ((k : ℝ) ^ 4) β (1 / 2) 1
      (by positivity) (by positivity) hβ (by norm_num), eventually_ge_atTop (0 : ℝ)]
      with L hbound hL
    have hm : 0 ≤ (spectatorBulkCount k L : ℝ) := Nat.cast_nonneg _
    have hh := hbound _ hm (spectatorBulkCount_upper k L hL)
    simp only [pow_one] at hh
    have ha : A i * spectatorBulkCount k L ≤ |A i| * spectatorBulkCount k L :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hm
    have hn : 0 ≤ |A i| := abs_nonneg _
    nlinarith only [hh, ha, hn, hm, Real.exp_pos (β * L)]
  filter_upwards [eventually_all.mpr hi] with L hL n hn
  exact Real.exp_lt_exp.mpr (hL ⟨n, by omega⟩)

theorem eventual_selected_frequency_band (k : ℕ) (Bs BD Bz β : ℝ) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ n ≤ k, ∀ V : ℕ → ℕ,
      (V n : ℝ) ≤ Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) n *
        spectatorBulkCount k L) →
      (V n : ℝ) < Real.exp (Real.exp (β * L)) := by
  filter_upwards [eventual_finite_frequency_band k k
    (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4)) β hβ]
    with L hL n hn V hV
  exact hV.trans_lt (hL n hn)

end Ostmann

end OAI
