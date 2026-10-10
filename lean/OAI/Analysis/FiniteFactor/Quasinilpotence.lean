import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

namespace FiniteFactor
open Filter
open scoped Topology

/-- Taking nth roots of the finite-prefix exponential bound, for n>0. -/
theorem root_le_prefix_exponential {a A B : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n)
    (hbound : a ≤ Real.exp (B - (n : ℝ)*A)) :
    a ^ (1 / (n : ℝ)) ≤ Real.exp (B / (n : ℝ) - A) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    a ^ (1 / (n : ℝ)) ≤ Real.exp (B - (n : ℝ)*A) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow ha hbound (by positivity)
    _ = Real.exp ((B - (n : ℝ)*A) * (1 / (n : ℝ))) := (Real.exp_mul _ _).symm
    _ = Real.exp (B / (n : ℝ) - A) := by
      congr 1
      field_simp

/-- The prefix is fixed before taking n→∞. Its additive loss B(q) may grow
arbitrarily with q; no uniform estimate on that loss is required. -/
theorem root_tendsto_zero_of_prefix_bounds (a A B : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hA : Tendsto A atTop atTop)
    (hbound : ∀ (q n : ℕ), 0 < n → a n ≤ Real.exp (B q - (n : ℝ)*A q)) :
    Tendsto (fun n => a n ^ (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall fun n => hl.trans_le (Real.rpow_nonneg (ha n) _)
  · intro u hu
    have hdecay : Tendsto (fun q => Real.exp (-A q)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hA
    obtain ⟨q, hq⟩ := (hdecay.eventually (gt_mem_nhds hu)).exists
    have hlim : Tendsto (fun n : ℕ => Real.exp (B q / (n : ℝ) - A q))
        atTop (𝓝 (Real.exp (-A q))) := by
      simpa only [zero_sub, Function.comp_def] using
        (Real.continuous_exp.tendsto (0 - A q)).comp
          ((tendsto_const_div_atTop_nhds_zero_nat (B q)).sub_const (A q))
    filter_upwards [hlim.eventually (gt_mem_nhds hq), eventually_gt_atTop (0 : ℕ)] with n hn hn0
    exact (root_le_prefix_exponential (ha n) hn0 (hbound q n hn0)).trans_lt hn

/-- Operator form of the analytic reduction, using precisely the norm-root
limit in MainTarget. This theorem does not assume spectral-radius theory. -/
theorem norm_quasinilpotent_of_prefix_bounds {R : Type*} [NormedRing R]
    (T : R) (A B : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hbound : ∀ (q n : ℕ), 0 < n → ‖T^n‖ ≤ Real.exp (B q - (n : ℝ)*A q)) :
    Tendsto (fun n : ℕ => ‖T^n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) :=
  root_tendsto_zero_of_prefix_bounds (fun n => ‖T^n‖) A B (fun n => norm_nonneg (T^n)) hA hbound

end FiniteFactor

end OAI
