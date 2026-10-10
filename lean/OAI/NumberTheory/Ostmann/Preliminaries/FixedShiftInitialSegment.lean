import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Preliminaries.SummandTails

namespace OAI

/-! # Restoring the removed initial interval in fixed-shift sieving -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem summandPrefix_card_le_initial_add_tail (C : Set ℕ) (lo N : ℕ) :
    (summandPrefix C N).card ≤ lo + 1 + (summandTail C lo N).card := by
  have hsub : summandPrefix C N ⊆ Finset.range (lo + 1) ∪ summandTail C lo N := by
    intro a ha
    obtain ⟨haC, haN⟩ := mem_summandPrefix C N a |>.mp ha
    by_cases hlo : a ≤ lo
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · exact Finset.mem_union_right _ (mem_summandTail C lo N a |>.mpr ⟨haC, by omega, haN⟩)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [Finset.card_range] using hh

 theorem sqrt_log_power_initial_small (j : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, (Real.sqrt x + C + 1) * Real.log x ^ j ≤ x := by
  have hc : 0 < 1 / (C + 2) := by positivity
  have hbound := (isLittleO_log_rpow_rpow_atTop (j : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).bound hc
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hr : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by simpa using hx1)
  have hp : 0 ≤ Real.log x ^ j := pow_nonneg hl _
  rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hp, abs_of_nonneg (Real.sqrt_nonneg x)] at hx
  have hlog : Real.log x ^ j ≤ Real.sqrt x / (C + 2) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hx
  have hm : (C + 2) * Real.log x ^ j ≤ Real.sqrt x := by
    have hh := (le_div_iff₀ (by positivity : 0 < C + 2)).mp hlog
    nlinarith
  have hs : Real.sqrt x + C + 1 ≤ (C + 2) * Real.sqrt x := by nlinarith
  calc
    _ ≤ ((C + 2) * Real.sqrt x) * Real.log x ^ j := mul_le_mul_of_nonneg_right hs hp
    _ = Real.sqrt x * ((C + 2) * Real.log x ^ j) := by ring
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg x)
    _ = x := by nlinarith [Real.sq_sqrt hx0]

end Ostmann

end OAI
