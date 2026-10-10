import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic

namespace OAI

open Filter
namespace Ostmann.Characters.HistoryFrequencyBudget

theorem eventually_const_sqrt_le (b c δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℝ in atTop, b*Real.sqrt m+c ≤ δ*m := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((2*|b|/δ)^2),eventually_ge_atTop (2*|c|/δ)] with m hm hb hc
  have hm0 : 0 ≤ m := by linarith
  have hs : 2*|b|/δ ≤ Real.sqrt m :=
    (Real.le_sqrt (by positivity) hm0).mpr hb
  have hs' : 2*|b| ≤ Real.sqrt m*δ := (div_le_iff₀ hδ).mp hs
  have hc' : 2*|c| ≤ m*δ := (div_le_iff₀ hδ).mp hc
  have hh := mul_le_mul_of_nonneg_right hs' (Real.sqrt_nonneg m)
  have hsq := Real.sq_sqrt hm0
  have hbc := mul_le_mul_of_nonneg_right (le_abs_self b) (Real.sqrt_nonneg m)
  nlinarith [le_abs_self c]

end Ostmann.Characters.HistoryFrequencyBudget

end OAI
