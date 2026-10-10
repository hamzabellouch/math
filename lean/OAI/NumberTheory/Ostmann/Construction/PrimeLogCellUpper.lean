import OAI.NumberTheory.Ostmann.ZeroDensity.OrdinaryPrimeIntervals
import OAI.NumberTheory.Ostmann.Construction.PrimeCellPartitionConstruction

namespace OAI

/-! # Uniform upper mass bound on a logarithmic prime cell -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem log_unit_ratio_upper {s : ℝ} (hs : 0 < s) :
    Real.log ((s + 1) / s) ≤ 1 / s := by
  have hh := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < s + 1) hs)
  have heq : (s + 1) / s - 1 = 1 / s := by field_simp; ring
  rwa [heq] at hh

theorem PublishedProgressionInput.ordinary_interval_upper (P : PublishedProgressionInput) :
    ∀ᶠ s : ℝ in atTop,
      reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp (s + 1)) ≤ 2 / s := by
  filter_upwards [theta_log_error_small P.errorConstant P.decay P.decay_pos,
    eventually_ge_atTop (1 : ℝ)] with s herr hs
  have hmain := P.ordinary_log_interval hs (by linarith : s ≤ s + 1) le_rfl
  have hlog := log_unit_ratio_upper (by linarith : 0 < s)
  have herror : 1 / (2 * (s + 1)) ≤ 1 / s :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h := (abs_le.mp hmain).2
  rw [show 2 / s = 1 / s + 1 / s by ring]
  linarith

theorem sum_primeLogCellSet_reciprocal (q a : ℕ) (s t : ℝ) :
    (∑ p ∈ primeLogCellSet q a s t, (p : ℝ)⁻¹) =
      reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) := by
  simp only [primeLogCellSet, Finset.sum_filter, reciprocalPrimeInterval]

/-- Every subset of the actual prime cell has reciprocal mass `O(1/s)`,
uniformly in the subset. -/
theorem PublishedProgressionInput.prime_log_cell_upper (P : PublishedProgressionInput) :
    ∀ᶠ s : ℝ in atTop, ∀ E : Finset ℕ,
      E ⊆ primeLogCellSet 1 0 s (s + 1) → (∑ p ∈ E, (p : ℝ)⁻¹) ≤ 2 / s := by
  filter_upwards [P.ordinary_interval_upper] with s hs E hE
  calc
    _ ≤ ∑ p ∈ primeLogCellSet 1 0 s (s + 1), (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun p _ _ => by positivity)
    _ ≤ 2 / s := by rw [sum_primeLogCellSet_reciprocal]; exact hs

end Ostmann

end OAI
