import OAI.NumberTheory.Ostmann.Preliminaries.MertensPrimeBands
import OAI.NumberTheory.Ostmann.Construction.PrimeLogGrid

namespace OAI

/-! # A fixed positive mass in the original whole bulk shell

This uses only the stated bounded-error Mertens estimate. A single ordinary
logarithmic band inside the shell suffices for the bulk normalization.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem whole_shell_mass_lower {C : ℝ} (hM : MertensEstimate C)
    (u v : ℝ) (hu : 1 ≤ u) (herror : 2 * (Real.log 2 + 2 * C) ≤ u)
    (huv : 2 * u ≤ v) :
    (1 / 4 : ℝ) ≤ ∑ p ∈ primeLogCellSet 1 0 u v, (p : ℝ)⁻¹ := by
  have hband := (logPrimeBand_weight_bounds u C hu hM).1
  have hsub : logPrimeBand u ⊆ primeLogCellSet 1 0 u v := by
    intro p hp
    obtain ⟨hprime, hlo, hhi⟩ := logPrimeBand_mem hp
    exact mem_primeLogCellSet_iff.mpr ⟨hprime, by simp only [Nat.modEq_one],
      hlo, hhi.trans huv⟩
  have hweight : (∑ p ∈ logPrimeBand u, Real.log (p : ℝ) / p) ≤
      (2 * u) * ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hhi := (logPrimeBand_mem hp).2.2
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hhi (by positivity : 0 ≤ (p : ℝ)⁻¹)
  have hmass : (1 / 4 : ℝ) ≤ ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
    nlinarith
  exact hmass.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => by positivity))

end Ostmann

end OAI
