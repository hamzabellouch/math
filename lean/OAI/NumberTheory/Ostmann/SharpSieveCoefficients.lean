import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

namespace Ostmann

noncomputable def normalizedCoefficients (s : Finset ℕ) (n : ℕ) : ℂ :=
  if n ∈ s then (s.card : ℂ)⁻¹ else 0

theorem normalizedCoefficients_energy (s : Finset ℕ) (N : ℕ)
    (hs : s ⊆ Finset.range N) :
    (∑ n ∈ Finset.range N, ‖normalizedCoefficients s n‖ ^ 2) = (s.card : ℝ)⁻¹ := by
  classical
  calc
    (∑ n ∈ Finset.range N, ‖normalizedCoefficients s n‖ ^ 2) =
        ∑ n ∈ s, ‖normalizedCoefficients s n‖ ^ 2 := by
      symm
      exact Finset.sum_subset hs (by
        intro n hn hns
        simp [normalizedCoefficients, hns])
    _ = ∑ _n ∈ s, ((s.card : ℝ)⁻¹) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [normalizedCoefficients, hn]
    _ = (s.card : ℝ) * ((s.card : ℝ)⁻¹) ^ 2 := by simp
    _ = (s.card : ℝ)⁻¹ := by
      by_cases h : (s.card : ℝ) = 0
      · simp [h]
      · field_simp

end Ostmann

end OAI
