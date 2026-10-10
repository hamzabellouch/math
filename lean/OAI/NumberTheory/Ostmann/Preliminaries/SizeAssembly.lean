import OAI.NumberTheory.Ostmann.Preliminaries.SquareRootTransfer

namespace OAI

namespace Ostmann.Preliminaries
open Filter

theorem sqrt_upper_of_cubic_log_sparsity (d : Decomposition) {C : ℝ} (hC : 0 < C)
    (hsparse : ∀ᶠ X : ℕ in atTop,
      (countUpTo d.A X : ℝ) ≤ C * X / Real.log (X : ℝ) ^ 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℕ in atTop,
      (countUpTo d.A X : ℝ) ≤ K * Real.sqrt X * Real.log (X : ℝ) ^ 2 := by
  have hlower := eventual_polylog_lower_of_upper d.swap 2 hC hsparse
  have hc : 0 < Real.log 2 / (2 * C) := by positivity
  obtain ⟨C1, hC1, hrough⟩ := eventually_count_square_rough d hc hlower
  obtain ⟨C2, hC2, hH⟩ := eventually_H_le_log_of_rough_count d hC1 hrough
  obtain ⟨C3, hC3, hsharp⟩ := eventually_count_square_sharp_of_H d hC2 hH
  exact ⟨2 * C3, by positivity, eventually_sqrt_upper_of_square d.A hC3 hsharp⟩

theorem sqrt_bounds_of_cubic_log_sparsity (d : Decomposition) {CA CB : ℝ}
    (hCA : 0 < CA) (hCB : 0 < CB)
    (hA : ∀ᶠ X : ℕ in atTop,
      (countUpTo d.A X : ℝ) ≤ CA * X / Real.log (X : ℝ) ^ 3)
    (hB : ∀ᶠ X : ℕ in atTop,
      (countUpTo d.B X : ℝ) ≤ CB * X / Real.log (X : ℝ) ^ 3) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ countUpTo d.A X ∧
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ countUpTo d.B X ∧
      (countUpTo d.A X : ℝ) ≤ C * Real.sqrt X * Real.log (X : ℝ) ^ 2 ∧
      (countUpTo d.B X : ℝ) ≤ C * Real.sqrt X * Real.log (X : ℝ) ^ 2 := by
  obtain ⟨KA, hKA, hAu⟩ := sqrt_upper_of_cubic_log_sparsity d hCA hA
  obtain ⟨KB, hKB, hBu⟩ := sqrt_upper_of_cubic_log_sparsity d.swap hCB hB
  have hAl := eventually_sqrt_lower_of_upper d hKB hBu
  have hBl := eventually_sqrt_lower_of_upper d.swap hKA hAu
  let c := min (Real.log 2 / (2 * KB)) (Real.log 2 / (2 * KA))
  let C := max KA KB
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := lt_of_lt_of_le hKA (le_max_left _ _)
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hAu, hBu, hAl, hBl, eventually_ge_atTop 2] with X hAu hBu hAl hBl hX
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply le_trans _ hAl
    gcongr
    exact min_le_left _ _
  · apply le_trans _ hBl
    gcongr
    exact min_le_right _ _
  · apply hAu.trans
    gcongr
    exact le_max_left _ _
  · apply hBu.trans
    gcongr
    exact le_max_right _ _

end Ostmann.Preliminaries

end OAI
