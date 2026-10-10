import OAI.Analysis.KadisonKastler.AmplificationPartition

namespace OAI

/-! # Choosing the finite degrees before the recovery randomization -/

namespace KadisonKastler

/-- The polynomial degree meets the scalar-recovery bound, and the finite
phase order exceeds twice that degree, as required by the word expansions. -/
theorem exists_recovery_degrees (n : ℕ) :
    ∃ N q : ℕ, 0 < N ∧ 2 * N < q ∧
      100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (100 * (n : ℝ) * (100 * Real.pi) ^ 3))
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_trans zero_lt_one
      (lt_of_le_of_lt (le_max_left _ _) hN)
    exact_mod_cast this
  exact ⟨N, 2 * N + 1, hNpos, by omega, (le_max_right _ _).trans hN.le⟩

end KadisonKastler

end OAI
