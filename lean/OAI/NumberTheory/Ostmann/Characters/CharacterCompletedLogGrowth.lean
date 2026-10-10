import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedDiskGrowth

namespace OAI

/-! # Subquadratic logarithmic growth of the entire completed L-function -/

namespace Ostmann

open Complex

theorem character_completed_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (s : ℂ), ‖s‖ ≤ (N : ℝ) + 1 →
      Real.log ‖χ.completed s‖ ≤
        A * ((N : ℝ) + 3) * (1 + Real.log ((N : ℝ) + 3)) := by
  obtain ⟨C, hC, hbound⟩ := character_completed_disk_growth
  let B := 2 * ((χ.modulus : ℝ) + 1) * (C + 1)
  let A := |Real.log B| + Real.log (χ.modulus : ℝ) + 1
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hlogq : 0 ≤ Real.log (χ.modulus : ℝ) := Real.log_nonneg hq
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro N s hs
  have hN : 1 ≤ (N : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hpow : 1 ≤ ((N : ℝ) + 2) ^ (N + 2) := one_le_pow₀ hN
  have hfac : ((N + 2).factorial : ℝ) ≤ ((N : ℝ) + 2) ^ (N + 2) := by
    exact_mod_cast Nat.factorial_le_pow (N + 2)
  have hcf : C + ((N + 2).factorial : ℝ) ≤ (C + 1) * ((N : ℝ) + 2) ^ (N + 2) := by
    nlinarith
  have hnorm : ‖χ.completed s‖ ≤ B * (χ.modulus : ℝ) ^ (N + 3) * ((N : ℝ) + 2) ^ (N + 3) := by
    apply (hbound χ N s hs).trans
    apply (mul_le_mul_of_nonneg_left hcf (by positivity)).trans_eq
    dsimp [B]
    rw [show N + 3 = (N + 2) + 1 by omega, pow_succ]
    ring
  have hlogN : 0 ≤ Real.log ((N : ℝ) + 3) := Real.log_nonneg (by linarith)
  by_cases hzero : χ.completed s = 0
  · rw [hzero, norm_zero, Real.log_zero]
    positivity
  · have hl := Real.log_le_log (norm_pos_iff.mpr hzero) hnorm
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
    have hn : Real.log ((N : ℝ) + 2) ≤ Real.log ((N : ℝ) + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have hb : Real.log B ≤ |Real.log B| * ((N : ℝ) + 3) := by
      apply (le_abs_self _).trans
      exact le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    have hpos : 0 ≤ (|Real.log B| + Real.log (χ.modulus : ℝ)) *
        ((N : ℝ) + 3) * Real.log ((N : ℝ) + 3) := by positivity
    dsimp [A]
    push_cast at hl
    nlinarith [mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (N : ℝ) + 3)]

end Ostmann

end OAI
