import OAI.NumberTheory.Ostmann.Characters.CharacterDiskGrowth

namespace OAI

/-! # Polynomial logarithmic growth along the contour disks -/

namespace Ostmann

open Complex Metric

theorem character_contour_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ∃ M : ℝ, 1 ≤ M ∧
      (∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M) ∧
      Real.log (3 * M) ≤ B * (1 + |t|) := by
  obtain ⟨C, hC, hbound⟩ := character_L_contour_disk_growth
  let D := max C 1
  let Q := 3 * D * (χ.modulus : ℝ) ^ 4
  let B := |Real.log Q| + 20 + 4 * Real.pi
  have hD : 1 ≤ D := le_max_right _ _
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro t
  let M := D * (χ.modulus : ℝ) ^ 4 * (9 + |t|) * Real.exp (Real.pi * (|t| + 3))
  have hM : 1 ≤ M := by
    dsimp [M]
    have hpow : 1 ≤ (χ.modulus : ℝ) ^ 4 := one_le_pow₀ hq
    have he : 1 ≤ Real.exp (Real.pi * (|t| + 3)) := Real.one_le_exp (by positivity)
    have hmul : 1 ≤ D * (χ.modulus : ℝ) ^ 4 := one_le_mul_of_one_le_of_one_le hD hpow
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hmul (by linarith [abs_nonneg t])) he
  refine ⟨M, hM, ?_, ?_⟩
  · intro z hz
    apply (hbound χ t z hz).trans
    dsimp [M, D]
    gcongr
    exact le_max_left _ _
  · have hMprod : 3 * M = Q * (9 + |t|) * Real.exp (Real.pi * (|t| + 3)) := by
      dsimp [M, Q]
      ring
    rw [hMprod, Real.log_mul (by positivity) (by positivity),
      Real.log_mul hQ.ne' (by positivity), Real.log_exp]
    have hlog : Real.log (9 + |t|) ≤ 8 + |t| := by
      have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 9 + |t|)
      linarith
    have hb : 1 + Real.pi ≤ B := by
      dsimp [B]
      nlinarith [Real.pi_pos, abs_nonneg (Real.log Q)]
    have hc : Real.log Q + 8 + 3 * Real.pi ≤ B := by
      dsimp [B]
      nlinarith [le_abs_self (Real.log Q), Real.pi_pos]
    have hh := mul_le_mul_of_nonneg_right hb (abs_nonneg t)
    nlinarith

end Ostmann

end OAI
