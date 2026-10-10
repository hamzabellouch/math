import Mathlib

namespace OAI

section

namespace KS.W19

def directedRound (q z d : ℚ) : ℚ :=
  q * (⌊(z - |d|) / q⌋ : ℤ)

def roundingResidual (q z d : ℚ) : ℚ :=
  z - |d| - directedRound q z d

theorem directedRound_grid (q z d : ℚ) :
    ∃ k : ℤ, directedRound q z d = q * k :=
  ⟨⌊(z - |d|) / q⌋, rfl⟩

theorem roundingResidual_nonneg (q z d : ℚ) (hq : 0 < q) :
    0 ≤ roundingResidual q z d := by
  simpa [roundingResidual, directedRound, mul_comm] using
    Int.sub_floor_div_mul_nonneg (z - |d|) hq

theorem roundingResidual_lt (q z d : ℚ) (hq : 0 < q) :
    roundingResidual q z d < q := by
  simpa [roundingResidual, directedRound, mul_comm] using
    Int.sub_floor_div_mul_lt (z - |d|) hq

theorem directedRound_decomposition (q z d : ℚ) :
    directedRound q z d = z - |d| - roundingResidual q z d := by
  simp [roundingResidual]

theorem abs_sub_sign_mul_nonneg {d theta : ℚ}
    (htheta : theta = 1 ∨ theta = -1) : 0 ≤ |d| - theta * d := by
  rcases htheta with rfl | rfl
  · simpa using sub_nonneg.mpr (le_abs_self d)
  · have h := neg_le_abs d
    simpa using sub_nonneg.mpr h

theorem roundingCoefficient_nonneg (q z d theta : ℚ) (hq : 0 < q)
    (htheta : theta = 1 ∨ theta = -1) :
    0 ≤ |d| - theta * d + roundingResidual q z d :=
  add_nonneg (abs_sub_sign_mul_nonneg htheta) (roundingResidual_nonneg q z d hq)

theorem directedRound_cast (q z d : ℚ) :
    (directedRound q z d : ℝ) =
      (q : ℝ) * (⌊((z : ℝ) - |(d : ℝ)|) / (q : ℝ)⌋ : ℤ) := by
  have hf : (⌊((z : ℝ) - |(d : ℝ)|) / (q : ℝ)⌋ : ℤ) =
      ⌊(z - |d|) / q⌋ := by
    simpa only [Rat.cast_div, Rat.cast_sub, Rat.cast_abs] using
      (Rat.floor_cast (α := ℝ) ((z - |d|) / q))
  simp only [directedRound, Rat.cast_mul, Rat.cast_intCast, hf]

theorem directedRound_cast_decomposition (q z d : ℚ) :
    (directedRound q z d : ℝ) = (z : ℝ) - |(d : ℝ)| -
      (roundingResidual q z d : ℝ) := by
  exact_mod_cast directedRound_decomposition q z d

theorem roundingResidual_cast_bounds (q z d : ℚ) (hq : 0 < q) :
    0 ≤ (roundingResidual q z d : ℝ) ∧
      (roundingResidual q z d : ℝ) < (q : ℝ) := by
  constructor
  · exact_mod_cast roundingResidual_nonneg q z d hq
  · exact_mod_cast roundingResidual_lt q z d hq

theorem roundingCoefficient_cast_nonneg (q z d theta : ℚ) (hq : 0 < q)
    (htheta : theta = 1 ∨ theta = -1) :
    0 ≤ |(d : ℝ)| - (theta : ℝ) * (d : ℝ) +
      (roundingResidual q z d : ℝ) := by
  exact_mod_cast roundingCoefficient_nonneg q z d theta hq htheta

end KS.W19

end

end OAI
