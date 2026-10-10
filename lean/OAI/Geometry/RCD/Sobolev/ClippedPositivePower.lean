import OAI.Geometry.RCD.Sobolev.PoissonLocality

namespace OAI

/-! # A globally Lipschitz extension of each bounded positive integer power -/

open MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates

theorem clipped_positive_power_lipschitz (A : ℝ≥0) (n : ℕ) :
    LipschitzWith ((n+1:ℕ)*A^n) (fun x : ℝ => (clipReal A x)^(n+1)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have h₁ := abs_pow_sub_pow_le (clipReal A x) (clipReal A y) (n+1)
  have hM : max |clipReal A x| |clipReal A y| ≤ A :=
    max_le (clipReal_abs_le _ _) (clipReal_abs_le _ _)
  have hp := pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hM n
  have hd := (clipReal_lipschitz A).dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hd
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h₁
  calc
    _ ≤ |clipReal A x-clipReal A y| *(n+1:ℝ)*(A:ℝ)^n :=
      h₁.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    _ ≤ |x-y| *(n+1:ℝ)*(A:ℝ)^n := by gcongr
    _ = _ := by push_cast; rw [Real.dist_eq]; ring

theorem clipped_positive_power_zero (A : ℝ≥0) (n : ℕ) :
    (clipReal A 0)^(n+1) = 0 := by rw [clipReal_zero]; simp

end RegularPointCoordinates

end

end OAI
