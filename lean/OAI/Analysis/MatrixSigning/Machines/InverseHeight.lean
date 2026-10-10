import Mathlib
import OAI.Analysis.MatrixSigning.Machines.InverseBounds

namespace OAI

section

namespace KS.W30

def inverseBitBound (n b : ℕ) : ℕ :=
  b * (n * n) + (n * n + (b * (n * n) + b) * n) + 1

theorem inverseBitBound_mono_dim {n N : ℕ} (b : ℕ) (hn : n ≤ N) :
    inverseBitBound n b ≤ inverseBitBound N b := by
  have hs := Nat.mul_le_mul hn hn
  have hb := Nat.mul_le_mul_left b hs
  exact Nat.add_le_add_right
    (Nat.add_le_add hb (Nat.add_le_add hs
      (Nat.mul_le_mul (Nat.add_le_add_right hb b) hn))) 1

theorem matrix_parts_le_of_inverse_parts {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (b : ℕ)
    (hnum : ∀ i j, (A⁻¹ i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (A⁻¹ i j).den ≤ 2 ^ b) (hdet : A.det ≠ 0)
    (i j : Fin n) :
    (A i j).num.natAbs ≤ 2 ^ inverseBitBound n b ∧
      (A i j).den ≤ 2 ^ inverseBitBound n b := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hdi : A⁻¹.det ≠ 0 := isUnit_iff_ne_zero.mp (Matrix.isUnit_nonsing_inv_det A hu)
  have hs := rational_inverse_parts_size_le A⁻¹ b hnum hden hdi i j
  rw [Matrix.nonsing_inv_nonsing_inv A hu] at hs
  exact ⟨(Nat.size_le.mp hs.1).le, (Nat.size_le.mp hs.2).le⟩

theorem matrix_parts_uniform_of_inverse_parts {n N : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (b : ℕ) (hn : n ≤ N)
    (hnum : ∀ i j, (A⁻¹ i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (A⁻¹ i j).den ≤ 2 ^ b) (hdet : A.det ≠ 0)
    (i j : Fin n) :
    (A i j).num.natAbs ≤ 2 ^ inverseBitBound N b ∧
      (A i j).den ≤ 2 ^ inverseBitBound N b := by
  have h := matrix_parts_le_of_inverse_parts A b hnum hden hdet i j
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (inverseBitBound_mono_dim b hn)
  exact ⟨h.1.trans hp, h.2.trans hp⟩

theorem inverseBitBound_le_polynomial (n b : ℕ) :
    inverseBitBound n b ≤ 6 * (b + 1) * (n + 1) ^ 3 := by
  unfold inverseBitBound
  ring_nf
  omega

theorem inverseBitBound_twice_le_polynomial (n b : ℕ) :
    inverseBitBound n (inverseBitBound n b) ≤ 32 * (b + 1) * (n + 1) ^ 6 := by
  unfold inverseBitBound
  ring_nf
  omega

theorem inverseBitBound_twice_le_input_polynomial {n b L : ℕ} (hn : n ≤ L) (hb : b ≤ L) :
    inverseBitBound n (inverseBitBound n b) ≤ 32 * (L + 1) ^ 7 := by
  apply le_trans (inverseBitBound_twice_le_polynomial n b)
  calc
    32 * (b + 1) * (n + 1) ^ 6 ≤ 32 * (L + 1) * (L + 1) ^ 6 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 32 (Nat.add_le_add_right hb 1))
        (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 6)
    _ = 32 * (L + 1) ^ 7 := by ring

end KS.W30

end

end OAI
