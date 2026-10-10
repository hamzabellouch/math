import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion

namespace Kadison

theorem coefficient_zero_of_unbounded_stages
    (z : ℂ) (C : ℝ) (p c : ℕ) (m : ℕ → ℕ)
    (hm : ∀ B : ℕ, ∃ n, B ≤ m n)
    (hbound : ∀ n, ‖z‖ ^ 2 * (m n : ℝ) ^ (p + 1) ≤
      C ^ 2 * (m n : ℝ) ^ (2 * c))
    (hc : 2 * c < p + 1) : z = 0 := by
  by_contra hz
  have hl : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  obtain ⟨B, hB⟩ := exists_nat_gt (max (C ^ 2 / ‖z‖ ^ 2) 1)
  obtain ⟨n, hn⟩ := hm B
  have hmn : (B : ℝ) ≤ m n := by exact_mod_cast hn
  have hm1 : 1 < (m n : ℝ) := (lt_of_le_of_lt (le_max_right _ _) hB).trans_le hmn
  have ht : C ^ 2 / ‖z‖ ^ 2 < (m n : ℝ) :=
    (lt_of_le_of_lt (le_max_left _ _) hB).trans_le hmn
  have hh := hbound n
  have hpow : (m n : ℝ) ^ (2 * c + 1) ≤ (m n : ℝ) ^ (p + 1) :=
    pow_le_pow_right₀ hm1.le hc
  have hpowpos : 0 < (m n : ℝ) ^ (2 * c) := pow_pos (by linarith) _
  have hh' : ‖z‖ ^ 2 * (m n : ℝ) ^ (2 * c + 1) ≤
      C ^ 2 * (m n : ℝ) ^ (2 * c) :=
    (mul_le_mul_of_nonneg_left hpow hl.le).trans hh
  rw [pow_succ (m n : ℝ) (2 * c)] at hh'
  have hle : ‖z‖ ^ 2 * (m n : ℝ) ≤ C ^ 2 := by
    apply (mul_le_mul_iff_right₀ hpowpos).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh'
  have hgt : C ^ 2 < (m n : ℝ) * ‖z‖ ^ 2 := (div_lt_iff₀ hl).mp ht
  nlinarith

end Kadison
end

end OAI
