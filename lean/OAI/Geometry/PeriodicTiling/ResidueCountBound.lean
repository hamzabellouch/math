import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace PeriodicTilingThree

theorem one_sub_pow_mul_linear_le_one (c : ℚ) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (r : ℕ) : (1 - c) ^ r * (1 + (r : ℚ) * c) ≤ 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hstep : (1 - c) * (1 + ((r : ℚ) + 1) * c) ≤ 1 + (r : ℚ) * c := by
        calc
          (1 - c) * (1 + ((r : ℚ) + 1) * c) =
              (1 + (r : ℚ) * c) - ((r : ℚ) + 1) * c ^ 2 := by ring
          _ ≤ 1 + (r : ℚ) * c :=
            sub_le_self _ (mul_nonneg (add_nonneg (Nat.cast_nonneg r) zero_le_one)
              (sq_nonneg c))
      calc
        (1 - c) ^ (r + 1) * (1 + ((r + 1 : ℕ) : ℚ) * c) =
            (1 - c) ^ r * ((1 - c) * (1 + ((r : ℚ) + 1) * c)) := by
              rw [pow_succ, Nat.cast_add, Nat.cast_one]
              ring
        _ ≤ (1 - c) ^ r * (1 + (r : ℚ) * c) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg (sub_nonneg.mpr hc1) r)
        _ ≤ 1 := ih

private theorem scalar_half_bound (x c : ℚ) (hx : 0 ≤ x)
    (hc : (1 : ℚ) / 1000 ≤ c) (h : x * (1 + 1000 * c) ≤ 1) : x ≤ 1 / 2 := by
  have htwo : (2 : ℚ) ≤ 1 + 1000 * c := by linarith only [hc]
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mpr
  exact (mul_le_mul_of_nonneg_left htwo hx).trans h

theorem residue_block_bound (c : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hc : (1 : ℚ) / 1000 ≤ c) : (1 - c) ^ 1000 ≤ 1 / 2 := by
  apply scalar_half_bound ((1 - c) ^ 1000) c
    (pow_nonneg (sub_nonneg.mpr hc1) 1000) hc
  exact one_sub_pow_mul_linear_le_one c hc0 hc1 1000

theorem residue_failure_block_bound : ((15598 : ℚ) / 15625) ^ 1000 ≤ 1 / 2 := by
  have h := residue_block_bound ((27 : ℚ) / 15625) (by norm_num)
    (by norm_num) (by norm_num)
  have heq : (1 : ℚ) - 27 / 15625 = 15598 / 15625 := by norm_num
  rw [heq] at h
  exact h

private theorem union_bound_from_block (p : ℚ) (hp : 0 ≤ p)
    (hblock : p ^ 1000 ≤ 1 / 2) : (129 : ℚ) ^ 3 * p ^ 32000 < 1 := by
  have hblocks : p ^ 32000 ≤ ((1 : ℚ) / 2) ^ 32 := by
    rw [show (32000 : ℕ) = 1000 * 32 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (a := p ^ 1000) (b := (1 : ℚ) / 2)
      (pow_nonneg hp 1000) hblock 32
  calc
    (129 : ℚ) ^ 3 * p ^ 32000 ≤
        (129 : ℚ) ^ 3 * ((1 : ℚ) / 2) ^ 32 :=
      mul_le_mul_of_nonneg_left hblocks (by norm_num)
    _ < 1 := by norm_num

theorem residue_union_bound_32000 :
    (129 : ℚ) ^ 3 * ((15598 : ℚ) / 15625) ^ 32000 < 1 := by
  exact union_bound_from_block ((15598 : ℚ) / 15625) (by norm_num)
    residue_failure_block_bound

theorem residue_union_bound_of_large_exponent {k : ℕ} (hk : 32000 ≤ k) :
    (129 : ℚ) ^ 3 * ((15598 : ℚ) / 15625) ^ k < 1 := by
  apply lt_of_le_of_lt _ residue_union_bound_32000
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) (by norm_num)

theorem residue_cube_64 : (64 : ℕ) ^ 3 = 262144 := by norm_num

theorem residue_matching_budget_64 : 32000 ≤ (64 : ℕ) ^ 3 / 3 - 1 := by
  norm_num

end PeriodicTilingThree

end OAI
