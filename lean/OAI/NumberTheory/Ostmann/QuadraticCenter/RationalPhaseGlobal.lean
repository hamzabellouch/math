import Mathlib.Data.Nat.Cast.Order.Field
import OAI.NumberTheory.Ostmann.QuadraticCenter.RationalPhaseBlock

namespace OAI

/-! # Summing the short-block bounds over all shifts -/

namespace Ostmann

open scoped BigOperators Classical

private theorem quotient_fiber_short (i j b r : ℕ) (hb : 0 < b)
    (hr : 2 * b ≤ r) (heq : i / b = j / b) :
    2 * |(((i : ℤ) - j : ℤ) : ℝ)| ≤ r := by
  have hi := Nat.mod_add_div i b
  have hj := Nat.mod_add_div j b
  rw [heq] at hi
  have hi' : ((i % b : ℕ) : ℝ) + (b : ℝ) * (j / b : ℕ) = i := by exact_mod_cast hi
  have hj' : ((j % b : ℕ) : ℝ) + (b : ℝ) * (j / b : ℕ) = j := by exact_mod_cast hj
  have hmi : ((i % b : ℕ) : ℝ) < b := by exact_mod_cast Nat.mod_lt i hb
  have hmj : ((j % b : ℕ) : ℝ) < b := by exact_mod_cast Nat.mod_lt j hb
  have hmi0 : (0 : ℝ) ≤ ((i % b : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmj0 : (0 : ℝ) ≤ ((j % b : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr' : (2 : ℝ) * b ≤ r := by exact_mod_cast hr
  push_cast
  have hab : |(i : ℝ) - j| ≤ b := by
    apply abs_le.mpr
    constructor <;> linarith
  linarith

theorem rational_phase_global_bound (θ : ℝ) (a : ℤ) (r N H : ℕ) (M : ℕ → ℕ)
    (hr : 2 ≤ r) (hcop : a.natAbs.Coprime r)
    (happrox : |θ - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2)
    (hlen : ∀ h ∈ Finset.range H, M h ≤ N) :
    ∑ h ∈ Finset.range H, ‖∑ j ∈ Finset.range (M h), realAdditivePhase (θ * h) ^ j‖ ≤
      (4 * (H : ℝ) / r + 1) * (2 * ((N : ℝ) + r * (1 + Real.log r))) := by
  let b := r / 2
  let w := fun h : ℕ => ‖∑ j ∈ Finset.range (M h), realAdditivePhase (θ * h) ^ j‖
  let C := 2 * ((N : ℝ) + r * (1 + Real.log r))
  have hb : 0 < b := by dsimp [b]; omega
  have hb2 : 2 * b ≤ r := by dsimp [b]; omega
  have hb4 : r ≤ 4 * b := by dsimp [b]; omega
  have hrp : 0 < r := by omega
  have hmap : ∀ h ∈ Finset.range H, h / b ∈ Finset.range (H / b + 1) := by
    intro h hh
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt (Finset.mem_range.mp hh)))
  have hsum : (∑ h ∈ Finset.range H, w h) =
      ∑ k ∈ Finset.range (H / b + 1), ∑ h ∈ (Finset.range H).filter (fun h => h / b = k), w h := by
    exact (Finset.sum_fiberwise_of_maps_to hmap w).symm
  have hblock : ∀ k ∈ Finset.range (H / b + 1),
      (∑ h ∈ (Finset.range H).filter (fun h => h / b = k), w h) ≤ C := by
    intro k hk
    apply rational_phase_block_bound θ a r N M _ hrp hcop happrox
    · intro i hi j hj
      exact quotient_fiber_short i j b r hb hb2
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    · intro h hh
      exact hlen h (Finset.mem_filter.mp hh).1
  have hbound : (∑ h ∈ Finset.range H, w h) ≤ (H / b + 1 : ℕ) * C := by
    rw [hsum]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using Finset.sum_le_sum hblock
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrp
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdiv : ((H / b : ℕ) : ℝ) ≤ 4 * (H : ℝ) / r := by
    apply (Nat.cast_div_le : ((H / b : ℕ) : ℝ) ≤ (H : ℝ) / b).trans
    apply (div_le_div_iff₀ hbR hrR).mpr
    have hb4R : (r : ℝ) ≤ 4 * b := by exact_mod_cast hb4
    nlinarith [show (0 : ℝ) ≤ H from Nat.cast_nonneg H]
  have hC : 0 ≤ C := by
    have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast hrp)
    dsimp [C]
    positivity
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ hC
  push_cast
  linarith

end Ostmann

end OAI
