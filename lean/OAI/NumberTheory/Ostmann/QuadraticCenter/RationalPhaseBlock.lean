import Mathlib.NumberTheory.Harmonic.Bounds
import OAI.NumberTheory.Ostmann.QuadraticCenter.RationalPhaseSeparation
import OAI.NumberTheory.Ostmann.Construction.SeparatedPhasePacking

namespace OAI

/-! # The harmonic bound for one short rational phase block -/

namespace Ostmann

open scoped BigOperators Classical

theorem phase_bin_sum_eq (r : ℕ) (N : ℝ) :
    (∑ k ∈ Finset.range (r + 1), if k = 0 then N else (r : ℝ) / k) =
      N + r * (harmonic r : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, ite_true,
    Nat.cast_add, Nat.cast_one]
  rw [harmonic, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  rw [Finset.mul_sum]
  simp only [div_eq_mul_inv]
  ring

/-- All points may be translated by an arbitrary integer block location.
Only the pairwise short-shift condition enters the estimate. -/
theorem rational_phase_block_bound (θ : ℝ) (a : ℤ) (r N : ℕ) (M : ℕ → ℕ) (S : Finset ℕ)
    (hr : 0 < r) (hcop : a.natAbs.Coprime r)
    (happrox : |θ - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2)
    (hshort : ∀ i ∈ S, ∀ j ∈ S, 2 * |(((i : ℤ) - j : ℤ) : ℝ)| ≤ (r : ℝ))
    (hlen : ∀ h ∈ S, M h ≤ N) :
    ∑ h ∈ S, ‖∑ j ∈ Finset.range (M h), realAdditivePhase (θ * h) ^ j‖ ≤
      2 * ((N : ℝ) + r * (1 + Real.log r)) := by
  let f := fun h : ℕ => θ * h - (round (θ * h) : ℤ)
  let w := fun h : ℕ => ‖∑ j ∈ Finset.range (M h), realAdditivePhase (θ * h) ^ j‖
  have hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 / (2 * (r : ℝ)) ≤ |f i - f j| := by
    intro i hi j hj hij
    have hd : (i : ℤ) - j ≠ 0 := by
      intro heq
      exact hij (by exact_mod_cast sub_eq_zero.mp heq)
    have hb := rational_phase_shift_separation θ a ((i : ℤ) - j)
      (round (θ * i) - round (θ * j)) r hr hcop hd (hshort i hi j hj) happrox
    convert hb using 1
    push_cast
    dsimp [f]
    congr 1
    ring
  have hweight := separated_phase_weight_sum S f w r N hr (Nat.cast_nonneg N)
    (fun h _ => abs_sub_round (θ * h)) hsep (fun _ _ => norm_nonneg _)
    (fun h hh => (linear_phase_sum_distance_bound (θ * h) (M h)).1.trans (by exact_mod_cast hlen h hh))
    (fun h _ => (linear_phase_sum_distance_bound (θ * h) (M h)).2)
  rw [phase_bin_sum_eq] at hweight
  apply hweight.trans
  have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log r) (Nat.cast_nonneg r)
  linarith

end Ostmann

end OAI
