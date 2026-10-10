import OAI.Combinatorics.LowSpaceSubsetSum.Counting.PrimeHash
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ResidueCoverage
import Mathlib.Data.Int.ModEq

namespace OAI

/-!
# Prime hashing supplies the finite collision interface

This connects the actual finite uniform prime sampler to the previously proved
collision-to-occupancy theorem. Integer differences may have polynomially many
bits; the parameter `u` remains explicit.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

noncomputable def primeProbability (ell : ℕ) (_p : ℕ) : ℝ :=
  1 / (primeRange ell).card

theorem primeRange_nonempty {ell : ℕ} (hell : 4 ≤ ell) :
    (primeRange ell).Nonempty := by
  apply Finset.card_pos.mp
  have h := primeRange_card_lower hell
  have hp : 0 < 2 ^ ell := pow_pos (by decide) _
  nlinarith

theorem primeProbability_sum {ell : ℕ} (hell : 4 ≤ ell) :
    (∑ p ∈ primeRange ell, primeProbability ell p) = 1 := by
  have h : ((primeRange ell).card : ℝ) ≠ 0 := by
    exact_mod_cast (primeRange_nonempty hell).card_pos.ne'
  simp [primeProbability, h]

theorem prime_pairwise_collision_bound (X : Finset ℤ) {ell u : ℕ}
    (hell : 4 ≤ ell) (hellu : ell ≤ u)
    (hbits : ∀ x ∈ X, ∀ y ∈ X, (x - y).natAbs < 2 ^ (2 * u)) :
    PairwiseCollisionBound (primeRange ell) (primeProbability ell) X
      (fun p x => x % (p : ℤ)) (8 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ell) := by
  intro x hx y hy hxy
  have hd : 0 < (x - y).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hxy)
  have hiff (p : ℕ) : x % (p : ℤ) = y % (p : ℤ) ↔ p ∣ (x - y).natAbs := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero,
      Int.natCast_dvd]
  have heq : (∑ p ∈ primeRange ell,
      primeProbability ell p * if x % (p : ℤ) = y % (p : ℤ) then (1 : ℝ) else 0) =
      (((primeRange ell).filter fun p => p ∣ (x - y).natAbs).card : ℝ) /
        (primeRange ell).card := by
    simp_rw [hiff, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    simp [primeProbability, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact prime_divisor_probability_le hell hellu hd (hbits x hx y hy)

/-- The abstract occupancy result now has a proved prime-hashing input. -/
theorem prime_occupied_probability (X : Finset ℤ) {ell u : ℕ}
    (hell : 4 ≤ ell) (hellu : ell ≤ u)
    (hbits : ∀ x ∈ X, ∀ y ∈ X, (x - y).natAbs < 2 ^ (2 * u))
    {T : ℝ} (hT : 0 < T) :
    1 - ((X.card : ℝ) + (8 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ell) * (X.card : ℝ) ^ 2) / T ≤
      ∑ p ∈ (primeRange ell).filter
        (fun p : ℕ => (X.card : ℝ) ^ 2 / T ≤ ((X.image (fun x => x % (p : ℤ))).card : ℝ)),
          primeProbability ell p := by
  apply occupied_probability_of_collision_bound
  · intro p _
    exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  · exact primeProbability_sum hell
  · positivity
  · exact hT
  · exact prime_pairwise_collision_bound X hell hellu hbits

end LowSpaceSubsetSum

end OAI
