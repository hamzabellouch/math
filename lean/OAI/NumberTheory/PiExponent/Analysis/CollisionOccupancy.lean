import Mathlib

namespace OAI

namespace PiExponent.Collision

open scoped BigOperators

variable {G : Type*}

theorem sum_sq_le_card_mul_sum_sq (S : Finset G) (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ S, n a ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : G => (1 : ℝ)) n

theorem sum_sq_le_card_mul_total_sq (S U : Finset G) (hSU : S ⊆ U)
    (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ U, n a ^ 2 := by
  apply (sum_sq_le_card_mul_sum_sq S n).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg hSU (fun a _ _ => sq_nonneg (n a))

theorem mass_sq_div_card_le_total_sq (S U : Finset G) (hSU : S ⊆ U)
    (n : G → ℝ) {mass : ℝ} (hmass : 0 ≤ mass)
    (hlow : mass ≤ ∑ a ∈ S, n a) (hcard : 0 < S.card) :
    mass ^ 2 / (S.card : ℝ) ≤ ∑ a ∈ U, n a ^ 2 := by
  have hsq : mass ^ 2 ≤ (∑ a ∈ S, n a) ^ 2 := by
    exact pow_le_pow_left₀ hmass hlow 2
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hcard
  apply (div_le_iff₀ hc).2
  calc
    mass ^ 2 ≤ (∑ a ∈ S, n a) ^ 2 := hsq
    _ ≤ (S.card : ℝ) * ∑ a ∈ U, n a ^ 2 :=
      sum_sq_le_card_mul_total_sq S U hSU n
    _ = (∑ a ∈ U, n a ^ 2) * (S.card : ℝ) := mul_comm _ _

theorem fraction_sq_mul_mass_sq_div_card_le_total_sq
    (S U : Finset G) (hSU : S ⊆ U) (n : G → ℝ)
    {η M : ℝ} (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hlow : η * M ≤ ∑ a ∈ S, n a) (hcard : 0 < S.card) :
    η ^ 2 * M ^ 2 / (S.card : ℝ) ≤ ∑ a ∈ U, n a ^ 2 := by
  simpa only [mul_pow] using
    mass_sq_div_card_le_total_sq S U hSU n (mul_nonneg hη hM) hlow hcard

variable [Fintype G]

theorem sum_sq_le_card_mul_univ_sq (S : Finset G) (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a, n a ^ 2 := by
  exact sum_sq_le_card_mul_total_sq S Finset.univ (Finset.subset_univ S) n

theorem nat_occupancy_square_lower_bound (S : Finset G) (n : G → ℕ)
    {η : ℝ} {M : ℕ} (hη : 0 ≤ η)
    (hlow : η * (M : ℝ) ≤ ∑ a ∈ S, (n a : ℝ)) (hcard : 0 < S.card) :
    η ^ 2 * (M : ℝ) ^ 2 / (S.card : ℝ) ≤ ∑ a, (n a : ℝ) ^ 2 := by
  exact fraction_sq_mul_mass_sq_div_card_le_total_sq S Finset.univ
    (Finset.subset_univ S) (fun a => (n a : ℝ)) hη (Nat.cast_nonneg M) hlow hcard

end PiExponent.Collision

end OAI
