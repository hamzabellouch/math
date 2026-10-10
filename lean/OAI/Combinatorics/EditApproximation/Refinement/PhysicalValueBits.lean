import OAI.Combinatorics.EditApproximation.Refinement.PhysicalDenominator
import OAI.Combinatorics.EditApproximation.Numerics.NumericalWork

namespace OAI

/-! Explicit bit bounds for the actual returned physical table values. -/

namespace EditApproximation

theorem rationalEncodingBits_of_den_dvd (r : ℚ) (V D : ℕ)
    (hV : |r| ≤ V) (hD : 0 < D) (hden : r.den ∣ D) :
    rationalEncodingBits r ≤ Nat.size V + 2 * Nat.size D + 1 := by
  have hdenSize := Nat.size_le_size (Nat.le_of_dvd hD hden)
  have hnumSize := (Nat.size_le_size (rational_numerator_bound r V hV)).trans
    (natural_product_bit_length V r.den)
  unfold rationalEncodingBits
  omega

theorem physicalRefinement_encoding_bits {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (T ell : ℕ) (hell : 0 < ell)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    rationalEncodingBits (physicalRefinement source target U N P F A T
      (1 / (ell : ℚ) ^ 10) choices node t q) ≤
        Nat.size ((32 * F + 1) * N) +
          2 * (J - node.1.val) * Nat.size (ell ^ 10 + 1) + 3 := by
  let value := physicalRefinement source target U N P F A T (1 / (ell : ℚ) ^ 10) choices node t q
  have hnonneg : 0 ≤ value := physicalRefinement_nonneg_all_seeds source target U N P F A T _ choices node t q
  have hupper : value ≤ (((32 * F + 1) * N : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      physicalRefinement_upper_all_seeds source target U N P F A hsize T _ choices node t q
  have h := rationalEncodingBits_of_den_dvd value ((32 * F + 1) * N)
    ((ell ^ 10 + 1) ^ (J - node.1.val)) (by rw [abs_of_nonneg hnonneg]; exact hupper)
    (pow_pos (by omega) _) (physicalRefinement_den_dvd source target U N P F A T ell hell choices node t q)
  have hpower := natural_power_bit_length (ell ^ 10 + 1) (J - node.1.val)
  have hpowerTwice := Nat.mul_le_mul_left 2 hpower
  simp only [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hpowerTwice
  change rationalEncodingBits value ≤ _
  omega

theorem refinement_denominator_base_bits (ell : ℕ) :
    Nat.size (ell ^ 10 + 1) ≤ 10 * Nat.size ell + 3 := by
  have hsum := natural_sum_bit_length (ell ^ 10) 1
  have hpower := natural_power_bit_length ell 10
  norm_num only [Nat.size_one] at hsum
  omega

end EditApproximation

end OAI
