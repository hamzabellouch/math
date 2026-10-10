import OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedCongruenceCount
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! The free residue digits in the mixed congruence count total the
triangular exponent r(r-1)/2. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_congruence_exponent_sum {r k : ℕ} (hrk : r≤k) :
    (∑ j∈range k, (r-min (j+1) r)) = r*(r-1)/2 := by
  have hcut : (∑ j∈range r, (r-min (j+1) r)) =
      ∑ j∈range k, (r-min (j+1) r) := by
    apply sum_subset (range_mono hrk)
    intro j _ hj
    have hh : r≤j := Nat.le_of_not_gt (fun h => hj (mem_range.mpr h))
    rw [Nat.min_eq_right (by omega),Nat.sub_self]
  rw [← hcut]
  calc
    _ = ∑ j∈range r, (r-1-j) := by
      apply sum_congr rfl
      intro j hj
      have hjr := mem_range.mp hj
      omega
    _ = ∑ j∈range r, j := sum_range_reflect (fun j => j) r
    _ = _ := sum_range_id r

theorem halasz_congruence_digit_product {p r k : ℕ} (hrk : r≤k) :
    (∏ j : Fin k, p^(r-min (j.val+1) r)) = p^(r*(r-1)/2) := by
  rw [prod_pow_eq_pow_sum]
  congr 1
  simpa only [← Fin.sum_univ_eq_sum_range] using halasz_congruence_exponent_sum hrk

end TwoPointCorrelations

end OAI
