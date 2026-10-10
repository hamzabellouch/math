import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337

/-- The reduced denominator of a finite rational sum divides the product of
its summands' reduced denominators. -/
theorem sum_den_dvd_prod {α : Type*} [DecidableEq α]
    (s : Finset α) (q : α → ℚ) :
    (∑ j ∈ s, q j).den ∣ ∏ j ∈ s, (q j).den := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul_left _ ih)

/-- A positive rational with denominator dividing `P` is at least `1/P`. -/
theorem one_div_le_of_den_dvd {q : ℚ} {P : ℕ}
    (hq : 0 < q) (hP : 0 < P) (hd : q.den ∣ P) :
    (1 : ℚ) / P ≤ q := by
  have hden : q.den ≤ P := Nat.le_of_dvd hP hd
  have hnum : (1 : ℚ) ≤ q.num := by
    exact_mod_cast (Rat.num_pos.mpr hq)
  calc
    (1 : ℚ) / P ≤ 1 / q.den := by
      exact one_div_le_one_div_of_le (by exact_mod_cast q.den_pos) (by exact_mod_cast hden)
    _ ≤ (q.num : ℚ) / q.den :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = q := Rat.num_div_den q

/-- The remainder after subtracting finitely many positive unit fractions
from one has a gap of at least the reciprocal of the denominator product. -/
theorem prefix_remainder_gap {α : Type*} [DecidableEq α]
    (s : Finset α) (n : α → ℕ)
    (hn : ∀ j ∈ s, 0 < n j)
    (hrem : 0 < 1 - ∑ j ∈ s, (1 : ℚ) / (n j : ℚ)) :
    (1 : ℚ) / (∏ j ∈ s, n j : ℕ) ≤
      1 - ∑ j ∈ s, (1 : ℚ) / (n j : ℚ) := by
  apply one_div_le_of_den_dvd hrem
  · exact Finset.prod_pos hn
  · have hd := sum_den_dvd_prod s (fun j => (1 : ℚ) / (n j : ℚ))
    have heq : (∏ j ∈ s, ((1 : ℚ) / (n j : ℚ)).den) = ∏ j ∈ s, n j := by
      apply Finset.prod_congr rfl
      intro j hj
      simpa only [one_div] using Rat.inv_natCast_den_of_pos (hn j hj)
    simpa only [Rat.ofNat_sub_den, heq] using hd

end Problem337

end OAI
