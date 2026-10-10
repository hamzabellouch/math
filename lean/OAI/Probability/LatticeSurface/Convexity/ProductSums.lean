import Mathlib

namespace OAI

open scoped BigOperators

example (s t : Finset ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ x ∈ s.product t, f x) = ∑ x ∈ s, ∑ y ∈ t, f (x,y) := by
  exact Finset.sum_product s t f

example (s t : Finset ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ x ∈ s.product t, f x) = ∑ x ∈ s, ∑ y ∈ t, f (x,y) := by
  exact Finset.sum_product s t f

end OAI
