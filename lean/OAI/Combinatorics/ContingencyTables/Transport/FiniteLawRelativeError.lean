import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments

namespace OAI

/-! # Passing deterministic relative error through a finite law -/

namespace ContingencyTables.FiniteLawMoments

open ResidualMixture
open scoped BigOperators

variable {X : Type*} [Fintype X]

lemma expectation_relative_error (p : RationalLaw X) (f g : X → ℝ) (delta : ℝ)
    (herror : ∀ x,|g x-f x| ≤ delta*f x) :
    |expectation p g-expectation p f| ≤ delta*expectation p f := by
  have he : expectation p g-expectation p f=∑ x,(p.mass x:ℝ)*(g x-f x) := by
    unfold expectation
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  calc
    _ ≤ ∑ x,|(p.mass x:ℝ)*(g x-f x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x,(p.mass x:ℝ)*(delta*f x) := by
      apply Finset.sum_le_sum
      intro x _
      have hp : (0:ℝ) ≤ p.mass x := by exact_mod_cast p.nonnegative x
      rw [abs_mul,abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left (herror x) hp
    _ = _ := by
      unfold expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end ContingencyTables.FiniteLawMoments

end OAI
