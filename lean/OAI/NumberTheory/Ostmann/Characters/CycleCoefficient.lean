import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Pi

namespace OAI

/-!
# A coefficient bound for a cycle

Once all but one Mellin index are fixed, the cycle relation determines
the remaining index. This is the final finite-sum estimate in Section 6.
-/

namespace Ostmann

open scoped BigOperators

/-- A cycle relation costs one supremum and the masses of the remaining indices. -/
theorem cycleCoefficient_sum_le {G I : Type*} [CommGroup G] [Fintype G] [Fintype I]
    [DecidableEq G] [DecidableEq I]
    (b₀ : G → ℝ) (b : I → G → ℝ) (S : ℝ)
    (h₀ : ∀ a, b₀ a ≤ S) (hb : ∀ i a, 0 ≤ b i a) :
    (∑ f : I → G, ∑ a : G,
      if a * (∏ i, f i) = 1 then b₀ a * (∏ i, b i (f i)) else 0) ≤
        S * ∏ i, ∑ a : G, b i a := by
  classical
  have hinner (f : I → G) :
      (∑ a : G, if a * (∏ i, f i) = 1 then b₀ a * (∏ i, b i (f i)) else 0) =
        b₀ (∏ i, f i)⁻¹ * (∏ i, b i (f i)) := by
    simp only [mul_eq_one_iff_eq_inv]
    simp
  simp_rw [hinner]
  calc
    _ ≤ ∑ f : I → G, S * (∏ i, b i (f i)) := by
      apply Finset.sum_le_sum
      intro f _
      exact mul_le_mul_of_nonneg_right (h₀ _) (Finset.prod_nonneg (fun i _ => hb i _))
    _ = S * ∏ i, ∑ a : G, b i a := by
      rw [← Finset.mul_sum, Fintype.prod_sum]

end Ostmann

end OAI
