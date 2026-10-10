import OAI.NumberTheory.TwoPoint.Bounds.PositiveWordProbability

namespace OAI

/-! A bounded function pays the probability of its actual nonzero support. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem FiniteLaw.average_abs_le_support {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (f : A → ℝ) (E : A → Prop) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C) (hsupport : ∀ x, f x ≠ 0 → E x) :
    μ.average (fun x => |f x|) ≤ C * μ.probability E := by
  calc
    _ ≤ μ.average (fun x => (if E x then 1 else 0) * C) := by
      apply μ.average_mono
      intro x
      by_cases hx : E x
      · simpa only [ite_eq_left hx, one_mul] using hf x
      · have hz : f x = 0 := by by_contra hn; exact hx (hsupport x hn)
        simp only [hz, abs_zero, ite_eq_right hx, zero_mul, le_refl]
    _ = C * μ.probability E := by rw [μ.average_mul_const]; exact mul_comm _ _

end TwoPointCorrelations

end OAI
