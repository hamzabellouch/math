import OAI.NumberTheory.CubicMoment.Estimates.ModelOverlapCounting

namespace OAI

/-! The elementary symmetric pair bound used to remove shared-prime
pairs from the quadratic cube model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma symmetric_pair_energy_le {α : Type*} (S : Finset α) (R : α → α → Prop)
    (hsym : ∀ a ∈ S, ∀ b ∈ S, R a b ↔ R b a) (w : α → ℝ) (M : ℝ)
    (hM : ∀ a ∈ S, ((S.filter (R a)).card:ℝ) ≤ M) :
    (∑ a ∈ S, ∑ b ∈ S, if R a b then w a*w b else 0) ≤ M*∑ a ∈ S, (w a)^2 := by
  have hrow : (∑ a ∈ S, ∑ b ∈ S, if R a b then (w a)^2 else 0) ≤
      M*∑ a ∈ S, (w a)^2 := by
    have he (a : α) : (∑ b ∈ S, if R a b then (w a)^2 else 0) =
        ((S.filter (R a)).card:ℝ)*(w a)^2 := by
      rw [← Finset.sum_filter]
      simp
    simp_rw [he]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_right (hM a ha) (sq_nonneg _))
  have hcol : (∑ a ∈ S, ∑ b ∈ S, if R a b then (w b)^2 else 0) ≤
      M*∑ a ∈ S, (w a)^2 := by
    rw [Finset.sum_comm]
    convert hrow using 1
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hsym b hb a ha]
  have htwice : 2*(∑ a ∈ S, ∑ b ∈ S, if R a b then w a*w b else 0) ≤
      (∑ a ∈ S, ∑ b ∈ S, if R a b then (w a)^2 else 0) +
      (∑ a ∈ S, ∑ b ∈ S, if R a b then (w b)^2 else 0) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    by_cases h : R a b
    · simp only [ite_eq_left h]
      nlinarith [sq_nonneg (w a-w b)]
    · simp only [ite_eq_right h,mul_zero,zero_add,le_refl]
  linarith

end CubicFirstMoment

end

end OAI
