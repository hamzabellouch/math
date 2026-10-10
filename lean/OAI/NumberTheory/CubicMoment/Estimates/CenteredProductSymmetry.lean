import OAI.NumberTheory.CubicMoment.Estimates.CenteredProductMellin

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma centeredProductPolynomial_swap (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (u : ℝ) :
    centeredProductPolynomial A B α β ℓ u = centeredProductPolynomial B A β α ℓ u := by
  unfold centeredProductPolynomial
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm b a]
  ring

lemma centeredProductSmoothed_swap (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (W : ℝ → ℂ) (X u : ℝ) :
    centeredProductSmoothed A B α β ℓ W X u = centeredProductSmoothed B A β α ℓ W X u := by
  unfold centeredProductSmoothed
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm b a]
  ring

end CubicFirstMoment

end

end OAI
