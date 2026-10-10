import OAI.NumberTheory.Ostmann.Characters.MixedExternalMass

namespace OAI

/-! # Comparing energies on the support of the original external law -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_square_mono_support {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ j a, 0 ≤ ν j a) (N : ℕ) (u v a b center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ s y x z, 0 ≤ W s y x z)
    (hFH : ∀ y, (∏ j, ν j (y j)) ≠ 0 → ∀ s x z, ‖F s y x z‖ ≤ ‖H s y x z‖) :
    (mixedExternalAverage ν N u v a b center
      (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤
    (mixedExternalAverage ν N u v a b center
      (fun s y x z => (‖H s y x z‖ ^ 2 : ℂ) * W s y x z)).re := by
  simp only [mixedExternalAverage_finite, ← Complex.ofReal_pow, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : (∏ j, ν j (x.2.1 j)) = 0
  · simp only [mixedExternalPrior, hx, zero_mul, le_refl]
  · apply mul_le_mul_of_nonneg_left _ (mixedExternalPrior_nonneg ν hν N u v a b center x)
    apply mul_le_mul_of_nonneg_right _ (hW _ _ _ _)
    exact pow_le_pow_left₀ (norm_nonneg _) (hFH x.2.1 hx _ _ _) 2

end Ostmann

end OAI
