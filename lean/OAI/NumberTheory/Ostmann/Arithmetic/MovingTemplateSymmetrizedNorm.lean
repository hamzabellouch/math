import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateMaskedSymmetrization
import OAI.NumberTheory.Ostmann.Characters.MixedExternalMass

namespace OAI

/-! # The masked symmetrized energy is a nonnegative real number -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_norm_eq_re {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ j a, 0 ≤ ν j a) (N : ℕ) (u v a b center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hreal : ∀ s y x z, (F s y x z).im = 0)
    (hpos : ∀ s y x z, 0 ≤ (F s y x z).re) :
    ‖mixedExternalAverage ν N u v a b center F‖ =
      (mixedExternalAverage ν N u v a b center F).re := by
  have hi : (mixedExternalAverage ν N u v a b center F).im = 0 := by
    simp only [mixedExternalAverage_finite, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hreal, mul_zero,
      Finset.sum_const_zero]
  have hr : (((mixedExternalAverage ν N u v a b center F).re : ℝ) : ℂ) =
      mixedExternalAverage ν N u v a b center F := by
    apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im, hi]
  rw [← hr, Complex.norm_real, Real.norm_of_nonneg
    (mixedExternalAverage_re_nonneg ν hν N u v a b center F hpos)]
  rfl

theorem movingTemplateMaskedSymmetrizedEnergy_norm_eq_re
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ) (hν : ∀ j a, 0 ≤ ν j a)
    (active : MovingRegularSlot n r m → Bool) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ) :
    ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G n r m
      ν active greg Jleft Jright diagonal u v a b center‖ =
    (movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G n r m
      ν active greg Jleft Jright diagonal u v a b center).re := by
  unfold movingTemplateMaskedSymmetrizedEnergy
  apply mixedExternalAverage_norm_eq_re ν hν
  · intro s y x z
    have h := (movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ
      hφ Jleft Jright diagonal y x z).2
    rw [← h]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
  · intro s y x z
    have h := movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ
      hφ Jleft Jright diagonal y x z
    rw [← h.2]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (sq_nonneg _) h.1

end Ostmann

end OAI
