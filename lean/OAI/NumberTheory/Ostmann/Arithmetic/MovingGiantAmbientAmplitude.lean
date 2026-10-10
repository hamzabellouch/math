import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitude
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantAmbientPrior

namespace OAI

/-! # Restricting the giant average to its full smooth cell -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrior_ambient_complex_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hsub : smoothGiantPrimeRange G ⊆ P) (f : P → ℂ) :
    (∑ p : P, (smoothGiantPrior P φ G p : ℂ) * f p) =
      ∑ q : smoothGiantPrimeRange G,
        (smoothGiantPrior (smoothGiantPrimeRange G) φ G q : ℂ) * f ⟨q, hsub q.property⟩ := by
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using smoothGiantPrior_ambient_mean P hP φ G hout hsub (fun p => (f p).re)
  · simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using smoothGiantPrior_ambient_mean P hP φ G hout hsub (fun p => (f p).im)

theorem movingTemplatePrimeAmplitude_giant_ambient {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ψ : ℝ → ℝ) (H : ℝ) (hout : ∀ x, 1 ≤ |x| → ψ x = 0)
    (hsub : smoothGiantPrimeRange H ⊆ P)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      P (smoothGiantPrior P ψ H) ν greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      (smoothGiantPrimeRange H) (smoothGiantPrior (smoothGiantPrimeRange H) ψ H)
      ν greg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  rw [smoothGiantPrior_ambient_complex_mean P hP ψ H hout hsub]
  apply Finset.sum_congr rfl
  intro XL _
  congr 1
  rw [smoothGiantPrior_ambient_complex_mean P hP ψ H hout hsub]

end Ostmann

end OAI
