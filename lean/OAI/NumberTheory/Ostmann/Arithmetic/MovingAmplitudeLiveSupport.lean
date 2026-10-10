import OAI.NumberTheory.Ostmann.Construction.SmoothGiantLiveSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitude

namespace OAI

/-! # The exact full giant amplitude on its nonzero finite support -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplatePrimeAmplitude_live {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (P : Finset ℕ) (H : ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      P (smoothGiantPrior P φ H) ν greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      (smoothGiantLivePrimes P φ H) (smoothGiantPrior (smoothGiantLivePrimes P φ H) φ H)
      ν greg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  exact smoothGiantPrior_double_sum_live P φ H (fun XL XR =>
    ∑ s : transferFrequencyRange (V n),
      ∑ y : MovingRegularSlot n r m → σ, ((∏ i, ν i (y i) : ℝ) : ℂ) *
        (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m
          s.val y XL XR *
          movingTaggedTransform
            (Sum.elim (fun b : Bool => if b then XL else XR) (value ∘ y))
            (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val))

end Ostmann

end OAI
