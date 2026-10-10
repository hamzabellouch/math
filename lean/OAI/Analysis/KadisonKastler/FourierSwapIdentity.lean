import OAI.Analysis.KadisonKastler.L2FourierNaturality

namespace OAI

/-! # Fourier conjugacy from identities after swapping scalar variables -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem fourier_swap_identity (μ : Measure X)
    (A C : Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ) →L[ℂ] Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ))
    (B D : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ)
    (hA : ∀ F, l2ScalarSwap volume μ (A F) = B (l2ScalarSwap volume μ F))
    (hC : ∀ F, l2ScalarSwap volume μ (C F) = D (l2ScalarSwap volume μ F))
    (hBD : ∀ F, (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp (B F) =
      D ((Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp F))
    (F : Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ)) :
    𝓕 (A F) = C (𝓕 F) := by
  apply (l2ScalarSwap volume μ).injective
  rw [l2ScalarSwap_fourier, hA, hBD, ← l2ScalarSwap_fourier, hC]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem linearIsometryEquiv_conjugate_of_intertwines (e : E ≃ₗᵢ[ℂ] F)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (h : ∀ x, e (A x) = B (e x)) :
    A = e.symm.conjStarAlgEquiv B := by
  apply ContinuousLinearMap.ext
  intro x
  apply e.injective
  change e (A x) = e (e.symm (B (e x)))
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact h x

end

end KadisonKastler

end OAI
