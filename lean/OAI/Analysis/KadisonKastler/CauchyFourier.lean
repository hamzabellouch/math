import OAI.Analysis.KadisonKastler.FourierLaplace
import Mathlib.Probability.Distributions.Cauchy

namespace OAI

/-! # The scalar Cauchy transform by Fourier inversion -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory
open scoped FourierTransform

noncomputable section

/-- In mathlib's Fourier convention the transform of the two-sided
exponential is exactly the normalized Cauchy density. -/
theorem fourier_laplaceKernel_cauchy {γ : NNReal} (hγ : 0 < γ) (ξ : ℝ) :
    𝓕 (laplaceKernel (2 * Real.pi * γ)) ξ = (cauchyPDFReal 0 γ ξ : ℂ) := by
  have ha : 0 < 2 * Real.pi * (γ : ℝ) := by positivity
  rw [fourier_laplaceKernel ha]
  apply congrArg (fun x : ℝ => (x : ℂ))
  rw [cauchyPDFReal_def]
  simp only [sub_zero]
  have hg : (γ : ℝ) ≠ 0 := ne_of_gt (show (0 : ℝ) < γ from hγ)
  have hd : ξ ^ 2 + (γ : ℝ) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The inverse transform of the Cauchy density is the two-sided
exponential. All integrability hypotheses follow from proved library
results and the explicit transform above. -/
theorem fourierInv_cauchyPDFReal {γ : NNReal} (hγ : 0 < γ) (t : ℝ) :
    𝓕⁻ (fun x : ℝ => (cauchyPDFReal 0 γ x : ℂ)) t =
      laplaceKernel (2 * Real.pi * γ) t := by
  have ha : 0 < 2 * Real.pi * (γ : ℝ) := by positivity
  have hF : (𝓕 (laplaceKernel (2 * Real.pi * γ)) : ℝ → ℂ) =
      fun x => (cauchyPDFReal 0 γ x : ℂ) :=
    funext (fourier_laplaceKernel_cauchy hγ)
  have hi : Integrable (𝓕 (laplaceKernel (2 * Real.pi * γ))) := by
    rw [hF]
    exact (integrable_cauchyPDFReal 0).ofReal
  have h := (integrable_laplaceKernel ha).fourierInv_fourier_eq hi
    ((continuous_laplaceKernel (2 * Real.pi * γ)).continuousAt (x := t))
  simpa only [hF] using h

end

end KadisonKastler

end OAI
