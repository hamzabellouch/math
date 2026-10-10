import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform

theorem schwartz_fourier_at_zero {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    (𝓕 g) (0 : Ambient d) = ∫ x, g x := by
  change 𝓕 (g : Ambient d → ℂ) (0 : Ambient d) = _
  simp [Real.fourier_eq]

theorem schwartz_inverse_fourier_integral {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    (∫ x, (𝓕⁻ g) x) = g 0 := by
  rw [← schwartz_fourier_at_zero, FourierTransform.fourier_fourierInv_eq]

theorem inverse_fourier_mean_zero_of_zero_at_origin {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hg : g 0 = 0) : (∫ x, (𝓕⁻ g) x) = 0 :=
  (schwartz_inverse_fourier_integral g).trans hg

theorem inverse_fourier_mean_zero_of_support_away_origin {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hg : (0 : Ambient d) ∉ tsupport g) : (∫ x, (𝓕⁻ g) x) = 0 := by
  apply inverse_fourier_mean_zero_of_zero_at_origin
  by_contra h
  exact hg (subset_tsupport g h)

end

end RieszRectifiability

end OAI
