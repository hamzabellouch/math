import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSliceFourierSupport

namespace OAI

/-! The manuscript uses angular frequencies in `exp(iηy)`, whereas
mathlib's Fourier transform uses `exp(-2πi xξ)`. These definitions and
identities keep the conversion explicit. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

def planarAngularFourier (f : ℝ × ℝ → ℂ) (frequency : ℝ × ℝ) : ℂ :=
  planarFourier f (frequency.1 / (2 * Real.pi), frequency.2 / (2 * Real.pi))

def angularFourier (g : ℝ → ℂ) (ω : ℝ) : ℂ := 𝓕 g (ω / (2 * Real.pi))

theorem planarAngularFourier_eq_integral (f : ℝ × ℝ → ℂ) (frequency : ℝ × ℝ) :
    planarAngularFourier f frequency = ∫ z : ℝ × ℝ,
      Complex.exp (-(Complex.I * (z.1 * frequency.1 + z.2 * frequency.2))) * f z
        ∂volume.prod volume := by
  unfold planarAngularFourier planarFourier
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem planarSchwartzSlice_angularFourier_eq_zero
    (f : SchwartzMap (ℝ × ℝ) ℂ) (b s ω : ℝ)
    (hfiber : ∀ η, planarAngularFourier f (ω - s * η, η) = 0) :
    angularFourier (planarSchwartzSlice f b s) ω = 0 := by
  apply planarSchwartzSlice_fourier_eq_zero
  intro η
  have h := hfiber ((2 * Real.pi) * η)
  have hξ : (ω - s * ((2 * Real.pi) * η)) / (2 * Real.pi) =
      ω / (2 * Real.pi) - s * η := by field_simp [Real.pi_ne_zero]
  have hη : (2 * Real.pi * η) / (2 * Real.pi) = η := by field_simp [Real.pi_ne_zero]
  simpa only [planarAngularFourier, hξ, hη] using h

end LipschitzHilbert

end

end OAI
