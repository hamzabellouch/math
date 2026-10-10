import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import OAI.Analysis.PlanarPacking.Cardinal

namespace OAI

/-!
# Sharp Fourier certificates in the plane

The radial Schwartz certificate uses the Fourier kernel `exp (-2πi⟪x, ξ⟫)`
and the sharp triangular packing normalization.
-/

open MeasureTheory

namespace SharpPlanar




def Radial (f : Plane → ℝ) : Prop :=
  ∀ x y, ‖x‖ = ‖y‖ → f x = f y


noncomputable def fourier (f : Plane → ℝ) (ξ : Plane) : ℂ :=
  ∫ x : Plane, (f x : ℂ) *
    Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I)


def SharpCertificate (f : SchwartzMap Plane ℝ) : Prop :=
  Radial f ∧ fourier f 0 = 1 ∧ f 0 = 2 / Real.sqrt 3 ∧
    (∀ ξ, (fourier f ξ).im = 0 ∧ 0 ≤ (fourier f ξ).re) ∧
    (∀ x, 1 ≤ ‖x‖ → f x ≤ 0)

end SharpPlanar

end OAI
