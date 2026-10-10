import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothHorizontalLimit
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothRightContour
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothActualZeroSum

namespace OAI

/-! # Passing the actual finite contour identity to infinite height -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology BigOperators Interval

theorem smooth_contour_limit (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 2 ≤ X) :
    I * (∫ y : ℝ, rightContourIntegrand χ X y) -
      I * (∫ y : ℝ, leftContourIntegrand χ X y) =
    -(2 * (Real.pi : ℂ) * I) *
      ((∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i) +
        smoothTrivialZeroTerm χ) := by
  obtain ⟨t, htpos, htlim, hzero, htop, hbot⟩ := smooth_horizontal_integrals_tendsto χ X hX
  have htneg : Tendsto (fun n => -t n) atTop atBot := tendsto_neg_atTop_atBot.comp htlim
  have hr := intervalIntegral_tendsto_integral
    (rightContourIntegrand_integrable χ X (by linarith)) htneg htlim
  have hl := intervalIntegral_tendsto_integral
    (leftContourIntegrand_integrable χ X (by linarith)) htneg htlim
  let f : ℂ → ℂ := fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z
  have hbd : Tendsto (fun n => rectangleBoundaryIntegral f (-(1 / 2)) 2 (-t n) (t n))
      atTop (𝓝 (I * (∫ y : ℝ, rightContourIntegrand χ X y) -
        I * (∫ y : ℝ, leftContourIntegrand χ X y))) := by
    have hh := ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)
    simpa [rectangleBoundaryIntegral, f, smoothHorizontalIntegral,
      rightContourIntegrand, leftContourIntegrand, primeMellinLine, primeVerticalWeight,
      leftContourLine, smoothContourWeight] using hh
  have hs := (smoothActualZeroSum_tendsto e χ X hX).comp htlim
  have hres : Tendsto (fun n => -(2 * (Real.pi : ℂ) * I) *
      ((∑ z ∈ criticalZerosUpTo χ (t n), (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z) +
        smoothTrivialZeroTerm χ)) atTop
      (𝓝 (-(2 * (Real.pi : ℂ) * I) *
        ((∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i) +
          smoothTrivialZeroTerm χ))) :=
    tendsto_const_nhds.mul (hs.add_const (smoothTrivialZeroTerm χ))
  apply tendsto_nhds_unique hbd
  apply hres.congr
  intro n
  exact (smoothContour_truncated χ X (by linarith) (t n) (htpos n) (hzero n)).symm

end Ostmann

end OAI
