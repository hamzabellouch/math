import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarBarrier
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! Quantitative inward inequalities for the forbidden-side normalized slope. -/

namespace DefocusingNLS

theorem spectralRiccati_upper (z t e eps : ℝ) (ht : 1≤t) (heps : 0<eps)
    (hz : 1+eps≤z) (he : e≤eps/2*Real.sqrt t) :
    Real.sqrt t*(1-z^2)-z/(2*t)+e≤ -eps/2 := by
  have ht0 : 0<t := by linarith
  have hs : 1≤Real.sqrt t := by
    have hh := Real.sq_sqrt ht0.le
    have hn := Real.sqrt_nonneg t
    nlinarith
  have hz0 : 0≤z := by linarith
  have hsq : 1-z^2≤ -eps := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg t)
  have hdiv : 0≤z/(2*t) := by positivity
  have hlow := mul_le_mul_of_nonneg_left hs heps.le
  nlinarith

theorem spectralRiccati_lower (z t e eps : ℝ) (ht : 1≤t) (heps : 0<eps)
    (hz0 : 0≤z) (hz : z≤1-eps) (he : 0≤e) (hsmall : 1≤eps*t) :
    eps/2≤Real.sqrt t*(1-z^2)-z/(2*t)+e := by
  have ht0 : 0<t := by linarith
  have hs : 1≤Real.sqrt t := by
    have hh := Real.sq_sqrt ht0.le
    have hn := Real.sqrt_nonneg t
    nlinarith
  have hsq : eps≤1-z^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg t)
  have hdiv : z/(2*t)≤eps/2 := (div_le_iff₀ (by positivity : 0<2*t)).mpr (by nlinarith)
  have hlow := mul_le_mul_of_nonneg_left hs heps.le
  nlinarith

end DefocusingNLS

end OAI
