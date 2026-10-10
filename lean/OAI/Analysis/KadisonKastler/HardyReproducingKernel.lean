import OAI.Analysis.KadisonKastler.HardyCauchyKernel
import OAI.Analysis.KadisonKastler.FrequencySupport
import OAI.Analysis.KadisonKastler.RegularCoreHilbertSum

namespace OAI

/-! # The concrete Hardy reproducing vectors

The inverse Fourier transform of a one-sided exponential belongs to the
positive-frequency space. Its normalization is computed, not assumed.
-/

namespace KadisonKastler

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

def hardyFrequencyKernel (z : ℂ) (hz : 0 < z.re) : RegularCoreHilbert ℂ :=
  (positiveLaplaceKernel_memLp hz).toLp (positiveLaplaceKernel z)

def hardyReproducingKernel (z : ℂ) (hz : 0 < z.re) : RegularCoreHilbert ℂ :=
  𝓕⁻ (hardyFrequencyKernel z hz)

theorem hardyFrequencyKernel_norm_sq (z : ℂ) (hz : 0 < z.re) :
    ‖hardyFrequencyKernel z hz‖ ^ 2 = 1 / (2 * z.re) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (hardyFrequencyKernel z hz) (hardyFrequencyKernel z hz))]
  change (∫ s : ℝ, (inner ℂ (hardyFrequencyKernel z hz s)
    (hardyFrequencyKernel z hz s)).re) = _
  have he : (fun s : ℝ => (inner ℂ (hardyFrequencyKernel z hz s)
      (hardyFrequencyKernel z hz s)).re) =ᵐ[volume]
      (Set.Ioi (0 : ℝ)).indicator (fun s => Real.exp ((-2 * z.re) * s)) := by
    filter_upwards [(positiveLaplaceKernel_memLp hz).coeFn_toLp] with s hs
    change (inner ℂ ((positiveLaplaceKernel_memLp hz).toLp (positiveLaplaceKernel z) s)
      ((positiveLaplaceKernel_memLp hz).toLp (positiveLaplaceKernel z) s)).re = _
    rw [hs]
    change RCLike.re (inner ℂ (positiveLaplaceKernel z s) (positiveLaplaceKernel z s)) = _
    rw [inner_self_eq_norm_sq]
    by_cases hp : 0 < s
    · simp only [positiveLaplaceKernel, Set.indicator, Set.mem_Ioi, ite_eq_left hp,
        Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
        Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero, ← Real.exp_nat_mul]
      congr 1
      ring
    · simp [positiveLaplaceKernel, hp]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioi,
    integral_exp_mul_Ioi (by linarith : -2 * z.re < 0)]
  simp

theorem hardyReproducingKernel_norm_sq (z : ℂ) (hz : 0 < z.re) :
    ‖hardyReproducingKernel z hz‖ ^ 2 = 1 / (2 * z.re) := by
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (hardyFrequencyKernel z hz)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map, hardyFrequencyKernel_norm_sq]

theorem hardyReproducingKernel_positive (z : ℂ) (hz : 0 < z.re) :
    regularFrequencyProjection 0 (hardyReproducingKernel z hz) =
      hardyReproducingKernel z hz := by
  apply (regularFrequencyProjection_fixed_iff 0 _).mpr
  change ∀ᵐ s : ℝ, s ≤ 0 / (2 * Real.pi) →
    (𝓕 (𝓕⁻ (hardyFrequencyKernel z hz)) : RegularCoreHilbert ℂ) s = 0
  rw [fourier_fourierInv_eq]
  filter_upwards [(positiveLaplaceKernel_memLp hz).coeFn_toLp] with s hs hle
  change (positiveLaplaceKernel_memLp hz).toLp (positiveLaplaceKernel z) s = 0
  rw [hs]
  simp only [zero_div] at hle
  exact Set.indicator_of_notMem (not_lt.mpr hle) _

end

end KadisonKastler

end OAI
