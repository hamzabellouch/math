import OAI.NumberTheory.CubicMoment.Estimates.KernelScaling
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

/-!
# A concrete Fourier cutoff kernel

The fixed cutoff is a smooth bump, one near zero and supported in [-1,1].
Its inverse Fourier transform is a normalized Schwartz kernel. Mathlib
uses exp(2π i x ξ); this frequency variable differs by 2π from the
height variable in the manuscript.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform

namespace CubicFirstMoment

def frequencyBump : ContDiffBump (0 : ℝ) where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def frequencyCutoff : SchwartzMap ℝ ℂ :=
  (show HasCompactSupport (fun x : ℝ => (frequencyBump x : ℂ)) from
    frequencyBump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp frequencyBump.contDiff)

theorem frequencyCutoff_apply (x : ℝ) : frequencyCutoff x = (frequencyBump x : ℂ) := rfl

theorem frequencyCutoff_one {x : ℝ} (hx : |x| ≤ 1/2) : frequencyCutoff x = 1 := by
  rw [frequencyCutoff_apply, frequencyBump.one_of_mem_closedBall]
  · rfl
  · simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, frequencyBump] using hx

theorem frequencyCutoff_zero {x : ℝ} (hx : 1 ≤ |x|) : frequencyCutoff x = 0 := by
  rw [frequencyCutoff_apply, frequencyBump.zero_of_le_dist]
  · rfl
  · simpa only [Real.dist_eq, sub_zero, frequencyBump] using hx

def truncationKernel : SchwartzMap ℝ ℂ := 𝓕⁻ frequencyCutoff

/-- Inversion identifies the Fourier transform with the actual compact cutoff. -/
theorem fourier_truncationKernel : 𝓕 truncationKernel = frequencyCutoff :=
  fourier_fourierInv_eq frequencyCutoff

/-- Normalization follows from the value of the Fourier transform at zero. -/
theorem integral_truncationKernel : (∫ y, truncationKernel y) = 1 := by
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f 0) fourier_truncationKernel
  rw [SchwartzMap.fourier_coe, Real.fourier_eq'] at h
  simpa only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, frequencyCutoff_one (by norm_num : |(0 : ℝ)| ≤ 1/2)] using h

/-- The chosen Fourier kernel gives the uniform two-endpoint approximation. -/
theorem fourier_interval_error {T : ℝ} (hT : 0 < T) (a b s : ℝ) :
    ‖(intervalStep a b s : ℂ) - intervalSmoothing (scaledKernel truncationKernel T) a b s‖ ≤
      kernelMoment truncationKernel 1 / (1 + T*|s-a|)^2 +
        kernelMoment truncationKernel 1 / (1 + T*|s-b|)^2 :=
  scaled_schwartz_interval_error truncationKernel integral_truncationKernel hT a b s

end CubicFirstMoment

end

end OAI
