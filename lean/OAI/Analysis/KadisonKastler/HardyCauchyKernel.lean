import OAI.Analysis.KadisonKastler.FourierIntegralL2
import OAI.Analysis.KadisonKastler.PoissonKernelContinuity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! # The one-sided exponential and its Cauchy transform

These are the concrete kernels for evaluating a positive-frequency multiplier.
All transforms here are computed from the half-line exponential integral.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The exponentially decreasing kernel on the positive frequency half-line. -/
def positiveLaplaceKernel (z : ℂ) : ℝ → ℂ :=
  Set.Ioi (0 : ℝ) |>.indicator (fun s => Complex.exp (-z * s))

theorem integrable_positiveLaplaceKernel {z : ℂ} (hz : 0 < z.re) :
    Integrable (positiveLaplaceKernel z) := by
  exact (integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0).integrable_indicator
    measurableSet_Ioi

theorem positiveLaplaceKernel_memLp {z : ℂ} (hz : 0 < z.re) :
    MemLp (positiveLaplaceKernel z) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (integrable_positiveLaplaceKernel hz).aestronglyMeasurable).mpr
  have hi := (integrableOn_exp_mul_Ioi (a := -2 * z.re) (by linarith) 0).integrable_indicator
    measurableSet_Ioi
  apply hi.congr
  filter_upwards [] with s
  by_cases hs : 0 < s
  · simp only [positiveLaplaceKernel, Set.indicator, Set.mem_Ioi, ite_eq_left hs,
      Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, ← Real.exp_nat_mul]
    congr 1
    ring
  · simp [positiveLaplaceKernel, hs]

theorem fourier_positiveLaplaceKernel {z : ℂ} (hz : 0 < z.re) (ξ : ℝ) :
    𝓕 (positiveLaplaceKernel z) ξ = (z + (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun s : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * s * ξ) : ℂ) * Complex.I) • positiveLaplaceKernel z s) =
      (Set.Ioi (0 : ℝ)).indicator
        (fun s => Complex.exp ((-z - (2 * Real.pi * ξ : ℝ) * Complex.I) * s)) := by
    funext s
    by_cases hs : 0 < s
    · simp only [positiveLaplaceKernel, Set.indicator, Set.mem_Ioi, ite_eq_left hs,
        smul_eq_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [positiveLaplaceKernel, hs]
  rw [he, integral_indicator measurableSet_Ioi]
  rw [integral_exp_mul_complex_Ioi (by simpa using (neg_lt_zero.mpr hz))]
  have hn : -z - (2 * Real.pi * ξ : ℝ) * Complex.I =
      -(z + (2 * Real.pi * ξ : ℝ) * Complex.I) := by ring
  rw [hn]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, one_div]

/-- The squared norm of the Cauchy kernel is a multiple of a probability
Poisson kernel. This also supplies its square integrability. -/
theorem cauchyResolvent_norm_sq {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    ‖(z + (2 * Real.pi * s : ℝ) * Complex.I)⁻¹‖ ^ 2 =
      realPoissonKernel (-z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s /
        (2 * z.re) := by
  rw [norm_inv, inv_pow, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one]
  unfold realPoissonKernel
  field_simp
  ring

theorem cauchyResolvent_memLp {z : ℂ} (hz : 0 < z.re) :
    MemLp (fun s : ℝ => (z + (2 * Real.pi * s : ℝ) * Complex.I)⁻¹) 2 := by
  have hn (s : ℝ) : z + (2 * Real.pi * s : ℝ) * Complex.I ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at h'
    exact hz.ne' h'
  have hc : Continuous (fun s : ℝ => (z + (2 * Real.pi * s : ℝ) * Complex.I)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · exact hn
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact ((integrable_realPoissonKernel (-z.im / (2 * Real.pi))
    (div_pos hz (by positivity))).div_const (2 * z.re)).congr
      (Filter.Eventually.of_forall fun s => (cauchyResolvent_norm_sq hz s).symm)

/-- The integral computation also holds for the actual unitary `L²` transform. -/
theorem fourier_positiveLaplaceKernel_toLp {z : ℂ} (hz : 0 < z.re) :
    𝓕 ((positiveLaplaceKernel_memLp hz).toLp (positiveLaplaceKernel z)) =
      (cauchyResolvent_memLp hz).toLp
        (fun s : ℝ => (z + (2 * Real.pi * s : ℝ) * Complex.I)⁻¹) := by
  have he : 𝓕 (positiveLaplaceKernel z) =
      (fun s : ℝ => (z + (2 * Real.pi * s : ℝ) * Complex.I)⁻¹) :=
    funext (fourier_positiveLaplaceKernel hz)
  have hF : MemLp (𝓕 (positiveLaplaceKernel z)) 2 := by
    rw [he]
    exact cauchyResolvent_memLp hz
  rw [fourier_toLp_of_integrable (integrable_positiveLaplaceKernel hz)
    (positiveLaplaceKernel_memLp hz) hF]
  apply Lp.ext
  filter_upwards [hF.coeFn_toLp, (cauchyResolvent_memLp hz).coeFn_toLp] with s h₁ h₂
  rw [h₁, h₂, he]

end

end KadisonKastler

end OAI
