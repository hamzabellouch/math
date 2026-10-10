import OAI.Analysis.KadisonKastler.HardyReproducingKernel

namespace OAI

/-! # Boundary formula for the Hardy reproducing kernel -/

namespace KadisonKastler

open MeasureTheory FourierTransform

noncomputable section

def hardyCauchyFunction (z : ℂ) (s : ℝ) : ℂ :=
  (z - (2 * Real.pi * s : ℝ) * Complex.I)⁻¹

theorem hardyCauchyFunction_memLp {z : ℂ} (hz : 0 < z.re) :
    MemLp (hardyCauchyFunction z) 2 := by
  have h := (cauchyResolvent_memLp hz).comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  convert h using 1
  funext s
  dsimp [hardyCauchyFunction, Function.comp_def]
  congr 1
  push_cast
  ring

theorem fourierInv_positiveLaplaceKernel {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    𝓕⁻ (positiveLaplaceKernel z) s = hardyCauchyFunction z s := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_positiveLaplaceKernel hz]
  unfold hardyCauchyFunction
  congr 1
  push_cast
  ring

theorem hardyReproducingKernel_apply_ae {z : ℂ} (hz : 0 < z.re) :
    hardyReproducingKernel z hz =ᵐ[volume] hardyCauchyFunction z := by
  have he : 𝓕⁻ (positiveLaplaceKernel z) = hardyCauchyFunction z :=
    funext (fourierInv_positiveLaplaceKernel hz)
  have hF : MemLp (𝓕⁻ (positiveLaplaceKernel z)) 2 := by
    rw [he]
    exact hardyCauchyFunction_memLp hz
  have h := fourierInv_toLp_of_integrable (integrable_positiveLaplaceKernel hz)
    (positiveLaplaceKernel_memLp hz) hF
  change 𝓕⁻ ((positiveLaplaceKernel_memLp hz).toLp _) = _ at h
  change (𝓕⁻ ((positiveLaplaceKernel_memLp hz).toLp _) : RegularCoreHilbert ℂ) =ᵐ[volume] _
  rw [h]
  exact hF.coeFn_toLp.trans (Filter.Eventually.of_forall fun s => congrFun he s)

theorem hardyCauchyFunction_ne_zero {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    hardyCauchyFunction z s ≠ 0 := by
  apply inv_ne_zero
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at he
  exact hz.ne' he

theorem hardyCauchyFunction_norm_sq {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    ‖hardyCauchyFunction z s‖ ^ 2 =
      realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s /
        (2 * z.re) := by
  unfold hardyCauchyFunction
  rw [norm_inv, inv_pow, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one]
  unfold realPoissonKernel
  field_simp
  ring

end

end KadisonKastler

end OAI
