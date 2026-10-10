import OAI.Analysis.KadisonKastler.HardyCauchyBoundary
import OAI.Analysis.KadisonKastler.HardyCompression
import OAI.Analysis.KadisonKastler.MeasurablePoisson

namespace OAI

/-! # Unit Hardy kernels and their Poisson compression -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def hardyUnitKernel (z : ℂ) (hz : 0 < z.re) : RegularCoreHilbert ℂ :=
  (Real.sqrt (2 * z.re) : ℂ) • hardyReproducingKernel z hz

theorem hardyUnitKernel_norm (z : ℂ) (hz : 0 < z.re) :
    ‖hardyUnitKernel z hz‖ = 1 := by
  have he : ‖hardyUnitKernel z hz‖ ^ 2 = 1 := by
    rw [hardyUnitKernel, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (by positivity), hardyReproducingKernel_norm_sq]
    field_simp
  nlinarith [norm_nonneg (hardyUnitKernel z hz)]

theorem hardyUnitKernel_density {z : ℂ} (hz : 0 < z.re) :
    (fun s => ‖hardyUnitKernel z hz s‖ ^ 2) =ᵐ[volume]
      realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (2 * z.re) : ℂ)
    (hardyReproducingKernel z hz), hardyReproducingKernel_apply_ae hz] with s hs hk
  change ‖((Real.sqrt (2 * z.re) : ℂ) • hardyReproducingKernel z hz) s‖ ^ 2 = _
  rw [hs, Pi.smul_apply, hk, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity), hardyCauchyFunction_norm_sq hz]
  field_simp

theorem hardyUnitKernel_positive (z : ℂ) (hz : 0 < z.re) :
    regularFrequencyProjection 0 (hardyUnitKernel z hz) = hardyUnitKernel z hz := by
  simp only [hardyUnitKernel, map_smul, hardyReproducingKernel_positive]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The isometric copy of the coefficient Hilbert space carried by a unit kernel. -/
def hardyKernelInclusion (z : ℂ) (hz : 0 < z.re) : H →ₗᵢ[ℂ] RegularCoreHilbert H where
  toLinearMap := (regularTensorVector (hardyUnitKernel z hz)).toLinearMap
  norm_map' x := by rw [ContinuousLinearMap.coe_coe, norm_regularTensorVector,
    hardyUnitKernel_norm, one_mul]

def hardyKernelCompression (z : ℂ) (hz : 0 < z.re)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) : H →L[ℂ] H :=
  (hardyKernelInclusion z hz).toContinuousLinearMap.adjoint.comp
    (T.comp (hardyKernelInclusion z hz).toContinuousLinearMap)

/-- Compressing a represented multiplication field gives its Poisson average. -/
theorem hardyKernelCompression_eq_poisson {z : ℂ} (hz : 0 < z.re)
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : RepresentsOperatorField volume F T) :
    hardyKernelCompression z hz T = measurablePoissonAverage F hF C hC
      (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) (div_pos hz (by positivity)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint
    (T (hardyKernelInclusion z hz x))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def,
    measurablePoissonAverage_apply]
  have hint : Integrable (fun s => realPoissonKernel (z.im / (2 * Real.pi))
      (z.re / (2 * Real.pi)) s • F s x) := by
    have hi := (integrable_realPoissonKernel (z.im / (2 * Real.pi)) (r := z.re / (2 * Real.pi))
      (div_pos hz (by positivity))).mul_const (C * ‖x‖)
    apply hi.mono' ((integrable_realPoissonKernel (z.im / (2 * Real.pi)) (r := z.re / (2 * Real.pi))
      (div_pos hz (by positivity))).aestronglyMeasurable.smul (hF x))
    filter_upwards [hC] with s hs
    change ‖realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s • F s x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg _ _
      (div_pos hz (by positivity)))]
    exact mul_le_mul_of_nonneg_left
      (((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
      (realPoissonKernel_nonneg _ _ (div_pos hz (by positivity)))
  change _ = (innerSL ℂ y) (∫ s, realPoissonKernel (z.im / (2 * Real.pi))
    (z.re / (2 * Real.pi)) s • F s x)
  rw [← (innerSL ℂ y).integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [hT (hardyKernelInclusion z hz x),
    regularTensorVector_apply_ae (hardyUnitKernel z hz) x,
    regularTensorVector_apply_ae (hardyUnitKernel z hz) y,
    hardyUnitKernel_density hz] with s hs hx hy hk
  change inner ℂ (regularTensorVector (hardyUnitKernel z hz) y s)
    (T (regularTensorVector (hardyUnitKernel z hz) x) s) = _
  change T (regularTensorVector (hardyUnitKernel z hz) x) s =
    F s (regularTensorVector (hardyUnitKernel z hz) x s) at hs
  rw [hs, hx, hy, map_smul, inner_smul_left, inner_smul_right]
  change star (hardyUnitKernel z hz s) *
    (hardyUnitKernel z hz s * inner ℂ y (F s x)) = _
  rw [← mul_assoc, RCLike.star_def, Complex.conj_mul']
  have hc : (‖hardyUnitKernel z hz s‖ : ℂ) ^ 2 =
      (realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s : ℂ) := by
    exact_mod_cast hk
  rw [hc]
  change _ = inner ℂ y (realPoissonKernel (z.im / (2 * Real.pi))
    (z.re / (2 * Real.pi)) s • F s x)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
  rfl

end

end KadisonKastler

end OAI
