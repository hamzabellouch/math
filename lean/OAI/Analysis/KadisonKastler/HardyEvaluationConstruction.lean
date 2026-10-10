import OAI.Analysis.KadisonKastler.HardyKernelRow
import OAI.Analysis.KadisonKastler.PublishedHardyEvaluation

namespace OAI

/-! # Constructed evaluation of positive-frequency multipliers

The normalized Cauchy kernel gives the Poisson compression. Its character
shifts and Fourier uniqueness prove invariance of the evaluation kernel.
Thus the compression is an algebra homomorphism on the multiplier algebra.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveFrequencyAlgebra_preserves
    (T : positiveFrequencyAlgebra (H := H)) (f : RegularCoreHilbert H)
    (hf : regularFrequencyProjection 0 f = f) :
    regularFrequencyProjection 0 (T.val f) = T.val f := by
  have h := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) T.property.2
  change regularFrequencyProjection 0 (T.val (regularFrequencyProjection 0 f)) =
    T.val (regularFrequencyProjection 0 f) at h
  simpa only [hf] using h

theorem hardyKernelRow_factor (z : ℂ) (hz : 0 < z.re)
    (T : positiveFrequencyAlgebra (H := H)) :
    ((hardyKernelRow z hz).comp T.val).comp (regularFrequencyProjection 0) =
      (((hardyKernelRow z hz).comp T.val).comp
        (hardyKernelInclusion z hz).toContinuousLinearMap).comp (hardyKernelRow z hz) := by
  apply hardyKernelInclusion_ext z hz
  intro s x
  change hardyKernelRow z hz (T.val (regularFrequencyProjection 0
      ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)))) =
    hardyKernelRow z hz (T.val (hardyKernelInclusion z hz
      (hardyKernelRow z hz ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)))))
  rcases le_total 0 s with hs | hs
  · have hp := regularCharacter_preserves_positive hs (hardyKernelInclusion z hz x)
      (hardyKernelInclusion_positive z hz x)
    have hc := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      A (hardyKernelInclusion z hz x)) (T.property.1 (2 * Real.pi * s)).eq
    change T.val ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (T.val (hardyKernelInclusion z hz x)) at hc
    have hTx := positiveFrequencyAlgebra_preserves T (hardyKernelInclusion z hz x)
      (hardyKernelInclusion_positive z hz x)
    have hr := hardyKernelRow_forward z hz hs (hardyKernelInclusion z hz x)
      (hardyKernelInclusion_positive z hz x)
    rw [hardyKernelRow_inclusion] at hr
    rw [hp, hc, hardyKernelRow_forward z hz hs _ hTx, hr]
    simp only [map_smul]
  · have hp := hardyKernelInclusion_backward_shift z hz (neg_nonneg.mpr hs) x
    simp only [neg_neg, Complex.ofReal_neg] at hp
    have hr : hardyKernelRow z hz ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) =
        Complex.exp (-z * (-s)) • x := by
      rw [← hardyKernelRow_projection z hz, hp, map_smul, hardyKernelRow_inclusion]
    rw [hp, hr]
    simp only [map_smul]

/-- Point evaluation constructed from the invariant Cauchy-kernel quotient. -/
def hardyEvaluationAt (z : ℂ) (hz : 0 < z.re) :
    positiveFrequencyAlgebra (H := H) →ₐ[ℂ] (H →L[ℂ] H) :=
  hardyCompressionAlgHom (positiveFrequencyAlgebra (H := H))
    (hardyKernelInclusion z hz).toContinuousLinearMap (hardyKernelRow z hz)
    (regularFrequencyProjection 0) (hardyKernelInclusion_adjoint_self z hz)
    (fun T => by
      apply ContinuousLinearMap.ext
      intro x
      exact positiveFrequencyAlgebra_preserves T (hardyKernelInclusion z hz x)
        (hardyKernelInclusion_positive z hz x))
    (hardyKernelRow_factor z hz)

@[simp] theorem hardyEvaluationAt_apply (z : ℂ) (hz : 0 < z.re)
    (T : positiveFrequencyAlgebra (H := H)) :
    hardyEvaluationAt z hz T = hardyKernelCompression z hz T.val := rfl

universe u

/-- Hardy multiplier evaluation by Poisson compression. -/
theorem publishedHardyMultiplierEvaluation : PublishedHardyMultiplierEvaluation.{u} := by
  intro H _ _ _ _ t r hr
  let z : ℂ := (2 * Real.pi * r : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I
  have hz : 0 < z.re := by
    change 0 < ((2 * Real.pi * r : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I : ℂ).re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  have hcenter : z.im / (2 * Real.pi) = t := by
    dsimp [z]
    simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    field_simp
  have hradius : z.re / (2 * Real.pi) = r := by
    dsimp [z]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    field_simp
  refine ⟨hardyEvaluationAt (H := H) z hz, ?_⟩
  intro F hF C hC T hT hr'
  rw [hardyEvaluationAt_apply]
  have he := hardyKernelCompression_eq_poisson hz F hF C hC T.val hT
  simpa only [hcenter, hradius] using he

end

end KadisonKastler

end OAI
