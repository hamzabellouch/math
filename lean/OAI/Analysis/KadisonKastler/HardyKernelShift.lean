import OAI.Analysis.KadisonKastler.HardyUnitKernel
import OAI.Analysis.KadisonKastler.FourierModulation
import OAI.Analysis.KadisonKastler.L2FourierNaturality
import OAI.Analysis.KadisonKastler.CoreFrequencyVectors

namespace OAI

/-! # Character shifts of the reproducing kernel

A backward shift followed by the positive-frequency projection is scalar on
an exponential kernel. Forward shifts preserve the positive-frequency space.
-/

namespace KadisonKastler

open MeasureTheory FourierTransform

noncomputable section

theorem positiveLaplace_shift_cut (z : ℂ) (hz : 0 < z.re) {b : ℝ} (hb : 0 ≤ b) :
    regularIndicatorProjection (Set.Ioi 0) measurableSet_Ioi
      (regularTranslateApply b (hardyFrequencyKernel z hz)) =
        Complex.exp (-z * b) • hardyFrequencyKernel z hz := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae (Set.Ioi 0) measurableSet_Ioi
      (regularTranslateApply b (hardyFrequencyKernel z hz)),
    regularTranslateApply_ae b (hardyFrequencyKernel z hz),
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae_eq_comp
      (positiveLaplaceKernel_memLp hz).coeFn_toLp,
    (positiveLaplaceKernel_memLp hz).coeFn_toLp,
    Lp.coeFn_smul (Complex.exp (-z * b)) (hardyFrequencyKernel z hz)]
    with s hp ht hshift hs hsmul
  rw [hp, hsmul, Pi.smul_apply]
  by_cases hpos : 0 < s
  · simp only [Set.indicator, Set.mem_Ioi, ite_eq_left hpos]
    rw [ht]
    change (hardyFrequencyKernel z hz) (s + b) =
      Complex.exp (-z * b) • (hardyFrequencyKernel z hz) s
    change hardyFrequencyKernel z hz (s + b) = positiveLaplaceKernel z (s + b) at hshift
    rw [hshift, show (hardyFrequencyKernel z hz) s = positiveLaplaceKernel z s from hs]
    have hsb : 0 < s + b := by linarith
    simp only [positiveLaplaceKernel, Set.indicator, Set.mem_Ioi, ite_eq_left hpos,
      ite_eq_left hsb, smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [Set.indicator, Set.mem_Ioi, ite_eq_right hpos]
    change 0 = Complex.exp (-z * b) • (hardyFrequencyKernel z hz) s
    rw [show (hardyFrequencyKernel z hz) s = positiveLaplaceKernel z s from hs]
    simp [positiveLaplaceKernel, hpos]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_frequencyProjection_zero (f : RegularCoreHilbert H) :
    𝓕 (regularFrequencyProjection 0 f) =
      regularIndicatorProjection (Set.Ioi 0) measurableSet_Ioi (𝓕 f) := by
  change (Lp.fourierTransformₗᵢ ℝ H)
    ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
      (regularIndicatorProjection (Set.Ioi (0 / (2 * Real.pi))) measurableSet_Ioi) f) = _
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]
  simp only [zero_div]
  rfl

theorem regularCharacter_preserves_positive {b : ℝ} (hb : 0 ≤ b)
    (f : RegularCoreHilbert H) (hf : regularFrequencyProjection 0 f = f) :
    regularFrequencyProjection 0
      ((regularCharacterUnitary (H := H) (2 * Real.pi * b) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * b) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f := by
  apply (regularFrequencyProjection_fixed_iff 0 _).mpr
  rw [fourier_regularCharacterUnitary]
  have hs := (regularFrequencyProjection_fixed_iff 0 f).mp hf
  filter_upwards [regularTranslateApply_ae (-b) (𝓕 f),
    (measurePreserving_add_right volume (-b)).quasiMeasurePreserving.ae hs]
      with s ht hsupport hle
  rw [ht]
  apply hsupport
  simp only [zero_div] at hle ⊢
  linarith

/-- Projected negative character shifts act diagonally on a reproducing kernel. -/
theorem hardyReproducingKernel_backward_shift (z : ℂ) (hz : 0 < z.re)
    {b : ℝ} (hb : 0 ≤ b) :
    regularFrequencyProjection 0
      ((regularCharacterUnitary (H := ℂ) (2 * Real.pi * (-b)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (hardyReproducingKernel z hz)) =
        Complex.exp (-z * b) • hardyReproducingKernel z hz := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (regularFrequencyProjection 0
    ((regularCharacterUnitary (H := ℂ) (2 * Real.pi * (-b)) :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (hardyReproducingKernel z hz))) =
        𝓕 (Complex.exp (-z * b) • hardyReproducingKernel z hz)
  rw [fourier_frequencyProjection_zero, fourier_regularCharacterUnitary, fourier_smul]
  simp only [hardyReproducingKernel, fourier_fourierInv_eq, neg_neg]
  exact positiveLaplace_shift_cut z hz hb

end

end KadisonKastler

end OAI
