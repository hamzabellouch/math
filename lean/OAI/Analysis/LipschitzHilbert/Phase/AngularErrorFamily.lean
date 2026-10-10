import OAI.Analysis.LipschitzHilbert.Phase.AngularErrorConvolution
import OAI.Analysis.LipschitzHilbert.Fourier.ActualErrorConvolution
import OAI.Analysis.LipschitzHilbert.Fourier.ErrorLineConcentration

namespace OAI

/-! Actual dyadic angular-error coefficients and their constructed line
majorant. The assumptions are packet and multiplier bounds, not an error
concentration or convolution estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

structure AngularErrorFamily (N : ℕ) (κ : Type) (ι : Fin N → Type)
    [Fintype κ] [∀ j, Fintype (ι j)] where
  baseX : ℝ
  baseZ : ℝ
  topLength : ℝ
  width : ℝ
  angleBase : ℝ
  referenceSlope : ℝ
  smallRatio : ℝ
  wideConstant : ℝ
  exponent : ℕ
  wideExponent : ℕ
  packetBound : ℝ
  multiplierBound : ℝ
  multiplierLip : ℝ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  angleBase_pos : 0 < angleBase
  smallRatio_pos : 0 < smallRatio
  smallRatio_le : smallRatio ≤ 1
  wideConstant_le : wideConstant ≤ smallRatio*(2:ℝ)^wideExponent
  wideRatio_ge : 1 ≤ wideConstant*((2:ℝ)^exponent)^4
  packetBound_nonneg : 0 ≤ packetBound
  multiplierBound_nonneg : 0 ≤ multiplierBound
  multiplierLip_nonneg : 0 ≤ multiplierLip
  direction : ℝ × ℝ → ℝ
  direction_measurable : Measurable direction
  test : ℝ × ℝ → EuclideanSpace ℂ κ
  test_measurable : Measurable test
  test_bound : ∀ z, ‖test z‖ ≤ 1
  site : ∀ j, ι j → ℤ × ℤ
  site_injective : ∀ j, Function.Injective (site j)
  multiplier : ∀ j, ι j → κ → ℝ → ℂ
  multiplier_measurable : ∀ j i k, Measurable (multiplier j i k)
  multiplier_bounded : ∀ j i k s, ‖multiplier j i k s‖ ≤ multiplierBound
  multiplier_near : ∀ j i k s, |s-referenceSlope| ≤ smallRatio*(angleBase*(2:ℝ)^j.val) →
    ‖multiplier j i k s-multiplier j i k referenceSlope‖ ≤
      multiplierLip*(|s-referenceSlope|/(angleBase*(2:ℝ)^j.val))
  multiplier_far : ∀ j i k s,
    (wideConstant*((2:ℝ)^exponent)^4)*(angleBase*(2:ℝ)^j.val) < |s-referenceSlope| →
    multiplier j i k s = 0
  wave : ∀ j, ι j → κ → ℝ × ℝ → ℂ
  wave_measurable : ∀ j i k, Measurable (wave j i k)
  wave_bound : ∀ j i k z, ‖wave j i k z‖ ≤ packetBound *
    tileEnvelope (baseX+(topLength/(2:ℝ)^j.val)*(site j i).1)
      (baseZ+width*(site j i).2) (topLength/(2:ℝ)^j.val) width 6 z

namespace AngularErrorFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def length (P : AngularErrorFamily N κ ι) (j : Fin N) : ℝ := P.topLength/(2:ℝ)^j.val
def angleStep (P : AngularErrorFamily N κ ι) (j : Fin N) : ℝ := P.angleBase*(2:ℝ)^j.val

def coefficient (P : AngularErrorFamily N κ ι) (j : Fin N) (i : ι j) : EuclideanSpace ℂ κ :=
  analyzingCoefficient volume (fun _ : ι j => P.length j * P.width)
    (angularErrorWave (P.multiplier j) (P.wave j) P.direction P.referenceSlope (P.angleStep j)) P.test i

def scaleError (P : AngularErrorFamily N κ ι) (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ i, ‖P.coefficient j i‖ * tileEnvelope
    (P.baseX+P.length j*(P.site j i).1) (P.baseZ+P.width*(P.site j i).2)
      (P.length j) P.width 6 (x,y)

def error (P : AngularErrorFamily N κ ι) (y x : ℝ) : ℝ := ∑ j, P.scaleError j y x

def sourceAmplitude (P : AngularErrorFamily N κ ι) : ℝ :=
  (64*(4*Real.pi)^2)*(P.packetBound*(2*P.multiplierBound+P.multiplierLip))

theorem sourceAmplitude_nonneg (P : AngularErrorFamily N κ ι) : 0 ≤ P.sourceAmplitude := by
  have := P.packetBound_nonneg
  have := P.multiplierBound_nonneg
  have := P.multiplierLip_nonneg
  unfold sourceAmplitude
  positivity

def sources (P : AngularErrorFamily N κ ι) (y : ℝ) : LineErrorSources N :=
  actualErrorSources P.wideExponent P.exponent P.direction P.direction_measurable
    P.referenceSlope P.angleBase P.smallRatio P.wideConstant P.sourceAmplitude P.topLength P.width y
    P.angleBase_pos P.smallRatio_pos P.sourceAmplitude_nonneg P.wideConstant_le P.topLength_pos P.width_pos

theorem scaleError_le (P : AngularErrorFamily N κ ι) (j : Fin N) (y x : ℝ) :
    P.scaleError j y x ≤ (P.sources y).term j x := by
  have h := angular_error_coefficient_convolution (P.site j) (P.site_injective j)
    P.baseX P.baseZ (P.length j) P.width
    (div_pos P.topLength_pos (pow_pos (by norm_num) _)) P.width_pos
    (P.multiplier j) (P.wave j) P.direction P.direction_measurable
    P.referenceSlope (P.angleStep j) P.smallRatio
    (P.wideConstant*((2:ℝ)^P.exponent)^4) P.packetBound P.multiplierBound P.multiplierLip
    (mul_pos P.angleBase_pos (pow_pos (by norm_num) _)) P.smallRatio_pos P.smallRatio_le P.wideRatio_ge
    P.packetBound_nonneg P.multiplierBound_nonneg P.multiplierLip_nonneg
    (P.multiplier_measurable j) (P.wave_measurable j) (P.multiplier_bounded j)
    (P.multiplier_near j) (P.multiplier_far j) (P.wave_bound j)
    P.test P.test_measurable P.test_bound (x,y)
  change P.scaleError j y x ≤ _ at h
  apply h.trans_eq
  rw [sources, actualErrorSources_term_eq]
  rw [← planarPositiveConvolution_const_mul]
  congr 1
  funext z
  unfold sourceAmplitude angleStep
  ring

theorem error_le_majorant (P : AngularErrorFamily N κ ι) (y x : ℝ) :
    P.error y x ≤ (P.sources y).majorant x :=
  Finset.sum_le_sum (fun j _ => P.scaleError_le j y x)

end AngularErrorFamily
end LipschitzHilbert

end

end OAI
