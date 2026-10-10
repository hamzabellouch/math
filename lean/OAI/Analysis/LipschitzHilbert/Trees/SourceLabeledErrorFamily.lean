import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorConvolution
import OAI.Analysis.LipschitzHilbert.Fourier.ErrorLineConcentration

namespace OAI

/-! Dyadic angular errors on translated lattices with bounded local
multiplicity of slope labels. The common source is counted before integration. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

structure LabeledAngularErrorFamily (N : ℕ) (Λ : Fin N → Type) (κ : Type)
    (ι : ∀ j, Λ j → Type) [∀ j, Fintype (Λ j)] [Fintype κ]
    [∀ j b, Fintype (ι j b)] where
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
  radius : ℝ
  radiusBound : ℕ
  multiplicity : ℕ
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
  radius_le : radius ≤ radiusBound
  direction : ℝ×ℝ → ℝ
  direction_measurable : Measurable direction
  test : ℝ×ℝ → EuclideanSpace ℂ κ
  test_measurable : Measurable test
  test_bound : ∀ z, ‖test z‖ ≤ 1
  originX : ∀ j, Λ j → ℝ
  originY : ∀ j, Λ j → ℝ
  slope : ∀ j, Λ j → ℝ
  localMultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (slope j)
    (angleBase*(2:ℝ)^j.val) multiplicity
  site : ∀ j b, ι j b → ℤ×ℤ
  site_injective : ∀ j b, Function.Injective (site j b)
  multiplier : ∀ j, Λ j → κ → ℝ → ℂ
  multiplier_measurable : ∀ j b k, Measurable (multiplier j b k)
  multiplier_bounded : ∀ j b k s, ‖multiplier j b k s‖ ≤ multiplierBound
  multiplier_support : ∀ j b k s, multiplier j b k s ≠ 0 →
    |s-slope j b| ≤ radius*(angleBase*(2:ℝ)^j.val)
  multiplier_near : ∀ j b k s, |s-referenceSlope| ≤ smallRatio*(angleBase*(2:ℝ)^j.val) →
    ‖multiplier j b k s-multiplier j b k referenceSlope‖ ≤
      multiplierLip*(|s-referenceSlope|/(angleBase*(2:ℝ)^j.val))
  multiplier_far : ∀ j b k s,
    (wideConstant*((2:ℝ)^exponent)^4)*(angleBase*(2:ℝ)^j.val) < |s-referenceSlope| →
      multiplier j b k s = 0
  wave : ∀ j b, ι j b → κ → ℝ×ℝ → ℂ
  wave_measurable : ∀ j b i k, Measurable (wave j b i k)
  wave_bound : ∀ j b i k z, ‖wave j b i k z‖ ≤ packetBound*
    tileEnvelope (originX j b+(topLength/(2:ℝ)^j.val)*(site j b i).1)
      (originY j b+width*(site j b i).2) (topLength/(2:ℝ)^j.val) width 6 z

namespace LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

def length (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) : ℝ :=
  P.topLength/(2:ℝ)^j.val

def angleStep (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) : ℝ :=
  P.angleBase*(2:ℝ)^j.val

def coefficient (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) (b : Λ j)
    (i : ι j b) : EuclideanSpace ℂ κ :=
  analyzingCoefficient volume (fun _ : ι j b => P.length j*P.width)
    (angularErrorWave (fun _ k => P.multiplier j b k) (P.wave j b)
      P.direction P.referenceSlope (P.angleStep j)) P.test i

def scaleError (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ b, ∑ i, ‖P.coefficient j b i‖*tileEnvelope
    (P.originX j b+P.length j*(P.site j b i).1)
    (P.originY j b+P.width*(P.site j b i).2) (P.length j) P.width 6 (x,y)

def error (P : LabeledAngularErrorFamily N Λ κ ι) (y x : ℝ) : ℝ :=
  ∑ j, P.scaleError j y x

def sourceAmplitude (P : LabeledAngularErrorFamily N Λ κ ι) : ℝ :=
  ((64*(4*Real.pi)^2)*(2*((2*P.radiusBound+1)*P.multiplicity):ℕ))*
    (P.packetBound*(2*P.multiplierBound+P.multiplierLip))

theorem sourceAmplitude_nonneg (P : LabeledAngularErrorFamily N Λ κ ι) :
    0 ≤ P.sourceAmplitude := by
  have := P.packetBound_nonneg
  have := P.multiplierBound_nonneg
  have := P.multiplierLip_nonneg
  unfold sourceAmplitude
  positivity

def sources (P : LabeledAngularErrorFamily N Λ κ ι) (y : ℝ) : LineErrorSources N :=
  actualErrorSources P.wideExponent P.exponent P.direction P.direction_measurable
    P.referenceSlope P.angleBase P.smallRatio P.wideConstant P.sourceAmplitude P.topLength P.width y
    P.angleBase_pos P.smallRatio_pos P.sourceAmplitude_nonneg P.wideConstant_le P.topLength_pos P.width_pos

theorem scaleError_le (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) (y x : ℝ) :
    P.scaleError j y x ≤ (P.sources y).term j x := by
  have h := source_labeled_error_convolution (ι j) (P.site j) (P.site_injective j)
    (P.originX j) (P.originY j) (P.slope j)
    (div_pos P.topLength_pos (pow_pos (by norm_num) _)) P.width_pos
    (mul_pos P.angleBase_pos (pow_pos (by norm_num) _))
    P.packetBound_nonneg P.multiplierBound_nonneg P.multiplierLip_nonneg
    P.smallRatio_pos P.smallRatio_le P.wideRatio_ge (P.localMultiplicity j) P.radius_le
    (P.multiplier j) (P.multiplier_measurable j) (P.multiplier_bounded j)
    (P.multiplier_support j) P.direction P.direction_measurable P.referenceSlope
    (P.multiplier_near j) (P.multiplier_far j) (P.wave j) (P.wave_measurable j)
    (P.wave_bound j) P.test P.test_measurable P.test_bound (x,y)
  change P.scaleError j y x ≤ _ at h
  apply h.trans_eq
  rw [sources,actualErrorSources_term_eq]
  rw [← planarPositiveConvolution_const_mul]
  congr 1
  funext z
  unfold sourceAmplitude
  ring

theorem error_le_majorant (P : LabeledAngularErrorFamily N Λ κ ι) (y x : ℝ) :
    P.error y x ≤ (P.sources y).majorant x :=
  Finset.sum_le_sum (fun j _ => P.scaleError_le j y x)

theorem scaleError_nonneg (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) (y x : ℝ) :
    0 ≤ P.scaleError j y x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (tileEnvelope_nonneg _ _ _ _ _ _)

theorem error_nonneg (P : LabeledAngularErrorFamily N Λ κ ι) (y x : ℝ) :
    0 ≤ P.error y x := Finset.sum_nonneg fun j _ => P.scaleError_nonneg j y x

theorem error_measurable (P : LabeledAngularErrorFamily N Λ κ ι) :
    Measurable (fun z : ℝ×ℝ => P.error z.2 z.1) := by
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro b _
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (tileEnvelope_measurable _ _ _ _ _)

theorem sources_log_budget (P : LabeledAngularErrorFamily N Λ κ ι) (y : ℝ) :
    (P.sources y).sumBound =
      (P.sourceAmplitude*((P.wideExponent+1:ℕ)+4*P.smallRatio+
        (4/Real.log 2)*Real.log ((2:ℝ)^P.exponent)))*Real.pi :=
  actualErrorSources_log_sumBound P.wideExponent P.exponent P.direction P.direction_measurable
    P.referenceSlope P.angleBase P.smallRatio P.wideConstant P.sourceAmplitude P.topLength P.width y
    P.angleBase_pos P.smallRatio_pos P.sourceAmplitude_nonneg P.wideConstant_le P.topLength_pos P.width_pos

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
