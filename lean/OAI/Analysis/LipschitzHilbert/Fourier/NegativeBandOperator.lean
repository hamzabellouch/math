import OAI.Analysis.LipschitzHilbert.Estimates.OperatorConjugation
import OAI.Analysis.LipschitzHilbert.Fourier.LocalizedBandOperator

namespace OAI

/-! The reflected negative band inherits the positive-band L2 constant
through the exact conjugation symmetry of the real Hilbert kernel. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem localizedSharpBandOperator_reflected
    (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ)
    (w l r : ℝ) (hw : 0<w) (f : Lp ℂ 2 planeMeasure) :
    localizedSharpBandOperator epsilon R he hR field hfield (conjugateReflectedCutoff p) w l r f=
      l2Conj planeMeasure (localizedSharpBandOperator epsilon R he hR field hfield p w l r
        (l2Conj planeMeasure f)) := by
  let C := l2Conj planeMeasure
  let M := stripL2Cutoff l r
  let K := sharpTimeKernel epsilon R
  let u := fun z : ℝ×ℝ => field (planeCoordinates z)
  have hu : LipschitzWith 2 u := by simpa only [u,mul_one] using product_slope_lipschitz field hfield
  let S := shortL2Operator K (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) u hu
  have hM (g : Lp ℂ 2 planeMeasure) : M (C g)=C (M g) :=
    congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T g)
      (l2Indicator_conjugate (horizontalStrip l r) (horizontalStrip_measurable l r))
  have hS (g : Lp ℂ 2 planeMeasure) : S (C g)=C (S g) :=
    congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T g)
      (shortL2Operator_conjugate K (sharpTimeKernel_measurable epsilon R)
        (sharpTimeKernel_integrable epsilon R he hR) (sharpTimeKernel_conj epsilon R) u hu)
  have hP (g : Lp ℂ 2 planeMeasure) : verticalL2Projection (conjugateReflectedCutoff p) w g=
      C (verticalL2Projection p w (C g)) :=
    congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T g)
      (verticalL2Projection_reflected p w hw)
  change M (S (verticalL2Projection (conjugateReflectedCutoff p) w (M f)))=
    C (M (S (verticalL2Projection p w (M (C f)))))
  rw [hP,hS,hM,←hM f]

theorem localized_negative_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ l r : ℝ, 1200*(r-l)≤1 →
      ‖localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield
        (conjugateReflectedCutoff p) w l r‖≤C := by
  obtain ⟨C,hC,hbound⟩ := localized_sharp_band_operator_norm hVariation hLL hH p hp
  refine ⟨C,hC,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb l r hwidth
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro f
  rw [localizedSharpBandOperator_reflected _ _ _ _ _ _ _ _ _ _ hw,l2Conj_norm]
  calc
    _ ≤ ‖localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield p w l r‖*
        ‖l2Conj planeMeasure f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C*‖f‖ := by
      rw [l2Conj_norm]
      exact mul_le_mul_of_nonneg_right (hbound epsilon R w he heR hR hw field hfield hfb l r hwidth) (norm_nonneg _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
