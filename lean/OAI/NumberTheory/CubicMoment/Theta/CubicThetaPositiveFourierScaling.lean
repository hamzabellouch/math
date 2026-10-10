import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHighSource

namespace OAI

/-! The full positive-height pairing survives every positive radial dilation. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveFourier_divide_integrable (F : CubicThetaSection)
    (h : Eisenstein) {r : ℝ} (hr : 0<r) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h (v/r))
      (Ioi (0:ℝ)) := by
  have hV := cubicThetaRadialWeightScale_positive_low hr W hW
  have hi := cubicThetaPositiveFourier_integrable h (cubicThetaRadialWeightScale r hr W)
    (div_pos hε hr) hV F
  exact cubicThetaRadialIntegral_divide_integrable r hr W _ hi

lemma cubicThetaPositiveFourier_divide_pairing (F : cubicThetaFiniteEnergySections)
    (h : Eisenstein) {r : ℝ} (hr : 0<r) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h (v/r))=
      ((r:ℂ)^2)⁻¹*inner ℂ
        (cubicThetaPositiveFourierMass h (cubicThetaRadialWeightScale r hr W)
          (div_pos hε hr) (cubicThetaRadialWeightScale_positive_low hr W hW)
          (cubicThetaRadialWeightScale_smooth r hr W hsm))
        (cubicThetaFiniteMassClosure F) := by
  rw [cubicThetaRadialIntegral_divide r hr W,
    cubicThetaPositiveFourierMass_pairing_finite]
  rfl

lemma cubicThetaPositiveFourier_dilate_integrable (F : CubicThetaSection)
    (h : Eisenstein) {r : ℝ} (hr : 0<r) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h (r*v))
      (Ioi (0:ℝ)) := by
  have hV := cubicThetaRadialWeightScale_positive_low (inv_pos.mpr hr) W hW
  have hi := cubicThetaPositiveFourier_integrable h
    (cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W)
    (div_pos hε (inv_pos.mpr hr)) hV F
  apply cubicThetaRadialIntegral_dilate_integrable r hr W _
  simpa only [cubicThetaRadialWeightScale_apply,mul_comm r⁻¹,←div_eq_mul_inv] using hi

lemma cubicThetaPositiveFourier_dilate_pairing (F : cubicThetaFiniteEnergySections)
    (h : Eisenstein) {r : ℝ} (hr : 0<r) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h (r*v))=
      (r:ℂ)^2*inner ℂ
        (cubicThetaPositiveFourierMass h (cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W)
          (div_pos hε (inv_pos.mpr hr))
          (cubicThetaRadialWeightScale_positive_low (inv_pos.mpr hr) W hW)
          (cubicThetaRadialWeightScale_smooth _ _ W hsm))
        (cubicThetaFiniteMassClosure F) := by
  rw [cubicThetaRadialIntegral_dilate r hr W,cubicThetaPositiveFourierMass_pairing_finite]
  simp only [cubicThetaRadialWeightScale_apply,mul_comm r⁻¹,←div_eq_mul_inv]

end CubicFirstMoment

end

end OAI
