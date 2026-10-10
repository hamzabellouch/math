import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionFourierPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMeanIntegral

namespace OAI

/-! Height dilation for genuine nonzero-frequency cusp observations. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialIntegral_divide (r : ℝ) (hr : 0<r)
    (W : C_c(ℝ,ℂ)) (f : ℝ → ℂ) :
    (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f (v/r))=
      ((r:ℂ)^2)⁻¹*∫ v in Ioi (0:ℝ),star (W (r*v))/(v:ℂ)^3*f v := by
  have he := cubicThetaRadialIntegral_dilate r⁻¹ (inv_pos.mpr hr) W f
  simpa only [div_inv_eq_mul,Complex.ofReal_inv,inv_pow,div_eq_mul_inv,inv_inv,mul_comm r,mul_comm r⁻¹] using he

lemma cubicThetaRadialIntegral_divide_integrable (r : ℝ) (hr : 0<r)
    (W : C_c(ℝ,ℂ)) (f : ℝ → ℂ)
    (hf : IntegrableOn (fun v => star (W (r*v))/(v:ℂ)^3*f v) (Ioi (0:ℝ))) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*f (v/r)) (Ioi (0:ℝ)) := by
  have hf' : IntegrableOn (fun v => star (W (v/r⁻¹))/(v:ℂ)^3*f v) (Ioi (0:ℝ)) := by
    simpa only [div_inv_eq_mul,mul_comm r] using hf
  have he := cubicThetaRadialIntegral_dilate_integrable r⁻¹ (inv_pos.mpr hr) W f hf'
  simpa only [div_eq_mul_inv,mul_comm r⁻¹] using he

lemma cubicThetaSectionFourier_divide_integrable (F : cubicThetaFiniteEnergySections)
    (h : Eisenstein) {r : ℝ} (hr : 1≤r) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*r,W v=0) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h (v/r))
      (Ioi (0:ℝ)) := by
  have hr0 : 0<r := lt_of_lt_of_le zero_lt_one hr
  let V := cubicThetaRadialWeightScale r hr0 W
  have hV : ∀ v≤(2:ℝ),V v=0 := by
    intro v hv
    change W (r*v)=0
    exact hW _ (by nlinarith)
  have hi := cubicThetaRadialIntegral_integrable_zero_extension V hV
    (cubicThetaSectionFourierFunction F h) (cubicThetaSectionFourier_weight_integrable F h V)
  exact cubicThetaRadialIntegral_divide_integrable r hr0 W _ hi

theorem cubicThetaSectionFourier_divide_pairing (F : cubicThetaFiniteEnergySections)
    (h : Eisenstein) {r : ℝ} (hr : 1≤r) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*r,W v=0) :
    (∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h (v/r))=
      ((r:ℂ)^2)⁻¹*inner ℂ
        (cubicThetaCuspFourierTest h (cubicThetaRadialWeightScale r (lt_of_lt_of_le zero_lt_one hr) W))
        (cubicThetaFiniteCuspRestriction F) := by
  have hr0 : 0<r := lt_of_lt_of_le zero_lt_one hr
  have hW2 : ∀ v≤(2:ℝ),W v=0 := by
    intro v hv
    exact hW _ (by linarith)
  let V := cubicThetaRadialWeightScale r hr0 W
  have hV : ∀ v≤(2:ℝ),V v=0 := by
    intro v hv
    change W (r*v)=0
    exact hW _ (by nlinarith)
  rw [cubicThetaRadialIntegral_zero_extension W hW2,cubicThetaRadialIntegral_divide r hr0]
  rw [cubicThetaSectionFourierPairing,cubicThetaRadialIntegral_zero_extension V hV]
  rfl

end CubicFirstMoment

end

end OAI
