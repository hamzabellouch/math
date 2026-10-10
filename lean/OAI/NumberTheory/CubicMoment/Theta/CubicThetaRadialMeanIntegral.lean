import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialWeightScaling
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! Change of height in the literal v^-3 radial mean integral. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaSectionMean_weight_integrable (F : cubicThetaFiniteEnergySections)
    (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*cubicThetaSectionMean F v) (Ioi (2:ℝ)) := by
  have hi := cubicThetaSectionMeanPairing_integrable F W
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2)*cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  have h := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable 2)
    (fun y => star (W y.2)*cubicThetaSectionFunction F y)).mp hi'
  rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)] at h
  change Integrable (fun y : ℂ × ℝ => star (W y.2)*cubicThetaSectionFunction F y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at h
  rw [←Measure.prod_restrict] at h
  apply h.integral_prod_right.congr
  filter_upwards with v
  dsimp only [cubicThetaSectionMean]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  ring

lemma cubicThetaRadialIntegral_zero_extension (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) (f : ℝ → ℂ) :
    (∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*f v)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f v := by
  have h (a : ℝ) (ha : a≤2) :
      (∫ v in Ioi a,star (W v)/(v:ℂ)^3*f v)=
        ∫ v : ℝ,star (W v)/(v:ℂ)^3*f v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hW v ((le_of_not_gt hv).trans ha),star_zero,zero_div,zero_mul]
  rw [h 2 le_rfl,h 0 (by norm_num)]

lemma cubicThetaRadialIntegral_dilate (r : ℝ) (hr : 0<r)
    (W : C_c(ℝ,ℂ)) (f : ℝ → ℂ) :
    (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f (r*v))=
      (r:ℂ)^2*∫ v in Ioi (0:ℝ),star (W (v/r))/(v:ℂ)^3*f v := by
  let g : ℝ → ℂ := fun v => star (W (v/r))/(v:ℂ)^3*f v
  have he : (fun v => star (W v)/(v:ℂ)^3*f (r*v))=
      (fun v => (r:ℂ)^3*g (r*v)) := by
    funext v
    dsimp only [g]
    rw [mul_div_cancel_left₀ v hr.ne',Complex.ofReal_mul,mul_pow]
    by_cases hv : v=0
    · simp [hv]
    · have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv
      field_simp
  rw [he,integral_const_mul,integral_comp_mul_left_Ioi g 0 hr,mul_zero]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  dsimp only [g]
  field_simp

lemma cubicThetaRadialIntegral_integrable_zero_extension (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) (f : ℝ → ℂ)
    (hf : IntegrableOn (fun v => star (W v)/(v:ℂ)^3*f v) (Ioi (2:ℝ))) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*f v) (Ioi (0:ℝ)) := by
  let g : ℝ → ℂ := fun v => star (W v)/(v:ℂ)^3*f v
  have he : (Ioi (0:ℝ)).indicator g=(Ioi (2:ℝ)).indicator g := by
    funext v
    change (if 0<v then g v else 0)=(if 2<v then g v else 0)
    split_ifs with h0 h2 h2
    · rfl
    · dsimp only [g]
      rw [hW v (le_of_not_gt h2),star_zero,zero_div,zero_mul]
    · have : False := h0 (lt_trans (by norm_num) h2)
      exact this.elim
    · rfl
  rw [←integrable_indicator_iff measurableSet_Ioi] at hf ⊢
  change Integrable ((Ioi (0:ℝ)).indicator g)
  rw [he]
  exact hf

lemma cubicThetaRadialIntegral_dilate_integrable (r : ℝ) (hr : 0<r)
    (W : C_c(ℝ,ℂ)) (f : ℝ → ℂ)
    (hf : IntegrableOn (fun v => star (W (v/r))/(v:ℂ)^3*f v) (Ioi (0:ℝ))) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*f (r*v)) (Ioi (0:ℝ)) := by
  let g : ℝ → ℂ := fun v => star (W (v/r))/(v:ℂ)^3*f v
  have hg : IntegrableOn (fun v => g (r*v)) (Ioi (0:ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff g 0 hr).mpr (by simpa only [mul_zero] using (show IntegrableOn g (Ioi (0:ℝ)) from hf))
  apply (hg.const_mul ((r:ℂ)^3)).congr
  filter_upwards with v
  dsimp only [g]
  rw [mul_div_cancel_left₀ v hr.ne',Complex.ofReal_mul,mul_pow]
  by_cases hv : v=0
  · simp [hv]
  · have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv
    field_simp

end CubicFirstMoment

end

end OAI
