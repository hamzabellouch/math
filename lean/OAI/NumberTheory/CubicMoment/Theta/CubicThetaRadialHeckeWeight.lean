import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMeanIntegral

namespace OAI

/-! The compact radial test dual to the two surviving Hecke height branches. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialHeckeWeight (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ)) : C_c(ℝ,ℂ) :=
  (r:ℂ)^2 • cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W+
    cubicThetaRadialWeightScale r hr W

lemma cubicThetaRadialHeckeWeight_apply (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ)) (v : ℝ) :
    cubicThetaRadialHeckeWeight r hr W v=(r:ℂ)^2*W (v/r)+W (r*v) := by
  change (r:ℂ)^2*W (r⁻¹*v)+W (r*v)=_
  rw [div_eq_mul_inv,mul_comm r⁻¹ v]

lemma cubicThetaRadialHeckeWeight_low {r H : ℝ} (hr : 1≤r) (hH : 0≤H) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤H*r,W v=0) :
    ∀ v≤H, cubicThetaRadialHeckeWeight r (by linarith) W v=0 := by
  intro v hv
  rw [cubicThetaRadialHeckeWeight_apply]
  have hratio : v/r≤H*r := by
    rw [div_le_iff₀ (by linarith : 0<r)]
    have : 1≤r*r := by nlinarith
    nlinarith
  rw [hW _ hratio,hW _ (by nlinarith),mul_zero,zero_add]

lemma cubicThetaRadialIntegral_hecke (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ))
    (f : ℝ → ℂ)
    (ha : IntegrableOn (fun v => star (W (v/r))/(v:ℂ)^3*f v) (Ioi (0:ℝ)))
    (hb : IntegrableOn (fun v => star (W (r*v))/(v:ℂ)^3*f v) (Ioi (0:ℝ))) :
    (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*(f (r*v)+(r:ℂ)^2*f (v/r)))=
      (r:ℂ)^2*(∫ v in Ioi (0:ℝ),star (W (v/r))/(v:ℂ)^3*f v)+
        ∫ v in Ioi (0:ℝ),star (W (r*v))/(v:ℂ)^3*f v := by
  have harg (v : ℝ) : v/r⁻¹=r*v := by simp [div_eq_mul_inv,mul_comm]
  have harg' (v : ℝ) : r⁻¹*v=v/r := by simp [div_eq_mul_inv,mul_comm]
  have hb' : IntegrableOn (fun v => star (W (v/r⁻¹))/(v:ℂ)^3*f v) (Ioi (0:ℝ)) := by
    simpa only [harg] using hb
  have hA := cubicThetaRadialIntegral_dilate_integrable r hr W f ha
  have hB := cubicThetaRadialIntegral_dilate_integrable r⁻¹ (inv_pos.mpr hr) W f hb'
  simp only [harg'] at hB
  have he := cubicThetaRadialIntegral_dilate r⁻¹ (inv_pos.mpr hr) W f
  simp only [harg,harg',Complex.ofReal_inv] at he
  calc
    _ = (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f (r*v))+
        (r:ℂ)^2*(∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f (v/r)) := by
      rw [←integral_const_mul,←integral_add hA (hB.const_mul _)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      ring
    _ = _ := by
      rw [cubicThetaRadialIntegral_dilate r hr W f,he]
      have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
      field_simp

lemma cubicThetaRadialHeckeWeight_integral (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ))
    (f : ℝ → ℂ)
    (ha : IntegrableOn (fun v => star (W (v/r))/(v:ℂ)^3*f v) (Ioi (0:ℝ)))
    (hb : IntegrableOn (fun v => star (W (r*v))/(v:ℂ)^3*f v) (Ioi (0:ℝ))) :
    (∫ v in Ioi (0:ℝ),star (cubicThetaRadialHeckeWeight r hr W v)/(v:ℂ)^3*f v)=
      (r:ℂ)^2*(∫ v in Ioi (0:ℝ),star (W (v/r))/(v:ℂ)^3*f v)+
        ∫ v in Ioi (0:ℝ),star (W (r*v))/(v:ℂ)^3*f v := by
  rw [←integral_const_mul,←integral_add (ha.const_mul _) hb]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  rw [cubicThetaRadialHeckeWeight_apply]
  simp only [star_add,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
  ring

end CubicFirstMoment

end

end OAI
