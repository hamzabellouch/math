import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselLogIntegral

namespace OAI

/-! Absolute integrability of the logarithmic cubic Bessel weight. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicBesselLogWeight (a u : ℝ) : ℝ :=
  Real.exp (-u/3)*Real.exp (-2*a*Real.cosh u)

lemma cubicBesselLogWeight_pos (a u : ℝ) : 0<cubicBesselLogWeight a u :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

lemma cubicBesselLogWeight_integrable {a : ℝ} (ha : 0<a) :
    Integrable (cubicBesselLogWeight a) := by
  have hi : IntegrableOn (fun t : ℝ => cubicBesselHeat (a^2) (a*t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff _ 0 ha).mpr
    simpa only [mul_zero] using cubicBesselHeat_integrable (sq_pos_of_pos ha)
  have hg : IntegrableOn (fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-a*(t+t⁻¹))) (Ioi 0) := by
    apply ((hi.const_mul a).const_mul ((a^2)^(1/6:ℝ))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [mul_assoc] using cubicBessel_scaled_heat ha ht
  have hl := (integrable_comp_exp _).mpr hg
  apply hl.congr
  filter_upwards with u
  change Real.exp u*((Real.exp u)^(-4/3:ℝ)*Real.exp (-a*(Real.exp u+(Real.exp u)⁻¹)))=
    cubicBesselLogWeight a u
  rw [←Real.exp_mul]
  have he : Real.exp u*Real.exp (u*(-4/3))=Real.exp (-u/3) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [←mul_assoc,he]
  unfold cubicBesselLogWeight
  rw [Real.cosh_eq,Real.exp_neg]
  congr 2
  ring

lemma cubicBesselKernel_log {a : ℝ} (ha : 0<a) :
    cubicBesselKernel (a^2)=∫ u : ℝ,cubicBesselLogWeight a u :=
  cubicBesselKernel_log_integral ha

end CubicFirstMoment

end

end OAI
