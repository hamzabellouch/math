import OAI.Analysis.HenonEmden.RadialGeometry

namespace OAI

universe uE

section RadialTaylor

open MeasureTheory Set Metric NormedSpace
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma norm_radial_error {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : (1:ℝ)/2 ≤ ‖x‖) (y : E) :
    |(‖x‖-‖y‖)-inner ℝ x (x-y)/‖x‖| ≤ ‖x-y‖^2 := by
  have hr : 0 < ‖x‖ := by linarith
  have hid := norm_sub_sq_real x y
  have hI : inner ℝ x (x-y) = ‖x‖^2-inner ℝ x y := by
    rw [inner_sub_right,real_inner_self_eq_norm_sq]
  have hs : (‖x‖-‖y‖)^2 ≤ ‖x-y‖^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (‖x‖-‖y‖)) (norm_nonneg (x-y))).mpr (abs_norm_sub_norm_le x y)
  have he : (‖x‖-‖y‖)-inner ℝ x (x-y)/‖x‖ = (‖x‖*(‖x‖-‖y‖)-inner ℝ x (x-y))/‖x‖ := by
    field_simp
  rw [he,abs_div,abs_of_pos hr,div_le_iff₀ hr,hI]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (‖x‖-‖y‖),mul_le_mul_of_nonneg_right hx (sq_nonneg ‖x-y‖)]

lemma eta_radial_taylor {n : ℕ} (hn : 1 ≤ n) {x : Space n} (hx : (1:ℝ)/2 ≤ ‖x‖)
    (y : Space n) {D : ℝ} (hD : 0 ≤ D) (hseg : ∀ t ∈ uIcc ‖x‖ ‖y‖, gapProfile t ≤ D) :
    |eta n x-eta n y-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖| ≤
      (secondConstant n*D^(N n-2)+derivativeConstant n*D^(N n-1))*‖x-y‖^2 := by
  have hs := etaProfile_taylor hn hD hseg
  have hnrm := norm_radial_error hx y
  have hp := (derivativeProfile_bound n ‖x‖).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gapProfile_nonneg _) (hseg _ left_mem_uIcc) _) (constants_nonneg n).1)
  have hsq : (‖y‖-‖x‖)^2 ≤ ‖x-y‖^2 := by
    simpa only [sq_abs,norm_sub_rev y x] using
      (sq_le_sq₀ (abs_nonneg (‖y‖-‖x‖)) (norm_nonneg (y-x))).mpr (abs_norm_sub_norm_le y x)
  have hs' : |eta n x-eta n y-derivativeProfile n ‖x‖*(‖x‖-‖y‖)| ≤ secondConstant n*D^(N n-2)*‖x-y‖^2 := by
    have hh := hs.trans (mul_le_mul_of_nonneg_left hsq (mul_nonneg (constants_nonneg n).2.1 (pow_nonneg hD _)))
    rw [show eta n x-eta n y-derivativeProfile n ‖x‖*(‖x‖-‖y‖) =
      -(etaProfile n ‖y‖-etaProfile n ‖x‖-derivativeProfile n ‖x‖*(‖y‖-‖x‖)) by unfold eta; ring,abs_neg]
    exact hh
  have he : eta n x-eta n y-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖ =
      (eta n x-eta n y-derivativeProfile n ‖x‖*(‖x‖-‖y‖))+
      derivativeProfile n ‖x‖*((‖x‖-‖y‖)-inner ℝ x (x-y)/‖x‖) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hs'
    ((by rw [abs_mul]; exact mul_le_mul hp hnrm (abs_nonneg _) (mul_nonneg (constants_nonneg n).1 (pow_nonneg hD _)) :
      |derivativeProfile n ‖x‖*((‖x‖-‖y‖)-inner ℝ x (x-y)/‖x‖)| ≤
        derivativeConstant n*D^(N n-1)*‖x-y‖^2))).trans_eq (by ring))

lemma flux_linearization_identity {n : ℕ} {x y : Space n} (hx : x ≠ 0) (hxy : x ≠ y) :
    fluxFactor n (x,y)-eta n x+w n x*radialFactor (x,y) =
      (eta n x-eta n y-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖)*
        inner ℝ (x-y) y/‖x-y‖^2-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖ := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hd : ‖x-y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hI : inner ℝ (x-y) x = inner ℝ x (x-y) := real_inner_comm _ _
  have hJ : inner ℝ (x-y) y = inner ℝ x (x-y)-‖x-y‖^2 := by
    have he : inner ℝ (x-y) (x-y) = inner ℝ (x-y) x-inner ℝ (x-y) y := inner_sub_right _ _ _
    rw [real_inner_self_eq_norm_sq,hI] at he; linarith
  simp only [fluxFactor,X,inner_sub_right,real_inner_smul_right,radialFactor,w_eq_profile,wProfile]
  rw [hI,hJ]
  simp only [inner_sub_right]
  field_simp
  ring

end HenonLaneEmden
end
end RadialTaylor

end OAI
