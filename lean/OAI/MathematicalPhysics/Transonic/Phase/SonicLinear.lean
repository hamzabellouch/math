import OAI.MathematicalPhysics.Transonic.Phase.Principal

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set
open scoped ContDiff

lemma GlobalProfile.U_smooth (P : GlobalProfile) :
    ContDiff ℝ ∞ (fun y => velocityToU y (P.velocity y)) :=
  (contDiff_id.sub P.velocity_smooth).div
    (contDiff_const.sub (contDiff_id.mul P.velocity_smooth)) (fun y => ne_of_gt (P.pole_pos y))

lemma GlobalProfile.A_smooth (P : GlobalProfile) : ContDiff ℝ ∞ P.A := by
  have he : P.A=(fun y => P.b*P.H y/(1-y*P.velocity y)) := funext P.A_eq
  rw [he]
  exact (contDiff_const.mul P.H_smooth).div
    (contDiff_const.sub (contDiff_id.mul P.velocity_smooth)) (fun y => ne_of_gt (P.pole_pos y))

lemma GlobalProfile.M0_smooth (P : GlobalProfile) : ContDiff ℝ ∞ P.M0 := by
  have he : P.M0=(fun y => P.A y^2*(1-P.velocity y^2)) := funext P.M0_factor
  rw [he]
  exact (P.A_smooth.pow 2).mul (contDiff_const.sub (P.velocity_smooth.pow 2))

lemma GlobalProfile.principalWeight_smooth (P : GlobalProfile) :
    ContDiff ℝ ∞ (fun y => P.M0 y^(-(2:ℝ)/3)*P.A y^2*(1-y*P.velocity y)^2) :=
  ((P.M0_smooth.rpow_const_of_ne (fun y => ne_of_gt (P.M0_pos y))).mul
    (P.A_smooth.pow 2)).mul ((contDiff_const.sub (contDiff_id.mul P.velocity_smooth)).pow 2)

lemma GlobalProfile.mellinPrincipal_sonic_derivative (P : GlobalProfile) :
    0<deriv P.mellinPrincipal (sonicRadius P.beta) := by
  let r := sonicRadius P.beta
  let K : ℝ → ℝ := fun y => P.M0 y^(-(2:ℝ)/3)*P.A y^2*(1-y*P.velocity y)^2
  let U : ℝ → ℝ := fun y => velocityToU y (P.velocity y)
  have hk : DifferentiableAt ℝ K r := P.principalWeight_smooth.differentiable (by simp) r
  have hu : DifferentiableAt ℝ U r := P.U_smooth.differentiable (by simp) r
  have hq := (hasDerivAt_const r (1:ℝ)).sub ((hu.hasDerivAt.pow 2).const_mul ell)
  have hd := (hk.hasDerivAt.mul hq).neg
  have he : P.mellinPrincipal=(fun y => -(K y*(1-ell*U y^2))) := by
    funext y
    exact (P.mellinPrincipal_U y).trans (by dsimp only [K,U]; ring)
  have hs := source_parameter_bounds P.beta_gt P.beta_lt
  have hU : U r=sonicSpeed := P.sonic_value
  have hz : 1-ell*U r^2=0 := by rw [hU,hs.1]; ring
  have hv : deriv P.mellinPrincipal r=2*ell*K r*sonicSpeed*deriv U r := by
    rw [he]
    have hd' : HasDerivAt (fun y => -(K y*(1-ell*U y^2)))
        (-(deriv K r*(1-ell*U r^2)+K r*(0-ell*(2*U r*deriv U r)))) r := by
      convert hd using 1
      simp
    rw [hd'.deriv,hz]
    simp only [mul_zero,zero_add,hU]
    ring
  rw [hv]
  have hK : 0<K r := mul_pos
    (mul_pos (Real.rpow_pos_of_pos (P.M0_pos r) _) (sq_pos_of_pos (P.A_pos r)))
    (sq_pos_of_pos (P.pole_pos r))
  exact mul_pos (mul_pos (mul_pos (by norm_num [ell]) hK) hs.2.1) P.sonic_slope

end SepticProfile

end
end

end OAI
