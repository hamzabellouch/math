import OAI.MathematicalPhysics.Transonic.Phase.Transport

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set
open scoped ContDiff

def GlobalProfile.timeTensor (P : GlobalProfile) (y : ℝ) : ℝ :=
  P.M0 y^((1:ℝ)/3)+(2/3:ℝ)*P.M0 y^(-(2:ℝ)/3)*P.A y^2
def GlobalProfile.mixedTensor (P : GlobalProfile) (y : ℝ) : ℝ :=
  (2/3:ℝ)*P.M0 y^(-(2:ℝ)/3)*P.A y*P.B y
def GlobalProfile.radialTensor (P : GlobalProfile) (y : ℝ) : ℝ :=
  P.M0 y^((1:ℝ)/3)-(2/3:ℝ)*P.M0 y^(-(2:ℝ)/3)*P.B y^2

def GlobalProfile.mellinPrincipal (P : GlobalProfile) (y : ℝ) : ℝ :=
  y^2*P.timeTensor y-2*y*P.mixedTensor y-P.radialTensor y

lemma GlobalProfile.M0_power_factor (P : GlobalProfile) (y : ℝ) :
    P.M0 y^((1:ℝ)/3)=P.M0 y^(-(2:ℝ)/3)*P.M0 y := by
  have he : (1:ℝ)/3=(-(2:ℝ)/3)+1 := by norm_num
  rw [he,Real.rpow_add (P.M0_pos y),Real.rpow_one]

lemma GlobalProfile.mellinPrincipal_factor (P : GlobalProfile) (y : ℝ) :
    P.mellinPrincipal y= -(P.M0 y^(-(2:ℝ)/3)*P.A y^2)*
      ((1-y*P.velocity y)^2-ell*(P.velocity y-y)^2) := by
  rw [GlobalProfile.mellinPrincipal,GlobalProfile.timeTensor,GlobalProfile.mixedTensor,
    GlobalProfile.radialTensor,P.M0_power_factor,P.M0_factor,P.B_eq]
  unfold ell
  ring

lemma GlobalProfile.mellinPrincipal_U (P : GlobalProfile) (y : ℝ) :
    P.mellinPrincipal y= -(P.M0 y^(-(2:ℝ)/3)*P.A y^2*(1-y*P.velocity y)^2)*
      (1-ell*(velocityToU y (P.velocity y))^2) := by
  rw [P.mellinPrincipal_factor,velocityToU]
  field_simp [ne_of_gt (P.pole_pos y)]
  ring

lemma GlobalProfile.sonic_value (P : GlobalProfile) :
    velocityToU (sonicRadius P.beta) (P.velocity (sonicRadius P.beta))=sonicSpeed :=
  (P.sonic_unique _ P.radius_pos.le).2 rfl

lemma GlobalProfile.mellinPrincipal_sonic (P : GlobalProfile) :
    P.mellinPrincipal (sonicRadius P.beta)=0 := by
  have hs := (source_parameter_bounds P.beta_gt P.beta_lt).1
  rw [P.mellinPrincipal_U,P.sonic_value,hs]
  ring

lemma GlobalProfile.mellinPrincipal_zero_iff (P : GlobalProfile) {y : ℝ} (hy : 0<y) :
    P.mellinPrincipal y=0 ↔ y=sonicRadius P.beta := by
  constructor
  · intro he
    have hp : 0<P.M0 y^(-(2:ℝ)/3)*P.A y^2*(1-y*P.velocity y)^2 :=
      mul_pos (mul_pos (Real.rpow_pos_of_pos (P.M0_pos y) _) (sq_pos_of_pos (P.A_pos y)))
        (sq_pos_of_pos (P.pole_pos y))
    rw [P.mellinPrincipal_U] at he
    have hu : 1-ell*(velocityToU y (P.velocity y))^2=0 :=
      (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr (ne_of_gt hp))
    have hU : 0<velocityToU y (P.velocity y) :=
      div_pos (sub_pos.mpr (P.below y hy).1) (P.pole_pos y)
    have hs := source_parameter_bounds P.beta_gt P.beta_lt
    have hroot : velocityToU y (P.velocity y)=sonicSpeed := by
      have hl : 0<ell := by norm_num [ell]
      nlinarith only [hu,hs.1,hs.2.1,hU,hl]
    exact (P.sonic_unique y hy.le).1 hroot
  · rintro rfl
    exact P.mellinPrincipal_sonic

end SepticProfile

end
end

end OAI
