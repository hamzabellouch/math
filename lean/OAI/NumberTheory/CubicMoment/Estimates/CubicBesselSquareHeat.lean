import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselSumIntegral

namespace OAI

/-! The square of the fixed Schlaefli integral as a positive double heat
integral. Its inner Mellin integral reduces to the proved Gamma sum. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicBesselSquareHeat (p : ℝ × ℝ) (x : ℝ) : ℝ :=
  x^(1/3:ℝ)*cubicBesselHeat x p.1*cubicBesselHeat x p.2

lemma cubicBesselSquareHeat_nonneg {p : ℝ × ℝ} (hp : p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))
    {x : ℝ} (hx : 0 < x) : 0 ≤ cubicBesselSquareHeat p x :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (cubicBesselHeat_nonneg hp.1))
    (cubicBesselHeat_nonneg hp.2)

lemma cubicBesselSquareHeat_laplace (t u x : ℝ) :
    cubicBesselSquareHeat (t,u) x =
      (t^(-4/3:ℝ)*u^(-4/3:ℝ)*Real.exp (-(t+u)))*
        (x^((4/3:ℝ)-1)*Real.exp (-(1/t+1/u)*x)) := by
  have he : -(1/t+1/u)*x=(-x/t)+(-x/u) := by ring
  rw [he,Real.exp_add,show -(t+u)= -t + -u by ring,Real.exp_add]
  norm_num only [show (4/3:ℝ)-1=1/3 by norm_num]
  unfold cubicBesselSquareHeat cubicBesselHeat
  ring_nf

lemma cubicBesselSquareHeat_inner_integrable {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    IntegrableOn (cubicBesselSquareHeat (t,u)) (Ioi 0) := by
  have hr : 0 < 1/t+1/u := add_pos (one_div_pos.mpr ht) (one_div_pos.mpr hu)
  have hi := (integrable_laplace_rpow (by norm_num : (0:ℝ) < 4/3) hr).const_mul
    (t^(-4/3:ℝ)*u^(-4/3:ℝ)*Real.exp (-(t+u)))
  apply hi.congr
  filter_upwards with x
  exact (cubicBesselSquareHeat_laplace t u x).symm

lemma cubicBesselSquareHeat_inner {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    (∫ x in Ioi (0:ℝ), cubicBesselSquareHeat (t,u) x)=
      Real.Gamma (4/3)*cubicBesselSumWeight (t+u) := by
  have hr : 0 < 1/t+1/u := add_pos (one_div_pos.mpr ht) (one_div_pos.mpr hu)
  simp_rw [cubicBesselSquareHeat_laplace t u]
  rw [integral_const_mul,laplace_rpow (by norm_num : (0:ℝ) < 4/3) hr]
  have he : t*u*(1/t+1/u)=t+u := by field_simp; ring
  have hp : t^(-4/3:ℝ)*u^(-4/3:ℝ)*(1/t+1/u)^(-4/3:ℝ)=(t+u)^(-4/3:ℝ) := by
    rw [←Real.mul_rpow ht.le hu.le,←Real.mul_rpow (mul_pos ht hu).le hr.le,he]
  unfold cubicBesselSumWeight
  calc
    _ = Real.Gamma (4/3)*(t^(-4/3:ℝ)*u^(-4/3:ℝ)*(1/t+1/u)^(-4/3:ℝ))*
        Real.exp (-(t+u)) := by ring_nf
    _ = _ := by rw [hp]; ring

lemma cubicBesselKernel_sq_integral {x : ℝ} (hx : 0 < x) :
    (cubicBesselKernel x)^2 =
      ∫ p : ℝ × ℝ, cubicBesselSquareHeat p x
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hp : (x^(1/6:ℝ))^2=x^(1/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
    congr 1
    norm_num
  rw [cubicBesselKernel,mul_pow,hp]
  rw [show (∫ t in Ioi (0:ℝ), cubicBesselHeat x t)^2=
      ∫ p : ℝ × ℝ, cubicBesselHeat x p.1*cubicBesselHeat x p.2
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) by
          rw [integral_prod_mul,pow_two],←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  unfold cubicBesselSquareHeat
  ring

end CubicFirstMoment

end

end OAI
