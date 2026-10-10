import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import OAI.MathematicalPhysics.Transonic.Phase.Radial

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped ContDiff Topology

lemma GlobalProfile.velocity_derivative (P : GlobalProfile) (y : ℝ) :
    HasDerivAt P.velocity (deriv P.velocity y) y :=
  (P.velocity_smooth.differentiable (by simp) y).hasDerivAt
lemma GlobalProfile.speed_sq_pos (P : GlobalProfile) (y : ℝ) : 0<1-(P.velocity y)^2 := by
  have h := abs_lt.mp (P.velocity_range y)
  nlinarith only [h.1,h.2,sq_nonneg (P.velocity y)]

def GlobalProfile.logA (P : GlobalProfile) (y : ℝ) : ℝ :=
  (P.beta*P.velocity y+y*deriv P.velocity y)/(1-y*P.velocity y)

lemma GlobalProfile.A_derivative (P : GlobalProfile) (y : ℝ) :
    HasDerivAt P.A (P.A y*P.logA y) y := by
  have he : P.A=(fun q => P.b*P.H q/(1-q*P.velocity q)) := funext P.A_eq
  have hd := ((P.H_derivative y).const_mul P.b).div
    ((hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_id y).mul (P.velocity_derivative y)))
    (ne_of_gt (P.pole_pos y))
  rw [he]
  convert hd using 1 <;> try rfl
  dsimp only [GlobalProfile.logA,GlobalProfile.integrand,Pi.sub_apply,Pi.mul_apply,id_eq]
  field_simp [ne_of_gt (P.pole_pos y)]
  unfold GlobalProfile.b
  ring

lemma GlobalProfile.M0_factor (P : GlobalProfile) (y : ℝ) :
    P.M0 y=(P.A y)^2*(1-(P.velocity y)^2) := by
  rw [GlobalProfile.M0,P.B_eq]
  ring

lemma GlobalProfile.M0_derivative (P : GlobalProfile) (y : ℝ) :
    HasDerivAt P.M0 (P.M0 y*(2*P.logA y-2*P.velocity y*deriv P.velocity y/(1-(P.velocity y)^2))) y := by
  have he : P.M0=fun q => (P.A q)^2*(1-(P.velocity q)^2) := funext P.M0_factor
  have hd := ((P.A_derivative y).pow 2).mul
    ((hasDerivAt_const y (1:ℝ)).sub ((P.velocity_derivative y).pow 2))
  rw [he]
  convert hd using 1
  norm_num only [Nat.cast_ofNat,pow_one,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
  field_simp [ne_of_gt (P.speed_sq_pos y)]
  ring

lemma hasDerivAt_rpow_log {f : ℝ → ℝ} {x a r : ℝ}
    (hf : HasDerivAt f (f x*a) x) (hp : 0<f x) :
    HasDerivAt (fun z => (f z)^r) ((f x)^r*(r*a)) x := by
  have hd := hf.rpow_const (p:=r) (Or.inl (ne_of_gt hp))
  rw [Real.rpow_sub_one (ne_of_gt hp)] at hd
  convert hd using 1
  field_simp [ne_of_gt hp]

def GlobalProfile.F (P : GlobalProfile) (y : ℝ) : ℝ := (P.M0 y)^((1:ℝ)/3)*P.A y
def GlobalProfile.G (P : GlobalProfile) (y : ℝ) : ℝ := (P.M0 y)^((1:ℝ)/3)*P.B y
def GlobalProfile.logF (P : GlobalProfile) (y : ℝ) : ℝ :=
  (5/3:ℝ)*P.logA y-(2/3:ℝ)*P.velocity y*deriv P.velocity y/(1-(P.velocity y)^2)

lemma GlobalProfile.F_derivative (P : GlobalProfile) (y : ℝ) :
    HasDerivAt P.F (P.F y*P.logF y) y := by
  have hd := (hasDerivAt_rpow_log (r:=(1:ℝ)/3) (P.M0_derivative y) (P.M0_pos y)).mul
    (P.A_derivative y)
  convert hd using 1 <;> try rfl
  dsimp only [GlobalProfile.F,GlobalProfile.logF]
  ring
lemma GlobalProfile.G_eq (P : GlobalProfile) (y : ℝ) : P.G y=P.F y*P.velocity y := by
  rw [GlobalProfile.G,P.B_eq,GlobalProfile.F]
  ring
lemma GlobalProfile.G_derivative (P : GlobalProfile) (y : ℝ) :
    HasDerivAt P.G (P.F y*P.logF y*P.velocity y+P.F y*deriv P.velocity y) y := by
  have he : P.G=fun q => P.F q*P.velocity q := funext P.G_eq
  rw [he]
  exact (P.F_derivative y).mul (P.velocity_derivative y)

lemma source_transport_algebra {y v w beta : ℝ} (hy : y≠0) (hp : 1-y*v≠0)
    (hv : 1-v^2≠0) (he : profileDenom ell y v*w=profileNumer ell beta y v) :
    ell*beta+(y-v)*((5/3:ℝ)*(beta*v+y*w)/(1-y*v)-(2/3:ℝ)*v*w/(1-v^2))-w-3*v/y=0 := by
  have hi : (ell*beta+(y-v)*((5/3:ℝ)*(beta*v+y*w)/(1-y*v)-(2/3:ℝ)*v*w/(1-v^2))-w-3*v/y)*
      (y*(1-y*v)*(1-v^2))=profileNumer ell beta y v-profileDenom ell y v*w := by
    unfold profileNumer profileDenom ell
    field_simp [hy,hp,hv]
    ring
  rw [he,sub_self] at hi
  exact (mul_eq_zero.mp hi).resolve_right (mul_ne_zero (mul_ne_zero hy hp) hv)

lemma GlobalProfile.radial_transport (P : GlobalProfile) {y : ℝ} (hy : 0<y) :
    ell*P.beta*P.F y+y*deriv P.F y-deriv P.G y-3*P.G y/y=0 := by
  have hc := source_transport_algebra (ne_of_gt hy) (ne_of_gt (P.pole_pos y))
    (ne_of_gt (P.speed_sq_pos y)) (P.equation y hy.le)
  change ell*P.beta+(y-P.velocity y)*((5/3:ℝ)*(P.beta*P.velocity y+y*deriv P.velocity y)/
    (1-y*P.velocity y)-(2/3:ℝ)*P.velocity y*deriv P.velocity y/(1-P.velocity y^2))-
    deriv P.velocity y-3*P.velocity y/y=0 at hc
  have hc' : ell*P.beta+(y-P.velocity y)*P.logF y-deriv P.velocity y-3*P.velocity y/y=0 := by
    simpa only [GlobalProfile.logF,GlobalProfile.logA,mul_div_assoc] using hc
  rw [(P.F_derivative y).deriv,(P.G_derivative y).deriv,P.G_eq]
  calc
    _=P.F y*(ell*P.beta+(y-P.velocity y)*P.logF y-deriv P.velocity y-3*P.velocity y/y) := by ring
    _=0 := by rw [hc',mul_zero]

end SepticProfile

end
end

end OAI
