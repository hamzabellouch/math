import OAI.NumberTheory.CubicMoment.Theta.CubicThetaVerticalDerivatives

namespace OAI

/-! The hyperbolic eigenvalue equation for the actual height-power
kernel, in Cartesian coordinates on the upper half-space. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCartesianKernel (s : ℂ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^s*((x^2+y^2+v^2:ℝ):ℂ)^(-s)

lemma cubicThetaCartesian_horizontal_second (s : ℂ) (x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v)) x=
      (v:ℂ)^s*cubicThetaQuadraticSecond (-s) (y^2+v^2) x := by
  have he : (fun t : ℝ => cubicThetaCartesianKernel s t y v)=
      (fun t : ℝ => (v:ℂ)^s*cubicThetaQuadraticPower (-s) (y^2+v^2) t) := by
    funext t
    unfold cubicThetaCartesianKernel cubicThetaQuadraticPower
    rw [add_assoc]
  rw [he]
  simp_rw [deriv_const_mul_field']
  rw [cubicThetaQuadratic_second_deriv (-s) (y^2+v^2) x
    (by nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv])]

lemma cubicThetaCartesian_y_second (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x t v)) y=
      (v:ℂ)^s*cubicThetaQuadraticSecond (-s) (x^2+v^2) y := by
  have he : (fun t : ℝ => cubicThetaCartesianKernel s x t v)=
      (fun t : ℝ => cubicThetaCartesianKernel s t x v) := by
    funext t
    unfold cubicThetaCartesianKernel
    rw [add_comm (x^2) (t^2)]
  rw [he]
  exact cubicThetaCartesian_horizontal_second s y x hv

lemma cubicThetaCartesian_vertical (s : ℂ) (x y : ℝ) :
    (fun t : ℝ => cubicThetaCartesianKernel s x y t)=
      cubicThetaVerticalKernel s (x^2+y^2) := by
  funext t
  unfold cubicThetaCartesianKernel cubicThetaVerticalKernel cubicThetaQuadraticPower
  rw [add_comm (x^2+y^2) (t^2)]

lemma cubicThetaKernel_jet_equation (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    (v:ℂ)^2*((v:ℂ)^s*cubicThetaQuadraticSecond (-s) (y^2+v^2) x+
      (v:ℂ)^s*cubicThetaQuadraticSecond (-s) (x^2+v^2) y+
      cubicThetaVerticalSecond s (x^2+y^2) v)-
        (v:ℂ)*cubicThetaVerticalFirst s (x^2+y^2) v=
      s*(s-2)*cubicThetaCartesianKernel s x y v := by
  let R : ℝ := x^2+y^2+v^2
  have hR : 0<R := by dsimp [R]; nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]
  have hRc : (R:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hx : x^2+(y^2+v^2)=R := by dsimp [R]; ring
  have hy : y^2+(x^2+v^2)=R := by dsimp [R]; ring
  have hz : v^2+(x^2+y^2)=R := by dsimp [R]; ring
  simp only [cubicThetaQuadraticSecond,cubicThetaVerticalSecond,cubicThetaVerticalFirst,
    cubicThetaQuadraticFirst,cubicThetaQuadraticPower,cubicThetaCartesianKernel]
  rw [hx,hy,hz]
  change (v:ℂ)^2*((v:ℂ)^s*(2*(-s)*(R:ℂ)^(-s-1)+
      4*(-s)*(-s-1)*(x:ℂ)^2*(R:ℂ)^(-s-2))+
    (v:ℂ)^s*(2*(-s)*(R:ℂ)^(-s-1)+4*(-s)*(-s-1)*(y:ℂ)^2*(R:ℂ)^(-s-2))+
    (s*(s-1)*(v:ℂ)^(s-2)*(R:ℂ)^(-s)+
      2*s*(v:ℂ)^(s-1)*(2*(-s)*(v:ℂ)*(R:ℂ)^(-s-1))+
      (v:ℂ)^s*(2*(-s)*(R:ℂ)^(-s-1)+4*(-s)*(-s-1)*(v:ℂ)^2*(R:ℂ)^(-s-2))))-
    (v:ℂ)*(s*(v:ℂ)^(s-1)*(R:ℂ)^(-s)+
      (v:ℂ)^s*(2*(-s)*(v:ℂ)*(R:ℂ)^(-s-1)))=
        s*(s-2)*((v:ℂ)^s*(R:ℂ)^(-s))
  rw [Complex.cpow_sub (-s) 1 hRc,Complex.cpow_sub (-s) 2 hRc,
    Complex.cpow_sub s 2 hvc,Complex.cpow_sub s 1 hvc]
  norm_num only [Complex.cpow_one,Complex.cpow_ofNat]
  have he : (R:ℂ)=(x:ℂ)^2+(y:ℂ)^2+(v:ℂ)^2 := by
    dsimp [R]
    push_cast
    rfl
  field_simp
  rw [he]
  ring

theorem cubicThetaCartesian_eigenvalue (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    (v:ℂ)^2*(deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v)) x+
      deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x t v)) y+
      deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t)) v)-
        (v:ℂ)*deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t) v=
      s*(s-2)*cubicThetaCartesianKernel s x y v := by
  rw [cubicThetaCartesian_horizontal_second s x y hv,
    cubicThetaCartesian_y_second s x y hv,cubicThetaCartesian_vertical,
    cubicThetaVertical_second_deriv s (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv,
    cubicThetaVertical_deriv s (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv]
  exact cubicThetaKernel_jet_equation s x y hv

end CubicFirstMoment

end

end OAI
