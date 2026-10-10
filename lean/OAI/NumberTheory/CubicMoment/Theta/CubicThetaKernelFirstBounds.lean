import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKernelRatios

namespace OAI

/-! Uniform first-coordinate derivative bounds for the kernel. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCartesian_x_deriv (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v) x=
      cubicThetaCartesianKernel s x y v*
        (-2*s*(x:ℂ)/((x^2+y^2+v^2:ℝ):ℂ)) := by
  have hp : 0<x^2+(y^2+v^2) := by
    nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv]
  have he : (fun t : ℝ => cubicThetaCartesianKernel s t y v)=
      (fun t : ℝ => (v:ℂ)^s*cubicThetaQuadraticPower (-s) (y^2+v^2) t) := by
    funext t
    unfold cubicThetaCartesianKernel cubicThetaQuadraticPower
    rw [add_assoc]
  rw [he,deriv_const_mul_field,cubicThetaQuadratic_deriv (-s) (y^2+v^2) x hp,
    cubicThetaQuadraticFirst_normalized (-s) (y^2+v^2) x hp]
  unfold cubicThetaQuadraticPower cubicThetaCartesianKernel
  rw [add_assoc]
  ring

theorem cubicThetaCartesian_x_deriv_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v) x‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*(2*‖s‖/v) := by
  rw [cubicThetaCartesian_x_deriv s x y hv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  rw [norm_div,norm_mul,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,
    Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (cubicThetaCartesian_radius_pos x y hv)]
  calc
    _ = (2*‖s‖)*(|x|/(x^2+y^2+v^2)) := by ring
    _ ≤ (2*‖s‖)*(1/v) := mul_le_mul_of_nonneg_left
      (cubicTheta_horizontal_ratio x y hv) (by positivity)
    _ = _ := by ring

lemma cubicThetaCartesian_v_deriv (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t) v=
      cubicThetaCartesianKernel s x y v*
        (s/(v:ℂ)-2*s*(v:ℂ)/((x^2+y^2+v^2:ℝ):ℂ)) := by
  rw [cubicThetaCartesian_vertical,cubicThetaVertical_deriv s
    (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv,
    cubicThetaVerticalFirst_normalized s (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv]
  unfold cubicThetaVerticalKernel cubicThetaQuadraticPower cubicThetaCartesianKernel
  rw [add_comm (v^2) (x^2+y^2)]

theorem cubicThetaCartesian_v_deriv_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t) v‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*(3*‖s‖/v) := by
  rw [cubicThetaCartesian_v_deriv s x y hv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  apply (norm_sub_le _ _).trans
  rw [norm_div,norm_div,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hv,
    abs_of_pos (cubicThetaCartesian_radius_pos x y hv)]
  calc
    _ = ‖s‖/v+(2*‖s‖)*(v/(x^2+y^2+v^2)) := by ring
    _ ≤ ‖s‖/v+(2*‖s‖)*(1/v) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (cubicTheta_vertical_ratio x y hv)
        (show 0≤2*‖s‖ by positivity))
    _ = _ := by ring

lemma cubicThetaCartesian_swap (s : ℂ) (x y v : ℝ) :
    cubicThetaCartesianKernel s x y v=cubicThetaCartesianKernel s y x v := by
  unfold cubicThetaCartesianKernel
  rw [add_comm (x^2) (y^2)]

theorem cubicThetaCartesian_y_deriv_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (fun t : ℝ => cubicThetaCartesianKernel s x t v) y‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*(2*‖s‖/v) := by
  simpa only [cubicThetaCartesian_swap s x] using cubicThetaCartesian_x_deriv_bound s y x hv

end CubicFirstMoment

end

end OAI
