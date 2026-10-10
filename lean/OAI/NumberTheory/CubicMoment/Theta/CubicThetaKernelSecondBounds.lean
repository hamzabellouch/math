import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKernelFirstBounds

namespace OAI

/-! Relative bounds for the actual second coordinate derivatives. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCartesian_x_second_normalized (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v)) x=
      cubicThetaCartesianKernel s x y v*
        (-2*s/((x^2+y^2+v^2:ℝ):ℂ)+
          4*s*(s+1)*(x:ℂ)^2/((x^2+y^2+v^2:ℝ):ℂ)^2) := by
  rw [cubicThetaCartesian_horizontal_second s x y hv,
    cubicThetaQuadraticSecond_normalized (-s) (y^2+v^2) x
      (by nlinarith [sq_nonneg x,sq_nonneg y,sq_pos_of_pos hv])]
  unfold cubicThetaCartesianKernel cubicThetaQuadraticPower
  rw [add_assoc]
  ring

theorem cubicThetaCartesian_x_second_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s t y v)) x‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*((2*‖s‖+4*‖s‖*‖s+1‖)/v^2) := by
  rw [cubicThetaCartesian_x_second_normalized s x y hv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  apply (norm_add_le _ _).trans
  rw [norm_div,norm_div,norm_mul,norm_mul,norm_mul,norm_mul,
    norm_neg,Complex.norm_ofNat,Complex.norm_ofNat,norm_pow,norm_pow,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (cubicThetaCartesian_radius_pos x y hv),sq_abs]
  calc
    _ = (2*‖s‖)*(1/(x^2+y^2+v^2))+
      (4*‖s‖*‖s+1‖)*(x^2/(x^2+y^2+v^2)^2) := by ring
    _ ≤ (2*‖s‖)*(1/v^2)+(4*‖s‖*‖s+1‖)*(1/v^2) :=
      add_le_add (mul_le_mul_of_nonneg_left (cubicTheta_radius_inverse x y hv) (by positivity))
        (mul_le_mul_of_nonneg_left (cubicTheta_horizontal_square_ratio x y hv) (by positivity))
    _ = _ := by ring

theorem cubicThetaCartesian_y_second_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x t v)) y‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*((2*‖s‖+4*‖s‖*‖s+1‖)/v^2) := by
  simpa only [cubicThetaCartesian_swap s x] using cubicThetaCartesian_x_second_bound s y x hv

lemma cubicThetaCartesian_v_second_normalized (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t)) v=
      cubicThetaCartesianKernel s x y v*
        (s*(s-1)/(v:ℂ)^2-(4*s^2+2*s)/((x^2+y^2+v^2:ℝ):ℂ)+
          4*s*(s+1)*(v:ℂ)^2/((x^2+y^2+v^2:ℝ):ℂ)^2) := by
  rw [cubicThetaCartesian_vertical,cubicThetaVertical_second_deriv s
    (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv,
    cubicThetaVerticalSecond_normalized s (add_nonneg (sq_nonneg x) (sq_nonneg y)) hv]
  unfold cubicThetaVerticalKernel cubicThetaQuadraticPower cubicThetaCartesianKernel
  rw [add_comm (v^2) (x^2+y^2)]

theorem cubicThetaCartesian_v_second_bound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ‖deriv (deriv (fun t : ℝ => cubicThetaCartesianKernel s x y t)) v‖ ≤
      ‖cubicThetaCartesianKernel s x y v‖*
        ((‖s*(s-1)‖+‖4*s^2+2*s‖+4*‖s‖*‖s+1‖)/v^2) := by
  rw [cubicThetaCartesian_v_second_normalized s x y hv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  simp only [norm_div,norm_mul,norm_pow,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv,
    abs_of_pos (cubicThetaCartesian_radius_pos x y hv)]
  calc
    _ = (‖s‖*‖s-1‖)/v^2+‖4*s^2+2*s‖*(1/(x^2+y^2+v^2))+
      (4*‖s‖*‖s+1‖)*(v^2/(x^2+y^2+v^2)^2) := by ring
    _ ≤ (‖s‖*‖s-1‖)/v^2+‖4*s^2+2*s‖*(1/v^2)+
      (4*‖s‖*‖s+1‖)*(1/v^2) :=
      add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (cubicTheta_radius_inverse x y hv) (_root_.norm_nonneg _)))
        (mul_le_mul_of_nonneg_left (cubicTheta_vertical_square_ratio x y hv) (by positivity))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
