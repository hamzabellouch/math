import Mathlib

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem lipschitz_derivative_taylor {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) {L : ℝ≥0} (hL : LipschitzWith L df)
    (x y : ℝ) : |f (x+y)-f x-df x*y| ≤ (L:ℝ)*y^2 := by
  let F : ℝ → ℝ := fun t => f (x+t*y)-df x*(t*y)
  have hD (t : ℝ) : HasDerivAt F ((df (x+t*y)-df x)*y) t := by
    convert ((hd (x+t*y)).comp t (((hasDerivAt_id t).mul_const y).const_add x)).sub
      (((hasDerivAt_id t).mul_const y).const_mul (df x)) using 1 <;> first | rfl | ring
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hD t).hasDerivWithinAt) (C:=(L:ℝ)*y^2) (by
      intro t ht
      rw [Real.norm_eq_abs,abs_mul]
      have HL := hL.dist_le_mul (x+t*y) x
      simp only [Real.dist_eq,add_sub_cancel_left,abs_mul] at HL
      calc
        _ ≤ ((L:ℝ)*(|t| *|y|))*|y| := mul_le_mul_of_nonneg_right HL (abs_nonneg _)
        _ ≤ ((L:ℝ)*(1*|y|))*|y| := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (by rw [abs_of_nonneg ht.1]; exact ht.2.le) (abs_nonneg _)) L.coe_nonneg) (abs_nonneg _)
        _ = _ := by rw [one_mul,mul_assoc,← pow_two,sq_abs])
  have heq : F 1-F 0=f (x+y)-f x-df x*y := by dsimp [F]; ring_nf
  rw [heq,Real.norm_eq_abs] at H
  exact H

theorem gaussian_abs_pow_integrable (n : ℕ) :
    Integrable (fun z : ℝ => |z|^n) (gaussianReal 0 1) := by
  have H := (memLp_id_gaussianReal' (μ:=0) (v:=1) (n:ℝ≥0∞) (by simp)).integrable_norm_pow'
  simpa only [id_eq,Real.norm_eq_abs] using H

theorem gaussian_second_moment : (∫ z : ℝ, z^2 ∂gaussianReal 0 1)=1 := by
  have H := variance_fun_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral (by fun_prop)] at H
  simpa using H

def gaussianThirdAbsMoment : ℝ := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1

theorem gaussianThirdAbsMoment_nonneg : 0 ≤ gaussianThirdAbsMoment :=
  integral_nonneg (fun _ => by positivity)

end SK.Analytic

end
end

end OAI
