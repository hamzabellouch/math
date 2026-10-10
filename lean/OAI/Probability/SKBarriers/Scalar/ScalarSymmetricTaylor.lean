import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSusceptibility
import OAI.Probability.SKBarriers.Gaussian.C1Taylor

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem lipschitz_second_derivative_taylor {f df ddf : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    {L : ℝ≥0} (hL : LipschitzWith L ddf) (x y : ℝ) :
    |f (x+y)-f x-df x*y-ddf x*y^2/2| ≤ (L:ℝ)*|y|^3 := by
  let F : ℝ → ℝ := fun t => f (x+t*y)-df x*(t*y)-ddf x*(t*y)^2/2
  have hD (t : ℝ) : HasDerivAt F ((df (x+t*y)-df x-ddf x*(t*y))*y) t := by
    convert (((hd (x+t*y)).comp t (((hasDerivAt_id t).mul_const y).const_add x)).sub
      (((hasDerivAt_id t).mul_const y).const_mul (df x))).sub
      (((((hasDerivAt_id t).mul_const y).pow 2).const_mul (ddf x)).div_const 2) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hD t).hasDerivWithinAt) (C:=(L:ℝ)*|y|^3) (by
      intro t ht
      rw [Real.norm_eq_abs,abs_mul]
      have HT := lipschitz_derivative_taylor hdd hL x (t*y)
      have htsq : t^2 ≤ 1 := by nlinarith [ht.1,ht.2]
      calc
        _ ≤ ((L:ℝ)*(t*y)^2)*|y| := mul_le_mul_of_nonneg_right HT (abs_nonneg _)
        _ ≤ ((L:ℝ)*y^2)*|y| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
          nlinarith [sq_nonneg y,mul_le_mul_of_nonneg_right htsq (sq_nonneg y)]
        _ = _ := by rw [← sq_abs y]; ring)
  have he : F 1-F 0=f (x+y)-f x-df x*y-ddf x*y^2/2 := by dsimp [F]; ring_nf
  rw [he,Real.norm_eq_abs] at H
  exact H

def symmetricIncrement (f : ℝ → ℝ) (z h : ℝ) : ℝ := f (z+h)+f (z-h)-2*f z

theorem symmetricIncrement_quad_bound {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) {K : ℝ≥0} (hK : LipschitzWith K df) (z h : ℝ) :
    |symmetricIncrement f z h| ≤ 2*(K:ℝ)*h^2 := by
  have hp := lipschitz_derivative_taylor hd hK z h
  have hn := lipschitz_derivative_taylor hd hK z (-h)
  rw [neg_sq] at hn
  have he : symmetricIncrement f z h=(f (z+h)-f z-df z*h)+(f (z+(-h))-f z-df z*(-h)) := by
    dsimp [symmetricIncrement]; ring_nf
  rw [he]
  calc
    _ ≤ |f (z+h)-f z-df z*h|+|f (z+(-h))-f z-df z*(-h)| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem symmetricIncrement_cubic_remainder {f df ddf : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    {L : ℝ≥0} (hL : LipschitzWith L ddf) (z h : ℝ) :
    |symmetricIncrement f z h-ddf z*h^2| ≤ 2*(L:ℝ)*|h|^3 := by
  have hp := lipschitz_second_derivative_taylor hd hdd hL z h
  have hn := lipschitz_second_derivative_taylor hd hdd hL z (-h)
  simp only [abs_neg,neg_sq] at hn
  have he : symmetricIncrement f z h-ddf z*h^2=
      (f (z+h)-f z-df z*h-ddf z*h^2/2)+
      (f (z+(-h))-f z-df z*(-h)-ddf z*h^2/2) := by dsimp [symmetricIncrement]; ring_nf
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

theorem scalarHierarchy_symmetricIncrement_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (z δ Y : ℝ) :
    |symmetricIncrement (scalarHierarchy n m v scalarSpinTerminal) z (δ*Y)| ≤ 2*δ^2*Y^2 ∧
    |symmetricIncrement (scalarHierarchy n m v scalarSpinTerminal) z (δ*Y)-
      δ^2*rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) z*Y^2| ≤
        2*(susceptibilityLipschitzConstant:ℝ)*|δ|^3*|Y|^3 := by
  constructor
  · have H := symmetricIncrement_quad_bound (scalarHierarchy_spin_hasDerivAt n m v)
      (scalarHierarchy_spin_gradient_lipschitz n m v hm) z (δ*Y)
    simpa only [NNReal.coe_one,mul_one,mul_pow,mul_assoc] using H
  · have H := symmetricIncrement_cubic_remainder (scalarHierarchy_spin_hasDerivAt n m v)
      (scalarHierarchy_spin_gradient_hasDerivAt n m v)
      (scalarHierarchy_spin_hessian_lipschitz n m v hm hmono) z (δ*Y)
    have he : rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) z*(δ*Y)^2=
        δ^2*rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) z*Y^2 := by ring
    rw [he,abs_mul,mul_pow] at H
    simpa only [mul_assoc] using H

end SK.Analytic

end
end

end OAI
