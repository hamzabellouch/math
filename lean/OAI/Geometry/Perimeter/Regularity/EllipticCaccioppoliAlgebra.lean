import OAI.Geometry.Perimeter.Regularity.ContinuousWithinAtSurfaceGradientOfLocalLevel

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem near_identity_bounds (A : Euc n →L[ℝ] Euc n)
    (hA : ‖ContinuousLinearMap.id ℝ (Euc n)-A‖≤1/2) (ξ : Euc n) :
    ‖A ξ‖≤2*‖ξ‖ ∧ ‖ξ‖^2/2≤ inner ℝ (A ξ) ξ := by
  have he := (ContinuousLinearMap.id ℝ (Euc n)-A).le_opNorm ξ
  simp only [sub_apply,ContinuousLinearMap.id_apply] at he
  have he' : ‖ξ-A ξ‖≤(1/2)*‖ξ‖ := he.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg ξ))
  have hn := norm_sub_le ξ (ξ-A ξ)
  simp only [sub_sub_cancel] at hn
  have hi := abs_real_inner_le_norm (ξ-A ξ) ξ
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at hi
  have hi' := (le_abs_self (‖ξ‖^2-inner ℝ (A ξ) ξ)).trans hi
  have he'' := mul_le_mul_of_nonneg_right he' (norm_nonneg ξ)
  constructor <;> nlinarith [norm_nonneg ξ]

 theorem caccioppoli_scalar {X Y Z J : ℝ}
    (hJ : X^2/2-4*X*Y-X*Z-2*Y*Z≤J) :
    X^2≤4*J+256*(Y^2+Z^2) := by
  nlinarith [sq_nonneg (X-16*Y),sq_nonneg (X-4*Z),sq_nonneg (Y-Z),sq_nonneg Y,sq_nonneg Z]

 theorem caccioppoli_pointwise (A : Euc n →L[ℝ] Euc n)
    (hA : ‖ContinuousLinearMap.id ℝ (Euc n)-A‖≤1/2) (ξ η ζ : Euc n) (c u : ℝ) :
    c^2*‖ξ‖^2 ≤ 4*inner ℝ (A ξ-ζ) ((c^2)•ξ+(2*c*u)•η)+
      256*(u^2*‖η‖^2+c^2*‖ζ‖^2) := by
  obtain ⟨hAn,hAi⟩ := near_identity_bounds A hA ξ
  have h1 : |(2*c*u)*inner ℝ (A ξ) η|≤4*(|c| * ‖ξ‖)*(|u| * ‖η‖) := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (A ξ) η) (abs_nonneg (2*c*u))
    have hh' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAn (norm_nonneg η)) (abs_nonneg (2*c*u))
    simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at hh hh' ⊢
    convert hh.trans hh' using 1
    ring
  have h2 : |c^2*inner ℝ ζ ξ|≤(|c| * ‖ξ‖)*(|c| * ‖ζ‖) := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg c)]
    have hh := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm ζ ξ) (sq_nonneg c)
    convert hh using 1
    rw [←sq_abs c]
    ring
  have h3 : |(2*c*u)*inner ℝ ζ η|≤2*(|u| * ‖η‖)*(|c| * ‖ζ‖) := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm ζ η) (abs_nonneg (2*c*u))
    simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at hh ⊢
    convert hh using 1
    ring
  have hbase := mul_le_mul_of_nonneg_left hAi (sq_nonneg c)
  have hlo : (|c| * ‖ξ‖)^2/2-4*(|c| * ‖ξ‖)*(|u| * ‖η‖)-
      (|c| * ‖ξ‖)*(|c| * ‖ζ‖)-2*(|u| * ‖η‖)*(|c| * ‖ζ‖) ≤
      inner ℝ (A ξ-ζ) ((c^2)•ξ+(2*c*u)•η) := by
    simp only [inner_add_right,inner_sub_left,real_inner_smul_right]
    have hh1 := neg_abs_le ((2*c*u)*inner ℝ (A ξ) η)
    have hh2 := le_abs_self (c^2*inner ℝ ζ ξ)
    have hh3 := le_abs_self ((2*c*u)*inner ℝ ζ η)
    simp only [mul_pow,sq_abs]
    nlinarith
  have hh := caccioppoli_scalar hlo
  simpa only [mul_pow,sq_abs] using hh

 theorem gradient_mul_C1 {f g : Euc n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Euc n) :
    gradient (fun y ↦ f y*g y) x=f x•gradient g x+g x•gradient f x := by
  apply (InnerProductSpace.toDual ℝ (Euc n)).injective
  simp only [gradient,map_add,map_smul,LinearIsometryEquiv.apply_symm_apply]
  exact fderiv_mul (hf x) (hg x)

 theorem gradient_square_test {f χ : Euc n → ℝ} (hf : Differentiable ℝ f) (hχ : Differentiable ℝ χ)
    (x : Euc n) : gradient (fun y ↦ χ y*χ y*f y) x=(χ x)^2•gradient f x+(2*χ x*f x)•gradient χ x := by
  rw [gradient_mul_C1 (f := fun y ↦ χ y*χ y) (g := f) (hχ.mul hχ) hf,gradient_mul_C1 hχ hχ]
  simp only [smul_add,smul_smul,pow_two]
  module

end RPISingularHarnack

end

end OAI
