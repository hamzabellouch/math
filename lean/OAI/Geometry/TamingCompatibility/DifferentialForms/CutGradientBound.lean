import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationCutoff
import OAI.Geometry.TamingCompatibility.Functional.CompactProfilePoint

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma cutKernel_gradient_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    {a : ℝ} (ha : 0 < a) (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ z : V,
      ‖fderiv ℝ (cutKernel η r) z‖ ≤ (48/r^3)*((1+‖z‖/r)⁻¹)^6+C*r^4 := by
  obtain ⟨C,hC,hbound⟩ := cutKernel_deriv_bound η hη hηc hη0 hη1 ha hηone
  refine ⟨C,hC,fun r hr z => ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_⟩
  intro w
  rw [Real.norm_eq_abs]
  have hinner := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z w)
    (show 0 ≤ (6:ℝ)*radialCoefficient r ‖z‖ from mul_nonneg (by norm_num) (radialCoefficient_nonneg _ _))
  have hprofile := mul_le_mul_of_nonneg_right
    (radialCoefficient_linear_profile hr (norm_nonneg z)) (by positivity : 0 ≤ 6*‖w‖)
  have hder := hbound r hr z w
  have he : (8/r^3)*((1+‖z‖/r)⁻¹)^6*(6*‖w‖) = (48/r^3)*((1+‖z‖/r)⁻¹)^6*‖w‖ := by ring
  rw [he] at hprofile
  nlinarith
end TamingCompatibility.Concentration

end
end

end OAI
