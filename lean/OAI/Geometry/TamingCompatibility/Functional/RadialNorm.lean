import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiDdcBound

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_logPotential_fderiv {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (logPotential s) z‖ ≤ 2/(s+‖z‖) := by
  have hA := radial_sq_pos hs z
  have ha : 0 < s+‖z‖ := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [logPotential_fderiv hs]
  simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,norm_mul,
    norm_inv,Real.norm_of_nonneg (le_of_lt hA)]
  calc
    _ ≤ (s^2+‖z‖^2)⁻¹ * (‖z‖*‖v‖) := by
      gcongr; exact norm_inner_le_norm _ _
    _ = (‖z‖/(s^2+‖z‖^2))*‖v‖ := by ring
    _ ≤ (2/(s+‖z‖))*‖v‖ := by
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
      apply (div_le_div_iff₀ hA ha).mpr
      nlinarith [sq_nonneg (s-‖z‖)]

lemma norm_sqrtPotential_fderiv {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (sqrtPotential s) z‖ ≤ 1 := by
  have hA := radial_sq_pos hs z
  have hq := Real.sqrt_pos.mpr hA
  have hq2 := Real.sq_sqrt (le_of_lt hA)
  have ht : ‖z‖ ≤ Real.sqrt (s^2+‖z‖^2) := by nlinarith [sq_nonneg s,norm_nonneg z]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [sqrtPotential_fderiv hs]
  simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,norm_mul,
    norm_inv,Real.norm_of_nonneg (le_of_lt hq),one_mul]
  calc
    _ ≤ (Real.sqrt (s^2+‖z‖^2))⁻¹ * (‖z‖*‖v‖) := by
      gcongr; exact norm_inner_le_norm _ _
    _ ≤ (Real.sqrt (s^2+‖z‖^2))⁻¹ * (Real.sqrt (s^2+‖z‖^2)*‖v‖) := by gcongr
    _ = _ := by field_simp

lemma norm_logPotential_hessian {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (logPotential s)) z‖ ≤ 6/(s+‖z‖)^2 := by
  have hA := radial_sq_pos hs z
  have ha : 0 < s+‖z‖ := by positivity
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  rw [logPotential_hessian hs]
  calc
    _ ≤ ‖⟪u,v⟫/(s^2+‖z‖^2)‖ + ‖2*⟪z,u⟫*⟪z,v⟫/(s^2+‖z‖^2)^2‖ := norm_sub_le _ _
    _ = ‖⟪u,v⟫‖/(s^2+‖z‖^2) + 2*‖⟪z,u⟫‖*‖⟪z,v⟫‖/(s^2+‖z‖^2)^2 := by
      simp only [norm_div,norm_mul,norm_pow,Real.norm_of_nonneg (le_of_lt hA)]
      norm_num
    _ ≤ (‖u‖*‖v‖)/(s^2+‖z‖^2) + 2*(‖z‖*‖u‖)*(‖z‖*‖v‖)/(s^2+‖z‖^2)^2 := by
      gcongr <;> exact norm_inner_le_norm _ _
    _ = (1/(s^2+‖z‖^2)+2*‖z‖^2/(s^2+‖z‖^2)^2)*‖u‖*‖v‖ := by ring
    _ ≤ (3/(s^2+‖z‖^2))*‖u‖*‖v‖ := by
      gcongr
      apply (le_div_iff₀ hA).mpr
      field_simp
      nlinarith [sq_nonneg s]
    _ ≤ (6/(s+‖z‖)^2)*‖u‖*‖v‖ := by
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
      apply (div_le_div_iff₀ hA (pow_pos ha 2)).mpr
      nlinarith [sq_nonneg (s-‖z‖)]

lemma norm_sqrtPotential_hessian {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (sqrtPotential s)) z‖ ≤ 4/(s+‖z‖) := by
  have hA := radial_sq_pos hs z
  have ha : 0 < s+‖z‖ := by positivity
  have hq := Real.sqrt_pos.mpr hA
  have hq2 := Real.sq_sqrt (le_of_lt hA)
  have hqa : s+‖z‖ ≤ 2*Real.sqrt (s^2+‖z‖^2) := by
    nlinarith [sq_nonneg (s-‖z‖)]
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  rw [sqrtPotential_hessian hs]
  calc
    _ ≤ ‖⟪u,v⟫/Real.sqrt (s^2+‖z‖^2)‖ +
      ‖⟪z,u⟫*⟪z,v⟫/(Real.sqrt (s^2+‖z‖^2))^3‖ := norm_sub_le _ _
    _ = ‖⟪u,v⟫‖/Real.sqrt (s^2+‖z‖^2) +
      ‖⟪z,u⟫‖*‖⟪z,v⟫‖/(Real.sqrt (s^2+‖z‖^2))^3 := by
        simp only [norm_div,norm_mul,norm_pow,Real.norm_of_nonneg (le_of_lt hq)]
    _ ≤ (‖u‖*‖v‖)/Real.sqrt (s^2+‖z‖^2) +
      (‖z‖*‖u‖)*(‖z‖*‖v‖)/(Real.sqrt (s^2+‖z‖^2))^3 := by
        gcongr <;> exact norm_inner_le_norm _ _
    _ = (1/Real.sqrt (s^2+‖z‖^2)+‖z‖^2/(Real.sqrt (s^2+‖z‖^2))^3)*‖u‖*‖v‖ := by ring
    _ ≤ (2/Real.sqrt (s^2+‖z‖^2))*‖u‖*‖v‖ := by
      gcongr
      apply (le_div_iff₀ hq).mpr
      field_simp
      nlinarith [sq_nonneg s]
    _ ≤ (4/(s+‖z‖))*‖u‖*‖v‖ := by
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
      apply (div_le_div_iff₀ hq ha).mpr
      linarith
end TamingCompatibility.RadialPotential

end

end OAI
