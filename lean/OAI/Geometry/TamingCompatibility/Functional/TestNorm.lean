import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.PlaneMeasure

namespace OAI

section

noncomputable section
namespace TamingCompatibility.Concentration
open ContinuousAlternatingMap ExteriorForms
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma testOne_deriv_norm {h : V → ℝ} (hh : Differentiable ℝ h) (v y : V) :
    ‖extDeriv (testOne h v) y‖ ≤ 2*‖fderiv ℝ h y‖*‖v‖ := by
  apply ContinuousAlternatingMap.opNorm_le_bound _ (by positivity)
  intro m
  have he : ![m 0,m 1] = m := by ext i; fin_cases i <;> rfl
  rw [← he,testOne_deriv hh,Real.norm_eq_abs,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    _ ≤ |fderiv ℝ h y (m 0)*⟪v,m 1⟫|+|fderiv ℝ h y (m 1)*⟪v,m 0⟫| := by simpa only [Real.norm_eq_abs] using norm_sub_le (fderiv ℝ h y (m 0)*⟪v,m 1⟫) (fderiv ℝ h y (m 1)*⟪v,m 0⟫)
    _ = |fderiv ℝ h y (m 0)| *|⟪v,m 1⟫|+|fderiv ℝ h y (m 1)| *|⟪v,m 0⟫| := by rw [abs_mul,abs_mul]
    _ ≤ (‖fderiv ℝ h y‖*‖m 0‖)*(‖v‖*‖m 1‖)+
        (‖fderiv ℝ h y‖*‖m 1‖)*(‖v‖*‖m 0‖) := by
      apply add_le_add <;> apply mul_le_mul
      · exact (fderiv ℝ h y).le_opNorm (m 0)
      · exact abs_real_inner_le_norm _ _
      · positivity
      · positivity
      · exact (fderiv ℝ h y).le_opNorm (m 1)
      · exact abs_real_inner_le_norm _ _
      · positivity
      · positivity
    _ = _ := by ring
end TamingCompatibility.Concentration

end
end

end OAI
