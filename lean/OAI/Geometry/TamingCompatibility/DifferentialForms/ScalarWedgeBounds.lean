import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Linear

namespace OAI

section

noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma one_eval_norm (a : Form (E := V) 1) (v : V) : |a ![v]| ≤ ‖a‖*‖v‖ := by
  have hh := (oneLinear a).le_opNorm v
  rw [oneLinear_apply] at hh
  simpa only [oneLinear,LinearIsometryEquiv.norm_map,Real.norm_eq_abs] using hh

lemma scalar_wedge_norm (l : V →L[ℝ] ℝ) (a : Form (E := V) 1) :
    ‖wedgeOne l a‖ ≤ 2*‖l‖*‖a‖ := by
  apply ContinuousAlternatingMap.opNorm_le_bound _ (by positivity)
  intro m
  have he : ![m 0,m 1] = m := by ext i; fin_cases i <;> rfl
  rw [← he,wedgeOne_apply_two,Real.norm_eq_abs,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    _ ≤ |l (m 0)*a ![m 1]|+|l (m 1)*a ![m 0]| := by simpa only [Real.norm_eq_abs] using norm_sub_le (l (m 0)*a ![m 1]) (l (m 1)*a ![m 0])
    _ = |l (m 0)| *|a ![m 1]|+|l (m 1)| *|a ![m 0]| := by rw [abs_mul,abs_mul]
    _ ≤ (‖l‖*‖m 0‖)*(‖a‖*‖m 1‖)+(‖l‖*‖m 1‖)*(‖a‖*‖m 0‖) := by
      apply add_le_add <;> apply mul_le_mul
      · exact l.le_opNorm _
      · exact one_eval_norm _ _
      · positivity
      · positivity
      · exact l.le_opNorm _
      · exact one_eval_norm _ _
      · positivity
      · positivity
    _ = _ := by ring

lemma scalar_wedge_unit (l : V →L[ℝ] ℝ) (a : Form (E := V) 1) (u v : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |wedgeOne l a ![u,v]| ≤ ‖a‖*(|l u|+|l v|) := by
  have ha := one_eval_norm a u
  have hb := one_eval_norm a v
  rw [hu,mul_one] at ha
  rw [hv,mul_one] at hb
  rw [wedgeOne_apply_two]
  calc
    _ ≤ |l u*a ![v]|+|l v*a ![u]| := by simpa only [Real.norm_eq_abs] using norm_sub_le (l u*a ![v]) (l v*a ![u])
    _ ≤ |l u| *‖a‖+|l v| *‖a‖ := by rw [abs_mul,abs_mul]; gcongr
    _ = _ := by ring
end TamingCompatibility.ExteriorForms

end
end

end OAI
