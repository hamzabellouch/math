import OAI.Geometry.EinsteinFour.JacobiTraceProducts

namespace OAI

/-! The scalar curvature contribution to the normal-curvature energy. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped Matrix.Norms.Frobenius
noncomputable section

theorem frobenius_sq_eq_sum_entries (A : NormalMatrix) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (by positivity)

theorem frobenius_sq_one_add (A : NormalMatrix) :
    ‖1 + A‖ ^ 2 = 3 + 2 * A.trace + ‖A‖ ^ 2 := by
  simp only [frobenius_sq_eq_sum_entries, Matrix.trace, Matrix.diag_apply,
    Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_three]
  norm_num
  ring

theorem frobenius_sq_one_add_of_trace_zero (A : NormalMatrix) (hA : A.trace = 0) :
    ‖1 + A‖ ^ 2 = 3 + ‖A‖ ^ 2 := by rw [frobenius_sq_one_add, hA]; ring

end
end PositiveEinsteinFour.Jacobi

end OAI
