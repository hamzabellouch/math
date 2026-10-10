import OAI.Analysis.FiniteFactor.CrossedProduct.Trace
import OAI.Analysis.FiniteFactor.Model

namespace OAI

namespace FiniteFactor
noncomputable section

/-- The actual generated source algebra is finite: every isometry is unitary. -/
theorem sourceAlgebra_finite (θ : SourceCoordinate → ℝ) : IsFiniteAlgebra (sourceAlgebra θ) := by
  intro v hv hiso
  let p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate := 1 - v * star v
  have hp : p ∈ sourceAlgebra θ := sub_mem (one_mem _) (mul_mem hv (star_mem hv))
  have hw : (v * star v) * (v * star v) = v * star v := by
    calc
      _ = v * (star v * v) * star v := by simp only [mul_assoc]
      _ = v * star v := by rw [hiso]; simp
  have hps : star p = p := by
    change star (1 - v * star v) = 1 - v * star v
    rw [star_sub, star_one, star_mul, star_star]
  have hpp : star p * p = p := by
    rw [hps]
    change (1 - v * star v) * (1 - v * star v) = 1 - v * star v
    rw [sub_mul, one_mul, mul_sub, mul_one, hw]
    abel
  have ht : sourceVacuumFunctional (v * star v) = 1 := by
    rw [sourceVacuumFunctional_tracial θ hv (star_mem hv), hiso, sourceVacuumFunctional_one]
  have hz : sourceVacuumFunctional (star p * p) = 0 := by
    rw [hpp]
    change inner ℂ sourceVacuum ((1 - v * star v) sourceVacuum) = 0
    rw [sub_apply, inner_sub_right]
    change sourceVacuumFunctional 1 - sourceVacuumFunctional (v * star v) = 0
    rw [sourceVacuumFunctional_one, ht, sub_self]
  have hp0 := (sourceVacuumFunctional_square_eq_zero_iff θ hp).mp hz
  exact (sub_eq_zero.mp hp0).symm

end
end FiniteFactor

end OAI
