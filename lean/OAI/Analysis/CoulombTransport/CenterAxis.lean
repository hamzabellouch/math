import OAI.Analysis.CoulombTransport.CenterCertificate
import OAI.Analysis.CoulombTransport.HessianMatrix

namespace OAI

noncomputable section

namespace Problem356.CenterAxis

open CenterCertificate CoulombCalculus

/-- The finite certificate and the analytic construction use the same central point. -/
@[simp] theorem point_zero : point 0 = (0 : E3) := by
  simp [point]

/-- The first positive component is the first analytic axis. -/
@[simp] theorem point_one : point 1 = axisVector 0 := by
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- The first negative component is opposite to the first analytic axis. -/
@[simp] theorem point_two : point 2 = -axisVector 0 := by
  change (!₂[-1, 0, 0] : E3) = -axisVector 0
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- The second positive component is the second analytic axis. -/
@[simp] theorem point_three : point 3 = axisVector 1 := by
  change (!₂[0, 1, 0] : E3) = axisVector 1
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- The second negative component is opposite to the second analytic axis. -/
@[simp] theorem point_four : point 4 = -axisVector 1 := by
  change (!₂[0, -1, 0] : E3) = -axisVector 1
  ext i
  fin_cases i <;> norm_num [point, axisVector]

/-- Each noncentral certificate point is a unit vector. -/
theorem norm_point_of_ne_zero (i : Fin 5) (hi : i ≠ 0) : ‖point i‖ = 1 := by
  fin_cases i <;> simp_all

/-- The two canonical contact triples coincide literally with the analytic center triples. -/
theorem canonical_center_triples :
    (point 0, (point 1, point 2)) = ((0 : E3), (axisVector 0, -axisVector 0)) ∧
    (point 0, (point 3, point 4)) = ((0 : E3), (axisVector 1, -axisVector 1)) := by
  simp

end Problem356.CenterAxis

end

end OAI
