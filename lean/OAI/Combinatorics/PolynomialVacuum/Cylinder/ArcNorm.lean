import OAI.Combinatorics.PolynomialVacuum.Cylinder.WeightFactor

namespace OAI

namespace PolynomialVacuumCylinder
open PolynomialVacuumAlgebra
variable {M : ℕ} {D : Finset (Vertex M)}

theorem criticalActivity_xStar : xStar=(PolynomialVacuumBridge.Corridor.criticalActivity : ℂ) := by
  simp only [xStar,PolynomialVacuumBridge.Corridor.criticalActivity,Real.cos_pi_div_eight]
  congr 1
  congr 1
  ring

@[simp] theorem norm_loopTurnPhase (r : ℤ) : ‖loopTurnPhase r‖=1 := by
  simp [loopTurnPhase,Complex.norm_exp,Complex.mul_re]
@[simp] theorem norm_zeta : ‖zeta‖=1 := by simp [zeta_eq_I]
@[simp] theorem norm_xStar : ‖xStar‖=PolynomialVacuumBridge.Corridor.criticalActivity := by
  rw [criticalActivity_xStar,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos PolynomialVacuumBridge.Corridor.criticalActivity_pos]

theorem BoundaryArc.norm_weight (A : BoundaryArc D) : ‖A.weight‖=PolynomialVacuumBridge.Corridor.criticalActivity^A.word.length := by
  simp [BoundaryArc.weight,norm_pow,norm_zpow]
end PolynomialVacuumCylinder

end OAI
