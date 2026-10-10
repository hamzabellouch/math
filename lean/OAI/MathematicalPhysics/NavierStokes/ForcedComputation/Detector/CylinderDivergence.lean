import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderLocalIntegration

namespace OAI

/-! The divergence theorem for a horizontally compact vector field over
one vertical period. No spatial decay hypothesis is imposed in the periodic direction. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CylinderLocalCalculus
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

theorem integral_scalarSpatialD_zero {g : Space → ℝ} (hg : ContDiff ℝ 1 g)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ x, horizontal x ∉ K → g x = 0)
    (hp : VerticallyPeriodic g) (j : Fin 3) :
    (∫ y, scalarSpatialD j g (atHeight y.1 y.2) ∂cylinderMeasure) = 0 := by
  fin_cases j
  · exact integral_horizontal_scalarD_zero hg hK hs 0
  · exact integral_horizontal_scalarD_zero hg hK hs 1
  · exact integral_vertical_scalarD_zero hg hK hs hp

theorem integral_divergence_zero {U : Space → Space} (hU : ContDiff ℝ 1 U)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ x, horizontal x ∉ K → U x = 0)
    (hp : VerticallyPeriodic U) :
    (∫ y, divergence U (atHeight y.1 y.2) ∂cylinderMeasure) = 0 := by
  have hc (j : Fin 3) : ContDiff ℝ 1 (fun x => U x j) :=
    (contDiff_apply ℝ ℝ j).comp hU
  have hz (j : Fin 3) (x : Space) (hx : horizontal x ∉ K) : U x j = 0 := by
    rw [hs x hx]
    rfl
  have hi (j : Fin 3) : Integrable
      (fun y => scalarSpatialD j (fun x => U x j) (atHeight y.1 y.2)) cylinderMeasure :=
    scalarSpatialD_cylinder_integrable (hc j) hK (hz j) j
  have he (x : Space) : divergence U x = ∑ j, scalarSpatialD j (fun x => U x j) x := by
    apply Finset.sum_congr rfl
    intro j _
    exact (fderiv_coordinate (hU.differentiable (by norm_num)) x (basis j) j).symm
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply Finset.sum_eq_zero
  intro j _
  exact integral_scalarSpatialD_zero (hc j) hK (hz j)
    (fun x n => congrFun (hp x n) j) j

end ForcedComputation.VelocityDetector.CylinderLocalCalculus

end

end OAI
