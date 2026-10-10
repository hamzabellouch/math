import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderEnergyDerivative
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderViscosity

namespace OAI

/-! Subtraction of the two classical Navier–Stokes equations, in the
ordering used by the localized difference-energy identity. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CylinderLocalCalculus
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

theorem gradient_sub {p q : Space → ℝ} (hp : Differentiable ℝ p)
    (hq : Differentiable ℝ q) (x : Space) :
    ShearFlows.gradient (fun y => p y - q y) x =
      ShearFlows.gradient p x - ShearFlows.gradient q x := by
  ext j
  simp only [ShearFlows.gradient, fderiv_fun_sub (hp x) (hq x),
    sub_apply, Pi.sub_apply]

theorem advection_difference {U V : Space → Space}
    (hU : Differentiable ℝ U) (hV : Differentiable ℝ V) (x : Space) :
    advection U x - advection V x =
      fderiv ℝ U x (U x - V x) + fderiv ℝ (fun y => U y - V y) x (V x) := by
  simp only [advection, fderiv_fun_sub (hU x) (hV x),
    sub_apply, map_sub]
  abel

theorem cylinder_difference_equation {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    initialTimeDerivative u t x - initialTimeDerivative v t x =
      -ShearFlows.gradient (fun y => p (t,y) - q (t,y)) x +
        ν • laplacian (cylinderDifference u v t) x -
        fderiv ℝ (fun y => u (t,y)) x (cylinderDifference u v t x) -
        fderiv ℝ (cylinderDifference u v t) x (v (t,x)) := by
  have hU := hu.regularity.spatial_u t ht
  have hV := hv.regularity.spatial_u t ht
  have hP := (hu.regularity.spatial_p t ht).differentiable (by norm_num)
  have hQ := (hv.regularity.spatial_p t ht).differentiable (by norm_num)
  have hd := congrArg₂ (· - ·) (hu.equation t ht x) (hv.equation t ht x)
  have ha := advection_difference (hU.differentiable (by norm_num))
    (hV.differentiable (by norm_num)) x
  unfold cylinderDifference
  rw [gradient_sub hP hQ, laplacian_sub hU hV, smul_sub]
  linear_combination hd - ha

end ForcedComputation.VelocityDetector.CylinderLocalCalculus

end

end OAI
