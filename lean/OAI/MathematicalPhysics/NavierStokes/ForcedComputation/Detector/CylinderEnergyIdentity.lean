import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderEnergyEquation

namespace OAI

/-! Discharge of the published localized energy identity in the strong
classical cylinder class used by the whole-plane detector. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory CylinderLocalCalculus
open scoped ContDiff BigOperators

theorem cylinder_energy_rate {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (2 * ∫ y, cylinderWeight n y.1 *
      dot (cylinderDifference u v t (atHeight y.1 y.2))
        (initialTimeDerivative u t (atHeight y.1 y.2) -
          initialTimeDerivative v t (atHeight y.1 y.2)) ∂cylinderMeasure) =
      -2 * ν * localizedDifferenceDissipation u v n t
        - 2 * localizedDifferenceInteraction u v n t
        + ν * localizedDiffusionError u v n t
        + localizedTransportError u v n t
        + 2 * localizedPressureError u v p q n t := by
  let W : Space → Space := cylinderDifference u v t
  let U : Space → Space := fun x => u (t,x)
  let V : Space → Space := fun x => v (t,x)
  let P : Space → ℝ := fun x => p (t,x) - q (t,x)
  let G : Space → Space := fun x => initialTimeDerivative u t x - initialTimeDerivative v t x
  let φ := cylinderWeight n
  have hU : ContDiff ℝ 2 U := hu.regularity.spatial_u t ht
  have hV : ContDiff ℝ 2 V := hv.regularity.spatial_u t ht
  have hW : ContDiff ℝ 2 W := hU.sub hV
  have hP : ContDiff ℝ 1 P := (hu.regularity.spatial_p t ht).sub (hv.regularity.spatial_p t ht)
  have hWp : VerticallyPeriodic W := by
    intro x k
    exact congrArg₂ (fun a b : Space => a - b)
      (hu.periodic_u t ht x k) (hv.periodic_u t ht x k)
  have hPp : VerticallyPeriodic P := by
    intro x k
    exact congrArg₂ (fun a b : ℝ => a - b)
      (hu.periodic_p t ht x k) (hv.periodic_p t ht x k)
  have hWdiv (x : Space) : divergence W x = 0 := by
    change divergence (fun y => U y - V y) x = 0
    rw [divergence_sub (hU.differentiable (by norm_num)) (hV.differentiable (by norm_num)),
      hu.divergence_zero t ht, hv.divergence_zero t ht, sub_self]
  have hφ := cylinderWeight_smooth n
  have hc := cylinderWeight_compactSupport n
  have hp := pressure_pairing (hφ.of_le (by simp)) hc (hW.of_le (by norm_num)) hP
    hWp hPp hWdiv
  have hν := viscosity_pairing hφ hc hW hWp
  have ha := transport_pairing (hφ.of_le (by simp)) hc (hW.of_le (by norm_num))
    (hV.of_le (by norm_num)) hWp (hv.periodic_u t ht) (hv.divergence_zero t ht)
  have hiP := weighted_integrable hφ.continuous hc
    (dot_continuous hW.continuous (gradient_continuous hP))
  have hiL := weighted_integrable hφ.continuous hc
    (dot_continuous hW.continuous (laplacian_continuous hW))
  have hiI := weighted_integrable hφ.continuous hc
    (dot_continuous hW.continuous
      ((hU.continuous_fderiv (by norm_num)).clm_apply hW.continuous))
  have hiA := weighted_integrable hφ.continuous hc
    (dot_continuous hW.continuous
      ((hW.continuous_fderiv (by norm_num)).clm_apply hV.continuous))
  have he (x : Space) : G x = -ShearFlows.gradient P x + ν • laplacian W x -
      fderiv ℝ U x (W x) - fderiv ℝ W x (V x) :=
    cylinder_difference_equation hu hv ht x
  have heInt : (∫ y, φ y.1 * dot (W (atHeight y.1 y.2)) (G (atHeight y.1 y.2))
      ∂cylinderMeasure) =
      -(∫ y, φ y.1 * dot (W (atHeight y.1 y.2)) (ShearFlows.gradient P (atHeight y.1 y.2))
        ∂cylinderMeasure) +
      ν * (∫ y, φ y.1 * dot (W (atHeight y.1 y.2)) (laplacian W (atHeight y.1 y.2))
        ∂cylinderMeasure) -
      (∫ y, φ y.1 * dot (W (atHeight y.1 y.2))
        (fderiv ℝ U (atHeight y.1 y.2) (W (atHeight y.1 y.2))) ∂cylinderMeasure) -
      (∫ y, φ y.1 * dot (W (atHeight y.1 y.2))
        (fderiv ℝ W (atHeight y.1 y.2) (V (atHeight y.1 y.2))) ∂cylinderMeasure) := by
    have heq : (fun y : Plane × ℝ => φ y.1 * dot (W (atHeight y.1 y.2))
        (G (atHeight y.1 y.2))) = (fun y =>
          -(φ y.1 * dot (W (atHeight y.1 y.2)) (ShearFlows.gradient P (atHeight y.1 y.2))) +
          ν * (φ y.1 * dot (W (atHeight y.1 y.2)) (laplacian W (atHeight y.1 y.2))) -
          φ y.1 * dot (W (atHeight y.1 y.2))
            (fderiv ℝ U (atHeight y.1 y.2) (W (atHeight y.1 y.2))) -
          φ y.1 * dot (W (atHeight y.1 y.2))
            (fderiv ℝ W (atHeight y.1 y.2) (V (atHeight y.1 y.2)))) := by
      funext y
      rw [he, dot_sub_right, dot_sub_right, dot_add_right, dot_neg_right, dot_smul_right]
      ring
    rw [heq]
    let A := fun y : Plane × ℝ => φ y.1 *
      dot (W (atHeight y.1 y.2)) (ShearFlows.gradient P (atHeight y.1 y.2))
    let B := fun y : Plane × ℝ => φ y.1 *
      dot (W (atHeight y.1 y.2)) (laplacian W (atHeight y.1 y.2))
    let C := fun y : Plane × ℝ => φ y.1 * dot (W (atHeight y.1 y.2))
      (fderiv ℝ U (atHeight y.1 y.2) (W (atHeight y.1 y.2)))
    let D := fun y : Plane × ℝ => φ y.1 * dot (W (atHeight y.1 y.2))
      (fderiv ℝ W (atHeight y.1 y.2) (V (atHeight y.1 y.2)))
    change (∫ y, -A y + ν * B y - C y - D y ∂cylinderMeasure) =
      -(∫ y, A y ∂cylinderMeasure) + ν * (∫ y, B y ∂cylinderMeasure) -
        (∫ y, C y ∂cylinderMeasure) - (∫ y, D y ∂cylinderMeasure)
    rw [integral_sub (f := fun y => -A y + ν * B y - C y) (g := D)
        ((hiP.neg.add (hiL.const_mul ν)).sub hiI) hiA,
      integral_sub (f := fun y => -A y + ν * B y) (g := C)
        (hiP.neg.add (hiL.const_mul ν)) hiI,
      integral_add (f := fun y => -A y) (g := fun y => ν * B y)
        hiP.neg (hiL.const_mul ν), integral_neg, integral_const_mul]
  change 2 * (∫ y, φ y.1 * dot (W (atHeight y.1 y.2)) (G (atHeight y.1 y.2))
    ∂cylinderMeasure) = _
  rw [heInt]
  change _ = -2 * ν * (∫ y, φ y.1 * ∑ j, dot (derivative W j (atHeight y.1 y.2))
      (derivative W j (atHeight y.1 y.2)) ∂cylinderMeasure) -
    2 * (∫ y, φ y.1 * dot (W (atHeight y.1 y.2))
      (fderiv ℝ U (atHeight y.1 y.2) (W (atHeight y.1 y.2))) ∂cylinderMeasure) +
    ν * (∫ y, scalarLaplacian φ y.1 * dot (W (atHeight y.1 y.2)) (W (atHeight y.1 y.2))
      ∂cylinderMeasure) +
    (∫ y, fderiv ℝ φ y.1 (horizontalLinear (V (atHeight y.1 y.2))) *
      dot (W (atHeight y.1 y.2)) (W (atHeight y.1 y.2)) ∂cylinderMeasure) +
    2 * (∫ y, P (atHeight y.1 y.2) *
      fderiv ℝ φ y.1 (horizontalLinear (W (atHeight y.1 y.2))) ∂cylinderMeasure)
  linear_combination ν * hν - 2 * hp - ha

theorem cylinder_local_energy_identity : CylinderLocalEnergyIdentity := by
  intro ν _hν f u v p q hu hv n t ht
  have h := localizedDifferenceEnergy_hasDerivAt hu hv n ht
  rw [cylinder_energy_rate hu hv n ht.le] at h
  exact h

end ForcedComputation.VelocityDetector

end

end OAI
