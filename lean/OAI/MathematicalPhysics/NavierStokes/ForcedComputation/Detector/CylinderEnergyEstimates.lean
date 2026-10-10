import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderEnergySpace
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderCutoffBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularLift
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EnergyCalculus

namespace OAI

/-! Energy and boundary estimates in the full cylinder comparison class. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set Filter
open scoped Topology

theorem localizedDifferenceEnergy_nonneg (u v : Velocity) (n : ℕ) (t : ℝ) :
    0 ≤ localizedDifferenceEnergy u v n t :=
  integral_nonneg (fun y => mul_nonneg (cylinderWeight_range n y.1).1 (dot_self_nonneg _))

theorem localizedDifferenceEnergy_initial {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    (n : ℕ) : localizedDifferenceEnergy u v n 0 = 0 := by
  simp [localizedDifferenceEnergy, cylinderDifference, hu.initial, hv.initial, dot]

theorem localizedDifferenceEnergy_le {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    localizedDifferenceEnergy u v n t ≤ differenceEnergy u v t := by
  unfold localizedDifferenceEnergy differenceEnergy cylinderDifference
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun y : Plane × ℝ =>
      mul_nonneg (cylinderWeight_range n y.1).1
        (dot_self_nonneg (u (t, atHeight y.1 y.2) - v (t, atHeight y.1 y.2)))))
    (hu.difference_energy_integrable hv ht)
  filter_upwards [] with y
  exact (mul_le_mul_of_nonneg_right (cylinderWeight_range n y.1).2
    (dot_self_nonneg _)).trans_eq (one_mul _)

theorem localizedDifferenceEnergy_limit {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => localizedDifferenceEnergy u v n t) atTop
      (𝓝 (differenceEnergy u v t)) :=
  cylinderWeight_integral_limit (hu.difference_energy_integrable hv ht)

theorem localizedDifferenceEnergy_continuous (hI : CylinderLocalEnergyIdentity)
    {ν : ℝ} (hν : 0 < ν) {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    ContinuousOn (localizedDifferenceEnergy u v n) (Icc 0 T) := by
  intro t ht
  by_cases h0 : t = 0
  · subst t
    change Tendsto _ _ _
    rw [localizedDifferenceEnergy_initial hu hv]
    have hlim := (hu.difference_energy_continuous hv hT) 0 ⟨le_rfl, hT⟩
    have hE0 : differenceEnergy u v 0 = 0 := by
      simp [differenceEnergy, hu.initial, hv.initial, dot]
    rw [ContinuousWithinAt, hE0] at hlim
    apply squeeze_zero' (Eventually.of_forall (localizedDifferenceEnergy_nonneg u v n))
      _ hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact localizedDifferenceEnergy_le hu hv hs.1 n
  · have hd := hI ν hν f u v p q hu hv n t (lt_of_le_of_ne ht.1 (Ne.symm h0))
    exact hd.continuousAt.continuousWithinAt

theorem localizedDifferenceDissipation_nonneg (u v : Velocity) (n : ℕ) (t : ℝ) :
    0 ≤ localizedDifferenceDissipation u v n t := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (cylinderWeight_range n y.1).1
    (Finset.sum_nonneg (fun _ _ => dot_self_nonneg _))

theorem localizedDifferenceInteraction_bound {ν B : ℝ}
    {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hB : ∀ x, ‖fderiv ℝ (fun y => u (t,y)) x‖ ≤ B) :
    |localizedDifferenceInteraction u v n t| ≤
      (3 * B) * localizedDifferenceEnergy u v n t := by
  have hi :=
    (cylinderWeight_integrable_mul (hu.difference_energy_integrable hv ht) n).const_mul (3 * B)
  have hb := norm_integral_le_of_norm_le
    (f := fun y => cylinderWeight n y.1 *
      dot (cylinderDifference u v t (atHeight y.1 y.2))
        (fderiv ℝ (fun x => u (t,x)) (atHeight y.1 y.2)
          (cylinderDifference u v t (atHeight y.1 y.2))))
    hi (Eventually.of_forall (fun y => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cylinderWeight_range n y.1).1]
    calc
      cylinderWeight n y.1 * |dot (cylinderDifference u v t (atHeight y.1 y.2))
          (fderiv ℝ (fun x => u (t,x)) (atHeight y.1 y.2)
            (cylinderDifference u v t (atHeight y.1 y.2)))|
          ≤ cylinderWeight n y.1 * ((3 * B) *
            dot (cylinderDifference u v t (atHeight y.1 y.2))
              (cylinderDifference u v t (atHeight y.1 y.2))) := by
        apply mul_le_mul_of_nonneg_left _ (cylinderWeight_range n y.1).1
        exact (dot_linear_bound _ _).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB _) (by norm_num))
            (dot_self_nonneg _))
      _ = _ := by simp only [cylinderDifference]; ring))
  simpa only [Real.norm_eq_abs, integral_const_mul, localizedDifferenceEnergy,
    localizedDifferenceInteraction, cylinderDifference] using hb

theorem localizedDiffusionError_bound {ν L : ℝ}
    {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hL : ∀ x, |scalarLaplacian (cylinderWeight n) x| ≤ L) :
    |localizedDiffusionError u v n t| ≤ L * differenceEnergy u v t := by
  have hb := norm_integral_le_of_norm_le
    (f := fun y => scalarLaplacian (cylinderWeight n) y.1 *
      dot (cylinderDifference u v t (atHeight y.1 y.2))
        (cylinderDifference u v t (atHeight y.1 y.2)))
    ((hu.difference_energy_integrable hv ht).const_mul L)
    (Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dot_self_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hL y.1) (dot_self_nonneg _)))
  simpa only [Real.norm_eq_abs, integral_const_mul, localizedDiffusionError,
    differenceEnergy, cylinderDifference] using hb

theorem localizedTransportError_bound {ν G B : ℝ} (hG : 0 ≤ G)
    {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hg : ∀ x, ‖fderiv ℝ (cylinderWeight n) x‖ ≤ G)
    (hB : ∀ x, ‖v (t,x)‖ ≤ B) :
    |localizedTransportError u v n t| ≤ (G * B) * differenceEnergy u v t := by
  have hd (x : Space) : |fderiv ℝ (cylinderWeight n) (horizontal x)
      (horizontalLinear (v (t,x)))| ≤ G * B := by
    calc
      _ ≤ ‖fderiv ℝ (cylinderWeight n) (horizontal x)‖ *
          ‖horizontalLinear (v (t,x))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ G * B := mul_le_mul (hg _) ((horizontal_norm_le _).trans (hB x))
        (norm_nonneg _) hG
  have hb := norm_integral_le_of_norm_le
    (f := fun y => fderiv ℝ (cylinderWeight n) y.1
      (horizontalLinear (v (t,atHeight y.1 y.2))) *
        dot (cylinderDifference u v t (atHeight y.1 y.2))
          (cylinderDifference u v t (atHeight y.1 y.2)))
    ((hu.difference_energy_integrable hv ht).const_mul (G * B))
    (Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dot_self_nonneg _)]
      apply mul_le_mul_of_nonneg_right _ (dot_self_nonneg _)
      simpa only [atHeight_horizontal] using hd (atHeight y.1 y.2)))
  simpa only [Real.norm_eq_abs, integral_const_mul, localizedTransportError,
    differenceEnergy, cylinderDifference] using hb

theorem localizedPressureError_bound {ν G : ℝ} (hG : 0 ≤ G)
    {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hg : ∀ x, ‖fderiv ℝ (cylinderWeight n) x‖ ≤ G) :
    |localizedPressureError u v p q n t| ≤
      G * (pressureDifferenceEnergy p q t + differenceEnergy u v t) := by
  have hi := ((hu.pressure_difference_integrable hv ht).add
    (hu.difference_energy_integrable hv ht)).const_mul G
  have hb := norm_integral_le_of_norm_le
    (f := fun y => (p (t,atHeight y.1 y.2) - q (t,atHeight y.1 y.2)) *
      fderiv ℝ (cylinderWeight n) y.1
        (horizontalLinear (cylinderDifference u v t (atHeight y.1 y.2))))
    hi (Eventually.of_forall (fun y => by
    let W := cylinderDifference u v t (atHeight y.1 y.2)
    let P := p (t, atHeight y.1 y.2) - q (t, atHeight y.1 y.2)
    have hd : |fderiv ℝ (cylinderWeight n) y.1 (horizontalLinear W)| ≤ G * ‖W‖ := by
      simpa only [Real.norm_eq_abs, horizontalLinear_eq] using
        ((fderiv ℝ (cylinderWeight n) y.1).le_opNorm (horizontal W)).trans
          (mul_le_mul (hg _) (horizontal_norm_le W) (norm_nonneg _) hG)
    have hy : |P| * ‖W‖ ≤ P ^ 2 + dot W W := by
      nlinarith [sq_nonneg (|P| - ‖W‖), sq_abs P, norm_sq_le_dot_self W,
        sq_nonneg P, sq_nonneg ‖W‖]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |P| * |fderiv ℝ (cylinderWeight n) y.1 (horizontalLinear W)|
          ≤ |P| * (G * ‖W‖) := mul_le_mul_of_nonneg_left hd (abs_nonneg P)
      _ = G * (|P| * ‖W‖) := by ring
      _ ≤ G * (P ^ 2 + dot W W) := mul_le_mul_of_nonneg_left hy hG))
  simpa only [Real.norm_eq_abs, integral_const_mul, Pi.add_apply,
    integral_add (hu.pressure_difference_integrable hv ht)
      (hu.difference_energy_integrable hv ht), pressureDifferenceEnergy,
    localizedPressureError, differenceEnergy, cylinderDifference] using hb

end ForcedComputation.VelocityDetector

end

end OAI
