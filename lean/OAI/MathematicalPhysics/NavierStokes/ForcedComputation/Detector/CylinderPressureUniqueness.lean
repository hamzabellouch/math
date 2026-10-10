import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderPointwiseUniqueness

namespace OAI

/-! The L2 condition removes the spatially constant pressure ambiguity on
the infinite cylinder. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set
open scoped ENNReal

theorem cylinderMeasure_univ : cylinderMeasure univ = ∞ := by
  unfold cylinderMeasure
  rw [← univ_prod_univ, Measure.prod_prod,
    (measure_univ : verticalPeriodMeasure univ = 1), mul_one]
  exact measure_univ_of_isAddLeftInvariant (volume : Measure Plane)

theorem cylinder_classical_pressure_unique {ν : ℝ} {f u v : Velocity} {p : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p)
    (hv : IsCylinderClassicalSolution ν f v (fun _ => 0))
    (heq : ∀ t, 0 ≤ t → ∀ x, u (t,x) = v (t,x)) :
    ∀ t, 0 ≤ t → ∀ x, p (t,x) = 0 := by
  intro t ht
  have htime (x : Space) : initialTimeDerivative u t x = initialTimeDerivative v t x :=
    derivWithin_congr (fun s hs => heq s hs x) (heq t ht x)
  have hspace : (fun x => u (t,x)) = fun x => v (t,x) := funext (heq t ht)
  have hgrad (x : Space) : gradient (fun y => p (t,y)) x = 0 := by
    have h1 := hu.equation t ht x
    have h2 := hv.equation t ht x
    rw [htime, hspace] at h1
    rw [gradient_constant, neg_zero, zero_add] at h2
    linear_combination h1 - h2
  have hder (x : Space) : fderiv ℝ (fun y => p (t,y)) x = 0 := by
    ext w
    rw [← coordinate_trace]
    have hz (j : Fin 3) : fderiv ℝ (fun y => p (t,y)) x (basis j) = 0 :=
      congrFun (hgrad x) j
    simp [hz]
  have hconst (x : Space) : p (t,x) = p (t,0) :=
    is_const_of_fderiv_eq_zero ((hu.regularity.spatial_p t ht).differentiable (by norm_num))
      hder x 0
  have hi := (hu.pressure_h1 t ht).1.square_integrable ⟨ht, le_rfl⟩
  have hic : Integrable (fun _ : Plane × ℝ => p (t,0) ^ 2) cylinderMeasure := by
    simpa only [cylinderPullback, hconst] using hi
  have hp : p (t,0) ^ 2 = 0 := by
    rcases integrable_const_iff.mp hic with hh | hh
    · exact hh
    · have hfin := hh.measure_univ_lt_top
      rw [cylinderMeasure_univ] at hfin
      exact False.elim (lt_irrefl _ hfin)
  intro x
  rw [hconst]
  nlinarith [sq_nonneg (p (t,0))]

theorem cylinder_classical_unique (hI : CylinderLocalEnergyIdentity)
    {ν : ℝ} (hν : 0 < ν) {f v : Velocity}
    (hv : IsCylinderClassicalSolution ν f v (fun _ => 0)) :
    ∀ u p, IsCylinderClassicalSolution ν f u p →
      ∀ t, 0 ≤ t → ∀ x, u (t,x) = v (t,x) ∧ p (t,x) = 0 := by
  intro u p hu
  have heq := cylinder_classical_velocity_unique hI hν hu hv
  have hp := cylinder_classical_pressure_unique hu hv heq
  exact fun t ht x => ⟨heq t ht x, hp t ht x⟩

end ForcedComputation.VelocityDetector

end

end OAI
