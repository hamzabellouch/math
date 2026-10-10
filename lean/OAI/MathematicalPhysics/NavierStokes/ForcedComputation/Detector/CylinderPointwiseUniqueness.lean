import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderEnergyUniqueness

namespace OAI

/-! Zero energy on one vertical period determines a continuous periodic
field everywhere, including the boundary of the chosen period. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set

theorem cylinderMeasure_eq_restrict : cylinderMeasure =
    volume.restrict ((univ : Set Plane) ×ˢ Icc (0 : ℝ) 1) := by
  rw [Measure.volume_eq_prod]
  simpa only [cylinderMeasure, verticalPeriodMeasure, Measure.restrict_univ] using
    (Measure.prod_restrict (μ := (volume : Measure Plane)) (ν := (volume : Measure ℝ))
      univ (Icc (0 : ℝ) 1))

theorem cylinder_slab_closure_interior :
    closure (interior ((univ : Set Plane) ×ˢ Icc (0 : ℝ) 1)) =
      (univ : Set Plane) ×ˢ Icc (0 : ℝ) 1 := by
  rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq,
    closure_univ, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]

theorem continuous_atHeight : Continuous (fun y : Plane × ℝ => atHeight y.1 y.2) := by
  apply continuous_pi
  intro j
  fin_cases j <;> dsimp [atHeight] <;> fun_prop

theorem cylinder_periodic_field_zero_of_energy_zero {W : Space → Space}
    (hW : Continuous W) (hp : VerticallyPeriodic W)
    (hi : Integrable (fun y => dot (W (atHeight y.1 y.2)) (W (atHeight y.1 y.2)))
      cylinderMeasure)
    (hE : (∫ y, dot (W (atHeight y.1 y.2)) (W (atHeight y.1 y.2))
      ∂cylinderMeasure) = 0) : ∀ x, W x = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun y : Plane × ℝ => dot_self_nonneg (W (atHeight y.1 y.2))))
    hi).mp hE
  rw [cylinderMeasure_eq_restrict] at hae
  have hcont := dot_continuous (hW.comp continuous_atHeight) (hW.comp continuous_atHeight)
  have he := Measure.eqOn_of_ae_eq hae hcont.continuousOn continuousOn_const
    (by rw [cylinder_slab_closure_interior])
  have hz (X : Plane) (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : W (atHeight X z) = 0 := by
    have hh : dot (W (atHeight X z)) (W (atHeight X z)) = 0 := he (show (X,z) ∈ (univ : Set Plane) ×ˢ Icc (0 : ℝ) 1 from ⟨mem_univ X, hz⟩)
    have hn := norm_sq_le_dot_self (W (atHeight X z))
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (W (atHeight X z))])
  intro x
  have hx : x = atHeight (horizontal x) (Int.fract (x 2)) +
      (⌊x 2⌋ : ℝ) • basis 2 := by
    ext j
    fin_cases j <;>
      simp [atHeight, horizontal, basis, Int.fract_add_floor]
  calc
    W x = W (atHeight (horizontal x) (Int.fract (x 2)) + (⌊x 2⌋ : ℝ) • basis 2) :=
      congrArg W hx
    _ = W (atHeight (horizontal x) (Int.fract (x 2))) := hp _ _
    _ = 0 := hz _ _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem cylinder_classical_velocity_unique (hI : CylinderLocalEnergyIdentity)
    {ν : ℝ} (hν : 0 < ν) {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q) :
    ∀ t, 0 ≤ t → ∀ x, u (t,x) = v (t,x) := by
  intro t ht x
  have hs : Continuous (fun x => u (t,x) - v (t,x)) :=
    (hu.regularity.spatial_u t ht).continuous.sub (hv.regularity.spatial_u t ht).continuous
  have hp : VerticallyPeriodic (fun x => u (t,x) - v (t,x)) := by
    intro y n
    exact congrArg₂ (· - ·) (hu.periodic_u t ht y n) (hv.periodic_u t ht y n)
  exact sub_eq_zero.mp (cylinder_periodic_field_zero_of_energy_zero hs hp
    (hu.difference_energy_integrable hv ht) (hu.difference_energy_zero hI hν hv ht) x)

end ForcedComputation.VelocityDetector

end

end OAI
