import OAI.MeasureTheory.Falconer.Angular.GraphTorusAngles
import OAI.MeasureTheory.Falconer.Angular.CircleRotation
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceArcLength_pair_integral_period {F : UnitCircle → UnitCircle → ℂ}
    (hF : Measurable (Function.uncurry F)) :
    (∫ u, ∫ v, F u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ θ₁ in (-Real.pi)..Real.pi, ∫ θ₂ in (-Real.pi)..Real.pi,
        F (sourceUnitDirection θ₁) (sourceUnitDirection θ₂) := by
  rw [sourceArcLength_integral_period hF.stronglyMeasurable.integral_prod_right.aestronglyMeasurable]
  apply intervalIntegral.integral_congr
  intro θ _
  exact sourceArcLength_integral_period
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem arctan_interval_integral (g : ℝ → ℂ) :
    (∫ α in (-Real.pi/2)..(Real.pi/2), g α) =
      ∫ z : ℝ, (1+z^2)⁻¹ • g (Real.arctan z) := by
  have he := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun z (_ : z ∈ (univ : Set ℝ)) => (Real.hasDerivAt_arctan' z).hasDerivWithinAt)
    Real.arctan_injective.injOn g
  have habs (z : ℝ) : |(1+z^2)⁻¹| = (1+z^2)⁻¹ := abs_of_nonneg (by positivity)
  simp only [image_univ, Real.range_arctan, Measure.restrict_univ, habs] at he
  rw [intervalIntegral.integral_of_le
    (by simpa only [neg_div] using neg_le_self (half_pos Real.pi_pos).le),
    integral_Ioc_eq_integral_Ioo]
  simpa only [neg_div] using he

theorem sourceArcLength_pair_graph_angles {F : UnitCircle → UnitCircle → ℂ}
    (hF : Measurable (Function.uncurry F))
    (hc : Continuous (fun p : ℝ × ℝ =>
      F (sourceUnitDirection p.1) (sourceUnitDirection p.2))) :
    (∫ u, ∫ v, F u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, (2/(1+z^2)) • ∫ φ in (-Real.pi)..Real.pi,
        F (sourceUnitDirection (φ+Real.arctan z))
          (sourceUnitDirection (φ-Real.arctan z)) := by
  rw [sourceArcLength_pair_integral_period hF,
    graph_torus_mean_half_difference (F := fun u v => F (sourceUnitDirection u)
      (sourceUnitDirection v)) hc
      (fun v u => congrArg (fun w => F w (sourceUnitDirection v)) (sourceUnitDirection_periodic u))
      (fun u v => congrArg (F (sourceUnitDirection u)) (sourceUnitDirection_periodic v)),
    arctan_interval_integral, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  rw [smul_smul, div_eq_mul_inv]

theorem sourceArcLength_pair_rotate_right (axis : ℝ)
    {F : UnitCircle → UnitCircle → ℂ} (hF : Measurable (Function.uncurry F)) :
    (∫ u, ∫ v, F u (sourceCircleRotate axis v) ∂sourceArcLength ∂sourceArcLength) =
      ∫ u, ∫ v, F u v ∂sourceArcLength ∂sourceArcLength := by
  apply integral_congr_ae
  filter_upwards with u
  exact sourceCircleRotate_integral axis (hF.comp (measurable_const.prodMk measurable_id))

theorem sourceArcLength_pair_graph_angles_rotated (axis : ℝ)
    {F : UnitCircle → UnitCircle → ℂ}
    (hF : Measurable (Function.uncurry F))
    (hc : Continuous (fun p : ℝ × ℝ =>
      F (sourceUnitDirection p.1) (sourceUnitDirection p.2))) :
    (∫ u, ∫ v, F u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, (2/(1+z^2)) • ∫ φ in (-Real.pi)..Real.pi,
        F (sourceUnitDirection (φ+Real.arctan z))
          (sourceUnitDirection (φ-Real.arctan z+axis)) := by
  rw [← sourceArcLength_pair_rotate_right axis hF]
  have hm : Measurable (fun p : UnitCircle × UnitCircle => F p.1 (sourceCircleRotate axis p.2)) :=
    hF.comp (measurable_fst.prodMk
      ((sourceCircleRotate_isometry axis).continuous.measurable.comp measurable_snd))
  have hcont : Continuous (fun p : ℝ × ℝ => F (sourceUnitDirection p.1)
      (sourceCircleRotate axis (sourceUnitDirection p.2))) := by
    simp only [sourceCircleRotate_comp]
    exact hc.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  simpa only [sourceCircleRotate_comp] using
    sourceArcLength_pair_graph_angles (F := fun u v => F u (sourceCircleRotate axis v)) hm hcont

end PlanarFalconer

end OAI
