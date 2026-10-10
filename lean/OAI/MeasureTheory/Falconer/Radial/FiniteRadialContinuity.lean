import OAI.MeasureTheory.Falconer.Measures.ExtendedDensityNorm

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem continuous_finite_radial_test {A B : Set Plane} (hAB : Disjoint A B)
    (α : Measure Plane) [IsFiniteMeasure α] (hα : ∀ᵐ y ∂α, y ∈ B)
    (F : BoundedContinuousFunction UnitCircle ℝ) :
    Continuous (fun x : A => ∫ ω, F ω ∂α.map (sourceRadialUnit x)) := by
  simp_rw [integral_map (measurable_sourceRadialUnit _).aemeasurable F.continuous.aestronglyMeasurable]
  apply continuous_of_dominated (bound := fun _ : Plane => ‖F‖)
  · intro x
    exact (F.continuous.measurable.comp (measurable_sourceRadialUnit x)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall (fun _ => F.norm_coe_le_norm _)
  · exact integrable_const _
  · filter_upwards [hα] with y hy
    simpa only [Function.comp_def, radialOn_eq_sourceRadialUnit] using
      F.continuous.comp (continuous_radialOn_center hAB ⟨y, hy⟩)

theorem sourceDensityNorm_radial_lowerSemicontinuous {A B : Set Plane}
    (hAB : Disjoint A B) (α : Measure Plane) [IsFiniteMeasure α]
    (hα : ∀ᵐ y ∂α, y ∈ B) {p q : ℝ} (hpq : p.HolderConjugate q) :
    LowerSemicontinuous (fun x : A => sourceDensityNorm p (α.map (sourceRadialUnit x))) := by
  simp_rw [← sourceTestNorm_eq_densityNorm _ hpq]
  exact sourceTestNorm_lowerSemicontinuous _ _ (continuous_finite_radial_test hAB α hα)

theorem sourceDensityNorm_radial_measurable {A B : Set Plane}
    (hAB : Disjoint A B) (α : Measure Plane) [IsFiniteMeasure α]
    (hα : ∀ᵐ y ∂α, y ∈ B) {p q : ℝ} (hpq : p.HolderConjugate q) :
    Measurable (fun x : A => sourceDensityNorm p (α.map (sourceRadialUnit x))) :=
  (sourceDensityNorm_radial_lowerSemicontinuous hAB α hα hpq).measurable

end PlanarFalconer

end OAI
