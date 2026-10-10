import OAI.MeasureTheory.Falconer.Radial.FiniteRadialContinuity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem continuousAt_sourceRadialUnit_center (x y : Plane) (hy : y ≠ x) :
    ContinuousAt (fun z => sourceRadialUnit z y) x := by
  rw [ContinuousAt, tendsto_subtype_rng]
  change Tendsto (fun z => sourceRadialVector z y) (𝓝 x) (𝓝 (sourceRadialVector x y))
  rw [show sourceRadialVector x y = ‖y-x‖⁻¹ • (y-x) by simp [sourceRadialVector,hy]]
  have hd : ContinuousAt (fun z : Plane => y-z) x := (continuous_const.sub continuous_id).continuousAt
  have h := (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))).smul hd
  apply h.congr'
  have hne : ∀ᶠ z in 𝓝 x, z ≠ y := isClosed_singleton.isOpen_compl.mem_nhds hy.symm
  filter_upwards [hne] with z hz
  simp [sourceRadialVector, hz.symm]

theorem continuous_atomless_radial_test (α : Measure Plane) [IsFiniteMeasure α]
    [NullSingletonClass α] (F : BoundedContinuousFunction UnitCircle ℝ) :
    Continuous (fun x => ∫ ω, F ω ∂α.map (sourceRadialUnit x)) := by
  simp_rw [integral_map (measurable_sourceRadialUnit _).aemeasurable F.continuous.aestronglyMeasurable]
  rw [continuous_iff_continuousAt]
  intro x
  apply continuousAt_of_dominated (bound := fun _ : Plane => ‖F‖)
  · exact Eventually.of_forall (fun z =>
      (F.continuous.measurable.comp (measurable_sourceRadialUnit z)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun z => Eventually.of_forall (fun y => F.norm_coe_le_norm _))
  · exact integrable_const _
  · filter_upwards [(show ∀ᵐ y ∂α, y ≠ x from by rw [ae_iff]; simp)] with y hy
    exact F.continuous.continuousAt.comp (continuousAt_sourceRadialUnit_center x y hy)

theorem sourceDensityNorm_atomless_radial_lowerSemicontinuous (α : Measure Plane)
    [IsFiniteMeasure α] [NullSingletonClass α] {p q : ℝ} (hpq : p.HolderConjugate q) :
    LowerSemicontinuous (fun x => sourceDensityNorm p (α.map (sourceRadialUnit x))) := by
  simp_rw [← sourceTestNorm_eq_densityNorm _ hpq]
  exact sourceTestNorm_lowerSemicontinuous _ _ (continuous_atomless_radial_test α)

end PlanarFalconer

end OAI
