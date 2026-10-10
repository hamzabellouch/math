import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace OAI

noncomputable section

namespace Invariant233.WeakConvergenceAEContinuous

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

theorem tendsto_map_of_ae_continuous
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : X → Y} (hf : Measurable f)
    (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x) :
    Tendsto (fun j => (μs j).map f) atTop
      (𝓝 (μ.map f)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  have heq : (μ : Measure X) (closure (f ⁻¹' F)) = (μ : Measure X) (f ⁻¹' F) := by
    apply measure_congr
    filter_upwards [hc] with x hx
    apply propext
    constructor
    · intro h
      have hfreq : ∃ᶠ y in 𝓝 x, f y ∈ F := mem_closure_iff_frequently.mp h
      exact hF.mem_of_frequently_of_tendsto hfreq hx
    · intro h
      exact subset_closure h
  simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk,
    Measure.map_apply hf hF.measurableSet]
  calc
    limsup (fun j => (μs j : Measure X) (f ⁻¹' F)) atTop ≤
        limsup (fun j => (μs j : Measure X) (closure (f ⁻¹' F))) atTop :=
      limsup_le_limsup (Eventually.of_forall (fun _ => measure_mono subset_closure))
    _ ≤ (μ : Measure X) (closure (f ⁻¹' F)) :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closure
    _ = (μ : Measure X) (f ⁻¹' F) := heq

theorem tendsto_integral_of_ae_continuous
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : X → ℝ} (hf : Measurable f)
    (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    Tendsto (fun j => ∫ x, f x ∂(μs j : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  let g : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max (-B) (min B x)) (by fun_prop) B (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)
  have hgf : ∀ x, g (f x) = f x := by
    intro x
    change max (-B) (min B (f x)) = f x
    rw [min_eq_right (abs_le.mp (hb x)).2, max_eq_right (abs_le.mp (hb x)).1]
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_map_of_ae_continuous hμ hf hc)) g
  have hmap (ν : ProbabilityMeasure X) :
      (∫ y, g y ∂(ν.map f : Measure ℝ)) = ∫ x, f x ∂(ν : Measure X) := by
    change (∫ y, g y ∂Measure.map f (ν : Measure X)) = _
    rw [integral_map hf.aemeasurable g.continuous.aestronglyMeasurable]
    simp only [hgf]
  simpa only [hmap] using h

end Invariant233.WeakConvergenceAEContinuous

end

end OAI
