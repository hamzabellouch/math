import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactWeakConvergence
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxBoundary

namespace OAI

/-!
Compact-test convergence to a coordinate-plane measure yields weak convergence of finite measures
on bounded projection regions, using compact closures and null frontiers.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem boundedProjectionFiniteMeasure_tendsto {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ (coordinatePlaneMeasure e)) (H : ℕ) :
    Tendsto (fun j => boundedProjectionFiniteMeasure (μ j) π (e 0) K H) atTop
      (𝓝 (boxPlaneFiniteMeasure (exhaustionBox ι H) e)) := by
  let : IsFiniteMeasureOnCompacts (coordinatePlaneMeasure e) :=
    coordinatePlaneMeasure_finite_on_compacts e π he.continuous.measurable Q hπ hleft
  let s := boundedProjectionRegion π (e 0) K H
  have hs : MeasurableSet s := (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet
  have hc : IsCompact (closure s) := boundedProjectionRegion_compact_closure π (e 0) K H
  have h := compactTestConvergence_restrict_tendsto μ (coordinatePlaneMeasure e) hlocal s hs hc
    (boundedProjectionRegion_null_frontier e π K he hπ.continuous hleft H)
  have heq : relativelyCompactFiniteMeasure (coordinatePlaneMeasure e) s hc =
      boxPlaneFiniteMeasure (exhaustionBox ι H) e := by
    apply Subtype.ext
    exact coordinatePlaneMeasure_restrict_boundedRegion e π K he hπ.continuous hleft H
  rw [heq] at h
  exact h

theorem coordinatePlaneMeasure_ae_section {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e) :
    ∀ᵐ x ∂coordinatePlaneMeasure e, e (π x) = x := by
  apply (ae_map_iff he.measurable.aemeasurable
    (isClosed_eq (he.comp hπ) continuous_id).measurableSet).mpr
  exact Filter.Eventually.of_forall (fun u => congrArg e (hleft u))

theorem projectionHeight_lipschitz {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) :
    LipschitzWith (1 + K * Q) (fun x => dist x (e (π x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have heπ := (he.comp hπ).dist_le_mul x y
  calc
    dist (dist x (e (π x))) (dist y (e (π y))) ≤ dist x y + dist (e (π x)) (e (π y)) :=
      dist_dist_dist_le _ _ _ _
    _ ≤ dist x y + ((K : ℝ) * Q) * dist x y := by
      simpa only [Function.comp_apply, NNReal.coe_mul] using! add_le_add (le_refl (dist x y)) heπ
    _ = ((1 + K * Q : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one]
      ring

end

end RieszRectifiability

end OAI
