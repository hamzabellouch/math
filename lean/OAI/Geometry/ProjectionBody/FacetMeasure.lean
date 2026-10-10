import OAI.Geometry.ProjectionBody.FacetCover
import Mathlib.MeasureTheory.Measure.Basic

namespace OAI

noncomputable section
open Set MeasureTheory

namespace ProjectionCounterexample

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [MeasurableSpace W]

/-- Finite additivity for shadows of visible faces. The geometric hypotheses
are explicit: the later applications must prove measurability and nullity of
the projected intersections. No facet-volume formula is assumed here. -/
theorem measure_image_halfspaceBody_eq_sum_visible
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W) (μ : Measure W)
    {u : V} (hqu : q u = 0) (hu : ∃ i, 0 < a i u)
    (hker : LinearMap.ker q = Submodule.span ℝ {u})
    (hmeas : ∀ i, MeasurableSet (q '' boundingFace a b i))
    (hnull : ∀ i j, i ≠ j →
      μ (q '' (boundingFace a b i ∩ boundingFace a b j)) = 0) :
    μ (q '' halfspaceBody a b) =
      ∑ i : {i : ι // 0 < a i u}, μ (q '' boundingFace a b i.1) := by
  classical
  rw [image_halfspaceBody_eq_visible_faces a b q hqu hu]
  have hd : Pairwise (fun i j : {i : ι // 0 < a i u} =>
      AEDisjoint μ (q '' boundingFace a b i.1) (q '' boundingFace a b j.1)) := by
    intro i j hij
    change μ ((q '' boundingFace a b i.1) ∩ (q '' boundingFace a b j.1)) = 0
    rw [image_visible_faces_inter a b q hker i.2 j.2]
    exact hnull i j (fun h => hij (Subtype.ext h))
  rw [measure_iUnion₀ hd (fun i => (hmeas i.1).nullMeasurableSet), tsum_fintype]

end ProjectionCounterexample

end

end OAI
