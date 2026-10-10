import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapUnpin

namespace OAI

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

lemma volume_coordinate_slices [Fintype V] (pins : Set V) (x : V) (hx : x ∉ pins)
    (K : Set (Free pins → ℝ)) (hK : MeasurableSet K) :
    volume K = ∫⁻ t : ℝ, volume {h : Free (insert x pins) → ℝ |
      (splitCoordinate pins x hx).symm (h,t) ∈ K} := by
  have he := (preserving_splitCoordinate pins x hx).symm (splitCoordinate pins x hx)
  rw [← he.measure_preimage hK.nullMeasurableSet]
  change ((volume : Measure (Free (insert x pins) → ℝ)).prod (volume : Measure ℝ))
    ((splitCoordinate pins x hx).symm ⁻¹' K) = _
  exact Measure.prod_apply_symm (hK.preimage (splitCoordinate pins x hx).symm.measurable)

lemma coordinate_restore_update (pins : Set V) (x : V) (hx : x ∉ pins) (b : V → ℝ)
    (h : Free (insert x pins) → ℝ) (t : ℝ) (y : V) :
    restore pins b ((splitCoordinate pins x hx).symm (h,t)) y =
      restore (insert x pins) (Function.update b x t) h y := by
  classical
  rw [coordinate_restore]
  by_cases hy : y = x
  · subst y
    simp [restore]
  · by_cases hp : y ∈ insert x pins <;> simp [restore, hy, hp]

lemma volume_body_coordinate [Fintype V] (G : SimpleGraph V) (pins : Set V) (b : V → ℝ)
    (x : V) (hx : x ∉ pins) :
    volume (conditionalBody G pins b) = ∫⁻ t : ℝ,
      volume (conditionalBody G (insert x pins) (Function.update b x t)) := by
  rw [volume_coordinate_slices pins x hx _ (closed_conditionalBody G pins b).measurableSet]
  apply lintegral_congr
  intro t
  congr 1
  ext h
  simp only [conditionalBody, mem_ofPred_eq, coordinate_restore_update]

end ExtremalEdges

end

end OAI
