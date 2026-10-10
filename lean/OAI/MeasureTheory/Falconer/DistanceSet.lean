import OAI.MeasureTheory.Falconer.Model
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem distanceSet_eq_image (E : Set Plane) :
    distanceSet E = (fun z : Plane × Plane => dist z.1 z.2) '' (E ×ˢ E) := by
  ext r
  constructor
  · rintro ⟨x,hx,y,hy,hr⟩
    exact ⟨(x,y), ⟨hx,hy⟩, hr⟩
  · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩,hr⟩
    exact ⟨x,hx,y,hy,hr⟩

theorem distanceSet_isCompact {E : Set Plane} (hE : IsCompact E) :
    IsCompact (distanceSet E) := by
  rw [distanceSet_eq_image]
  exact (hE.prod hE).image (continuous_fst.dist continuous_snd)

theorem distanceSet_measurable {E : Set Plane} (hE : IsCompact E) :
    MeasurableSet (distanceSet E) :=
  (distanceSet_isCompact hE).measurableSet

theorem distanceSet_nonnegative {E : Set Plane} {r : ℝ} (hr : r ∈ distanceSet E) :
    0 ≤ r := by
  obtain ⟨x,_,y,_,rfl⟩ := hr
  exact dist_nonneg

theorem zero_mem_distanceSet {E : Set Plane} (hE : E.Nonempty) :
    0 ∈ distanceSet E := by
  obtain ⟨x,hx⟩ := hE
  exact ⟨x,hx,x,hx,dist_self x⟩

theorem positive_volume_of_carried_absolutelyContinuous
    (D : Set ℝ) (τ : Measure ℝ) (hmass : 0 < τ univ)
    (hcarried : τ Dᶜ = 0) (hac : τ ≪ volume) : 0 < volume D := by
  by_contra h
  have hzero : volume D = 0 := le_antisymm (not_lt.mp h) bot_le
  have hτ : τ D = 0 := hac hzero
  have hz := measure_union_null hτ hcarried
  have : τ univ = 0 := by simpa only [union_compl_self] using hz
  exact (ne_of_gt hmass) this

theorem distanceSet_positive_of_measure (E : Set Plane) (τ : Measure ℝ)
    (hmass : 0 < τ univ) (hcarried : τ (distanceSet E)ᶜ = 0) (hac : τ ≪ volume) :
    0 < volume (distanceSet E) :=
  positive_volume_of_carried_absolutelyContinuous (distanceSet E) τ hmass hcarried hac

end PlanarFalconer

end OAI
