import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.NestedSeparatedNets

namespace OAI

/-!
The parent map chooses a covering net point, preferring a point within half the separation radius.
Separation makes this preferred choice unique.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def SeparatedCover.parent {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (x : E) : E := by
  classical
  by_cases h : ∃ z ∈ N.points, dist (x : X) z < r / 2
  · exact ⟨h.choose, N.subset h.choose_spec.1⟩
  · exact ⟨(N.covers x x.property).choose, N.subset (N.covers x x.property).choose_spec.1⟩

theorem SeparatedCover.parent_mem {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (x : E) : (N.parent x : X) ∈ N.points := by
  classical
  unfold SeparatedCover.parent
  split_ifs with h
  · exact h.choose_spec.1
  · exact (N.covers x x.property).choose_spec.1

theorem SeparatedCover.parent_dist {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (hr : 0 < r) (x : E) : dist (x : X) (N.parent x : X) < r := by
  classical
  unfold SeparatedCover.parent
  split_ifs with h
  · exact h.choose_spec.2.trans (by linarith)
  · exact (N.covers x x.property).choose_spec.2

theorem SeparatedCover.parent_forced {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (x : E) (z : X) (hz : z ∈ N.points)
    (hxz : dist (x : X) z < r / 2) : (N.parent x : X) = z := by
  classical
  have h : ∃ y ∈ N.points, dist (x : X) y < r / 2 := ⟨z, hz, hxz⟩
  have hp : dist (x : X) (N.parent x : X) < r / 2 := by
    unfold SeparatedCover.parent
    rw [dite_eq_left h]
    exact h.choose_spec.2
  by_contra hne
  have hsep := N.separated (N.parent_mem x) hz hne
  have ht := dist_triangle (N.parent x : X) (x : X) z
  rw [dist_comm (N.parent x : X) (x : X)] at ht
  linarith

theorem SeparatedCover.parent_self {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (hr : 0 < r) (x : E) (hx : (x : X) ∈ N.points) :
    N.parent x = x := by
  apply Subtype.ext
  exact N.parent_forced x x hx (by rw [dist_self]; positivity)

end

end RieszRectifiability

end OAI
