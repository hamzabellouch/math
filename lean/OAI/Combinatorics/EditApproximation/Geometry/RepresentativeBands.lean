import OAI.Combinatorics.EditApproximation.Refinement.ComputedBands
import OAI.Combinatorics.EditApproximation.Geometry.PrefixComparison
import OAI.Combinatorics.EditApproximation.Geometry.InitialCones
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The actual rational wide minimum, computed velocity and representative band. -/

namespace EditApproximation

open Finset



theorem rationalEndpointActionValue_cast {ny M : ℕ} (r : TargetInterval ny)
    (states : Fin M → TargetInterval ny) (child : Fin M → TargetInterval ny → ℚ) :
    (rationalEndpointActionValue r states child : ℝ) =
      endpointActionValue r states (fun i s => (child i s : ℝ)) := by
  simp only [rationalEndpointActionValue, endpointActionValue, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_sum]



theorem rationalWideActionMinimum_cast {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℚ) :
    (rationalWideActionMinimum parent r b P hnonempty child : ℝ) =
      wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ)) := by
  rw [rationalWideActionMinimum, rationalMinimum_cast]
  simp only [wideActionMinimum, rationalEndpointActionValue_cast, List.map_map, Function.comp_def]

theorem wideActionMinimum_lower {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (b P : ℕ)
    (hnonempty : wideActionList M parent r b P ≠ []) (a : ℝ) (ha : 1 ≤ a)
    (child : Fin M → TargetInterval target.length → ℝ)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          child i s) :
    max ((stateEditCost (substring source parent.lo parent.hi) target r : ℝ) / a)
      |stateLengthGap (substring source parent.lo parent.hi) target r| ≤
        wideActionMinimum parent r b P hnonempty child := by
  have hlower (states : Fin M → TargetInterval target.length) :
      max ((stateEditCost (substring source parent.lo parent.hi) target r : ℝ) / a)
        |stateLengthGap (substring source parent.lo parent.hi) target r| ≤ endpointActionValue r states child :=
    actual_endpoint_action_lower source target hM parent r states a ha child
      (fun i => (le_max_left _ _).trans (hchild i (states i)))
      (fun i => (le_max_right _ _).trans (hchild i (states i)))
  apply (le_finiteMinimum_iff _ _ _).2
  refine ⟨hlower _, ?_⟩
  intro value hvalue
  obtain ⟨states, hs, rfl⟩ := List.mem_map.mp hvalue
  exact hlower states



end EditApproximation

end OAI
