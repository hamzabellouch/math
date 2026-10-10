import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmup
import OAI.Combinatorics.EditApproximation.Geometry.RepresentativeBands

namespace OAI

/-! Averaging the actual physical wide Bellman recurrence bounds its exact Z slack. -/

namespace EditApproximation

open Finset

theorem physicalWarmup_average_wide_slack {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J)
    (hbelow : node.1.val < J) (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (q r : TargetInterval target.length) (b : ℕ)
    (hrep : (b, r) ∈ representatives node)
    (hnonempty : wideActionList M (physicalSourceInterval source.length node) r b P ≠ [])
    (hfinal : 0 ≤ physicalWarmup source target P L initial representatives T (node, q)) :
    physicalWarmupAverage source target P L initial representatives T (node, q) -
      wideActionMinimum (physicalSourceInterval source.length node) r b P hnonempty
        (fun i s => physicalWarmupAverage source target P L initial representatives T
          (physicalChild node hbelow i, s)) ≤
      L * targetEndpointDistance q r + initial (node, q) / T := by
  let child := fun i s => physicalWarmupAverage source target P L initial representatives T
    (physicalChild node hbelow i, s)
  let parent := physicalWarmupAverage source target P L initial representatives T (node, q)
  have hTr : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hcorrection : (initial (node, q) -
      physicalWarmup source target P L initial representatives T (node, q)) / T ≤
      initial (node, q) / T :=
    div_le_div_of_nonneg_right (sub_le_self _ hfinal) hTr
  have haction (states : Fin M → TargetInterval target.length)
      (hstates : states ∈ wideActionList M (physicalSourceInterval source.length node) r b P) :
      parent - L * targetEndpointDistance q r - initial (node, q) / T ≤
        endpointActionValue r states child := by
    have h := physicalWarmup_average_action_bound source target P L initial representatives
      T hT node hbelow hleaf q r b hrep states hstates
    dsimp only [parent, child, endpointActionValue]
    linarith only [h, hcorrection]
  have hlower : parent - L * targetEndpointDistance q r - initial (node, q) / T ≤
      wideActionMinimum (physicalSourceInterval source.length node) r b P hnonempty child := by
    apply (le_finiteMinimum_iff _ _ _).2
    constructor
    · exact haction _ (List.head_mem hnonempty)
    · intro value hvalue
      obtain ⟨states, hstates, rfl⟩ := List.mem_map.mp hvalue
      exact haction states hstates
  change parent - wideActionMinimum _ _ _ _ hnonempty child ≤ _
  linarith only [hlower]

end EditApproximation

end OAI
