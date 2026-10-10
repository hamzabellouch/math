import OAI.Combinatorics.EditApproximation.Refinement.StageWarmup
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmupSlack
import OAI.Combinatorics.EditApproximation.Geometry.ComparisonTree

namespace OAI

/-! Actual stage masses and representatives supply the comparison-node warmup hypotheses. -/

namespace EditApproximation

theorem stageWarmupMass_child_lower {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J) (hbelow : node.1.val < J) :
    ∀ i s, max ((stateEditCost
      (substring source (sourceChild (physicalSourceInterval source.length node) i).lo
        (sourceChild (physicalSourceInterval source.length node) i).hi) target s : ℝ) /
          (refinementFactor A F : ℝ))
      |stateLengthGap (substring source (sourceChild (physicalSourceInterval source.length node) i).lo
        (sourceChild (physicalSourceInterval source.length node) i).hi) target s| ≤
      (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ) := by
  intro i s
  have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT
    (physicalChild node hbelow i, s)
  have hmass : (stageWarmup source target U N P F A T (physicalChild node hbelow i, s) : ℝ) ≤
      stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) := Rat.cast_le.mpr h.2.1
  exact h.1.trans hmass

theorem stageRounded_representative_mem {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (physicalSource source node) target q) :
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    (b, roundInterval (seedGridSpacing b P) q) ∈ stageRepresentatives source target U N P F A node := by
  have hfactor := refinementFactor_spec A F (by omega)
  have hbounds := physicalInitialTable_bounds source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed
  exact rounded_comparison_representative (physicalSource source node) target N P F
    (refinementFactor A F) (by omega) (Nat.cast_nonneg _) (by linarith only [hfactor.1])
    (fun r => stageInitial source target U N P F A (node, r))
    (fun r => (le_max_left _ _).trans (hbounds (node, r)).1)
    (fun r => (hbounds (node, r)).2) q hc (physical_state_cost_le source target N hsize (node, q))

theorem stageWarmup_comparison_slack {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (physicalSource source node) target q) :
    let parent := physicalSourceInterval source.length node
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    let r := roundInterval (seedGridSpacing b P) q
    ∀ hnonempty : wideActionList M parent r b P ≠ [],
      (stageWarmupMass source target U N P F A T (node, q) : ℝ) -
        wideActionMinimum parent r b P hnonempty
          (fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)) ≤
      (128 * (F : ℝ)) * targetEndpointDistance q r + (stageInitial source target U N P F A (node, q) : ℝ) / T := by
  dsimp only
  intro hnonempty
  have hrep := stageRounded_representative_mem source target U N P F A hsize hP hF hA hseed node q hc
  have hinvariants := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT (node, q)
  have hfinal : 0 ≤ (stageWarmup source target U N P F A T (node, q) : ℝ) :=
    (abs_nonneg _).trans ((le_max_right _ _).trans hinvariants.1)
  simp only [stageWarmup, rationalPhysicalWarmup_cast] at hfinal
  have h := physicalWarmup_average_wide_slack source target P ((128 * F : ℚ) : ℝ)
    (fun s => (stageInitial source target U N P F A s : ℝ))
    (stageRepresentatives source target U N P F A) T hT node hbelow hleaf q _ _ hrep hnonempty hfinal
  simp only [stageWarmupMass, rationalPhysicalWarmupAverage_cast]
  simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using h

end EditApproximation

end OAI
