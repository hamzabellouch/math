import OAI.Combinatorics.EditApproximation.Geometry.ComparisonPhysical
import OAI.Combinatorics.EditApproximation.Geometry.ComparisonBounds

namespace OAI

/-!
Actual physical tables on the stopped comparison tree. Stopped states retain
their exact cost while the complete-tree representation carries them forward.
-/

namespace EditApproximation

open Finset

noncomputable def stoppedComparisonValue {α : Type*} (source target : List α)
    (row : TargetInterval target.length → ℝ) : ComparisonState source.length target.length → ℝ := by
  classical
  exact fun state => match state with
    | none => 0
    | some (parent, q) => if comparisonStopped source target parent q then
        stateEditCost (substring source parent.lo parent.hi) target q else row q

noncomputable def comparisonPhysicalLift {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) : ℝ := by
  classical
  exact stoppedComparisonValue source target
    (if hd : d ≤ J then fun q => table (⟨⟨d, by omega⟩, path⟩, q) else fun _ => 0)
    (comparisonFrontier source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path)

theorem stoppedComparisonValue_physical {α : Type*} {M J : ℕ} (source target : List α)
    (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (node : PhysicalNode M J) (q : TargetInterval target.length) :
    stoppedComparisonValue source target (fun r => table (node, r))
      (some (physicalSourceInterval source.length node, q)) = table (node, q) := by
  classical
  unfold stoppedComparisonValue
  dsimp only
  split_ifs with hstop
  · exact (hterminal node q hstop).symm
  · rfl

theorem comparisonPhysicalLift_root {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (rootQ : TargetInterval target.length) :
    comparisonPhysicalLift source target hM P hP table rootQ 0 PUnit.unit =
      table (⟨⟨0, by omega⟩, PUnit.unit⟩, rootQ) := by
  classical
  unfold comparisonPhysicalLift
  rw [dite_eq_left (Nat.zero_le J)]
  exact stoppedComparisonValue_physical source target table hterminal _ rootQ

theorem comparisonPhysicalLift_step_active {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (rootQ : TargetInterval target.length) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval target.length)
    (hfrontier : comparisonFrontier source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) node.1.val node.2 =
        some (physicalSourceInterval source.length node, q))
    (hactive : ¬ comparisonStopped source target (physicalSourceInterval source.length node) q)
    (i : Fin M) :
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      unfold comparisonStopped at hactive
      omega
    comparisonPhysicalLift source target hM P hP table rootQ (node.1.val + 1) (node.2, i) =
      table (physicalChild node hbelow i,
        comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc i) := by
  classical
  dsimp only
  unfold comparisonPhysicalLift
  rw [dite_eq_left (by omega : node.1.val + 1 ≤ J)]
  change stoppedComparisonValue source target _
    (comparisonStep source target hM P hP
      (comparisonFrontier source target hM P hP _ node.1.val node.2) i) = _
  rw [hfrontier]
  simp only [comparisonStep, dite_eq_right hactive]
  exact stoppedComparisonValue_physical source target table hterminal (physicalChild node hbelow i) _

theorem stoppedComparisonValue_step_stopped {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (row : Fin M → TargetInterval target.length → ℝ)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hstop : comparisonStopped source target parent q) :
    (∑ i, stoppedComparisonValue source target (row i)
      (comparisonStep source target hM P hP (some (parent, q)) i)) =
        stateEditCost (substring source parent.lo parent.hi) target q := by
  classical
  have hpoint (i : Fin M) : stoppedComparisonValue source target (row i)
      (comparisonStep source target hM P hP (some (parent, q)) i) =
        if i = ⟨0, hM⟩ then (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) else 0 := by
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [stoppedComparisonValue, ite_eq_left hstop]
  simp_rw [hpoint]
  simp

theorem comparisonPhysicalLift_terminal {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ) (rootQ : TargetInterval target.length)
    (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M J) :
    comparisonPhysicalLift source target hM P hP table rootQ J path =
      comparisonStateCost source target (comparisonFrontier source target hM P hP
        (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J path) := by
  classical
  unfold comparisonPhysicalLift
  generalize heq : comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J path = state
  cases state with
  | none => rfl
  | some state =>
    rcases state with ⟨parent, q⟩
    have hstop := comparison_frontier_terminal source target hM P hP
      (sourceIntervalAt M source.length 0 PUnit.unit) rootQ J hcapacity path parent q heq
    simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateCost]

end EditApproximation

end OAI
