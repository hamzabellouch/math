import OAI.Combinatorics.EditApproximation.Geometry.ComparisonLiftBounds

namespace OAI

/-! Actual mass and energy identities at every kind of comparison-tree node. -/

namespace EditApproximation

open Finset

theorem stoppedComparisonEnergy_step_stopped {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (row : Fin M → TargetInterval target.length → ℝ)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hstop : comparisonStopped source target parent q) :
    (∑ i, (comparisonStateGap source target (comparisonStep source target hM P hP (some (parent, q)) i)) ^ 2 /
      stoppedComparisonValue source target (row i)
        (comparisonStep source target hM P hP (some (parent, q)) i)) =
      (stateLengthGap (substring source parent.lo parent.hi) target q) ^ 2 /
        stateEditCost (substring source parent.lo parent.hi) target q := by
  classical
  have hpoint (i : Fin M) :
      (comparisonStateGap source target (comparisonStep source target hM P hP (some (parent, q)) i)) ^ 2 /
        stoppedComparisonValue source target (row i)
          (comparisonStep source target hM P hP (some (parent, q)) i) =
      if i = ⟨0, hM⟩ then (stateLengthGap (substring source parent.lo parent.hi) target q) ^ 2 /
        stateEditCost (substring source parent.lo parent.hi) target q else 0 := by
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [comparisonStateGap, stoppedComparisonValue, ite_eq_left hstop, zero_pow
      (by decide : 2 ≠ 0), zero_div]
  simp_rw [hpoint]
  simp

section Warmup

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

local notation "mass" => stageComparisonMass source target hM U N P F A hP T rootQ
local notation "energy" => stageComparisonEnergy source target hM U N P F A hP T rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

 theorem stageComparisonMass_step_stopped (d : ℕ) (path : TreeLayer M d)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    (∑ i : Fin M, mass (d + 1) (path, i)) = mass d path := by
  classical
  unfold stageComparisonMass comparisonPhysicalLift
  have hpoint (i : Fin M) :
      stoppedComparisonValue source target
        (if hd : d + 1 ≤ J then fun q => (stageWarmupMass source target U N P F A T
          (⟨⟨d + 1, by omega⟩, (path, i)⟩, q) : ℝ) else fun _ => 0)
        (frontier (d + 1) (path, i)) =
      if i = ⟨0, hM⟩ then (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) else 0 := by
    change stoppedComparisonValue source target _
      (comparisonStep source target hM P hP (frontier d path) i) = _
    rw [heq]
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [stoppedComparisonValue, ite_eq_left hstop]
  simp_rw [hpoint]
  rw [heq]
  simp only [sum_ite_eq', mem_univ, ite_true, stoppedComparisonValue, ite_eq_left hstop]

 theorem stageComparisonEnergy_step_stopped (d : ℕ) (path : TreeLayer M d)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    (∑ i : Fin M, energy (d + 1) (path, i)) = energy d path := by
  classical
  unfold stageComparisonEnergy stageComparisonMass comparisonPhysicalLift
  have hpoint (i : Fin M) :
      (comparisonStateGap source target (frontier (d + 1) (path, i))) ^ 2 /
        stoppedComparisonValue source target
          (if hd : d + 1 ≤ J then fun q => (stageWarmupMass source target U N P F A T
            (⟨⟨d + 1, by omega⟩, (path, i)⟩, q) : ℝ) else fun _ => 0)
          (frontier (d + 1) (path, i)) =
      if i = ⟨0, hM⟩ then (stateLengthGap (substring source parent.lo parent.hi) target q) ^ 2 /
        stateEditCost (substring source parent.lo parent.hi) target q else 0 := by
    change (comparisonStateGap source target (comparisonStep source target hM P hP (frontier d path) i)) ^ 2 /
      stoppedComparisonValue source target _ (comparisonStep source target hM P hP (frontier d path) i) = _
    rw [heq]
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [comparisonStateGap, stoppedComparisonValue, ite_eq_left hstop,
      zero_pow (by decide : 2 ≠ 0), zero_div]
  simp_rw [hpoint]
  rw [heq]
  simp only [sum_ite_eq', mem_univ, ite_true, comparisonStateGap, stoppedComparisonValue, ite_eq_left hstop]

 theorem stageComparison_step_none (d : ℕ) (path : TreeLayer M d) (heq : frontier d path = none) :
    mass d path = 0 ∧ (∑ i : Fin M, mass (d + 1) (path, i)) = 0 ∧
      energy d path = 0 ∧ (∑ i : Fin M, energy (d + 1) (path, i)) = 0 := by
  have hnext (i : Fin M) : frontier (d + 1) (path, i) = none := by
    change comparisonStep source target hM P hP (frontier d path) i = none
    rw [heq]
    rfl
  simp only [stageComparisonEnergy, stageComparisonMass, comparisonPhysicalLift, heq, hnext,
    comparisonStateGap, stoppedComparisonValue, zero_pow (by decide : 2 ≠ 0), zero_div,
    sum_const_zero, and_self]

include hsize hF hA hseed hT in
 theorem stageComparisonMass_step_active (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval target.length)
    (heq : frontier node.1.val node.2 = some (physicalSourceInterval source.length node, q))
    (hactive : ¬ comparisonStopped source target (physicalSourceInterval source.length node) q)
    (i : Fin M) :
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      unfold comparisonStopped at hactive
      omega
    mass (node.1.val + 1) (node.2, i) = stageWarmupMass source target U N P F A T
      (physicalChild node hbelow i, comparisonChildren source target hM P hP
        (physicalSourceInterval source.length node) q hc i) := by
  exact comparisonPhysicalLift_step_active source target hM P hP _
    (fun node q hstop => by
      exact_mod_cast stageWarmupMass_at_stopped source target hM U N P F A hsize hP hF hA hseed
        T hT node q hstop) rootQ node hbelow q heq hactive i

include hsize hF hA hseed hT in
 theorem stageComparisonEnergy_step_active (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval target.length)
    (heq : frontier node.1.val node.2 = some (physicalSourceInterval source.length node, q))
    (hactive : ¬ comparisonStopped source target (physicalSourceInterval source.length node) q)
    (i : Fin M) :
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      unfold comparisonStopped at hactive
      omega
    let childQ := comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc i
    energy (node.1.val + 1) (node.2, i) =
      (stateLengthGap (physicalSource source (physicalChild node hbelow i)) target childQ) ^ 2 /
        (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, childQ) : ℝ) := by
  dsimp only
  unfold stageComparisonEnergy
  rw [stageComparisonMass_step_active source target hM U N P F A hsize hP hF hA hseed T hT rootQ
    node hbelow q heq hactive i]
  change (comparisonStateGap source target (comparisonStep source target hM P hP
    (frontier node.1.val node.2) i)) ^ 2 / _ = _
  rw [heq]
  simp only [comparisonStep, dite_eq_right hactive, comparisonStateGap]
  rfl

end Warmup

end EditApproximation

end OAI
