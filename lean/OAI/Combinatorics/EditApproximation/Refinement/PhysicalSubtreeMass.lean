import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSubtree
import OAI.Combinatorics.EditApproximation.Refinement.StageTerminal

namespace OAI

/-! Actual original-table warmup masses below an arbitrary physical node. -/

namespace EditApproximation

open Finset

section Warmup

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (root : PhysicalNode M J) (rootQ : TargetInterval target.length)

/-- The comparison mass is the actual averaged warmup at active states and
true cost at carried stopped states. -/
noncomputable def subtreeComparisonMass (d : ℕ) (path : TreeLayer M d) : ℝ :=
  comparisonSubtreeLift source target hM P hP
    (fun state => (stageWarmupMass source target U N P F A T state : ℝ)) root rootQ d path

noncomputable def subtreeComparisonEnergy (d : ℕ) (path : TreeLayer M d) : ℝ :=
  (comparisonStateGap source target (comparisonFrontier source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) d path)) ^ 2 /
      subtreeComparisonMass source target hM U N P F A hP T root rootQ d path

include hsize hF hA hseed hT in
 theorem subtreeComparisonMass_bounds (d : ℕ) (path : TreeLayer M d) :
    0 ≤ subtreeComparisonMass source target hM U N P F A hP T root rootQ d path ∧
      subtreeComparisonMass source target hM U N P F A hP T root rootQ d path ≤
        2 * F * comparisonStateCost source target (comparisonFrontier source target hM P hP
          (some (physicalSourceInterval source.length root, rootQ)) d path) := by
  exact comparisonSubtreeLift_bounds source target hM P hP F (by exact_mod_cast hF) _
    (fun state => by
      have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT state
      have hlower := ((le_max_right _ _).trans h.1).trans (Rat.cast_le.mpr h.2.1)
      have hupper : (stageWarmupMass source target U N P F A T state : ℝ) ≤
          ((2 * F * stateEditCost (physicalSource source state.1) target state.2 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (h.2.2.1.trans h.2.2.2)
      exact ⟨(abs_nonneg _).trans hlower, by simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hupper⟩)
    root rootQ d path

include hsize hF hA hseed hT in
 theorem subtreeComparisonEnergy_bounds (d : ℕ) (hd : root.1.val + d ≤ J) (path : TreeLayer M d) :
    0 ≤ subtreeComparisonEnergy source target hM U N P F A hP T root rootQ d path ∧
      subtreeComparisonEnergy source target hM U N P F A hP T root rootQ d path ≤
        subtreeComparisonMass source target hM U N P F A hP T root rootQ d path := by
  apply gap_energy_bounds
  exact comparisonSubtreeLift_gap source target hM P hP _
    (fun state => by
      have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT state
      exact ((le_max_right _ _).trans h.1).trans (Rat.cast_le.mpr h.2.1)) root rootQ d hd path

include hsize hF hA hseed hT in
 theorem subtreeComparisonMass_root :
    subtreeComparisonMass source target hM U N P F A hP T root rootQ 0 PUnit.unit =
      stageWarmupMass source target U N P F A T (root, rootQ) := by
  exact comparisonSubtreeLift_root source target hM P hP _
    (fun node q hstop => by
      exact_mod_cast stageWarmupMass_at_stopped source target hM U N P F A hsize hP hF hA hseed
        T hT node q hstop) root rootQ

 theorem subtreeComparisonMass_terminal (K : ℕ) (hheight : root.1.val + K = J) (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M K) :
    subtreeComparisonMass source target hM U N P F A hP T root rootQ K path =
      comparisonStateCost source target (comparisonFrontier source target hM P hP
        (some (physicalSourceInterval source.length root, rootQ)) K path) := by
  exact comparisonSubtreeLift_terminal source target hM P hP _ root rootQ K hheight hcapacity path

include hsize hF hA hseed hT in
 theorem subtreeComparisonEnergy_telescope (K : ℕ) (hheight : root.1.val + K = J) (hcapacity : source.length ≤ M ^ J)
    (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ d ∈ range K, ∑ path : TreeLayer M d,
      ((∑ i : Fin M, subtreeComparisonEnergy source target hM U N P F A hP T root rootQ (d + 1) (path, i)) -
        subtreeComparisonEnergy source target hM U N P F A hP T root rootQ d path)) ≤
      2 * comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
  have htel := tree_frontier_telescope M K (subtreeComparisonEnergy source target hM U N P F A hP T root rootQ)
  have heq : (∑ d ∈ range K, ∑ path : TreeLayer M d,
      ((∑ i : Fin M, subtreeComparisonEnergy source target hM U N P F A hP T root rootQ (d + 1) (path, i)) -
        subtreeComparisonEnergy source target hM U N P F A hP T root rootQ d path)) =
      (∑ path : TreeLayer M K, subtreeComparisonEnergy source target hM U N P F A hP T root rootQ K path) -
        subtreeComparisonEnergy source target hM U N P F A hP T root rootQ 0 PUnit.unit := by
    have h := congrArg Neg.neg htel
    simp only [← sum_neg_distrib, neg_sub] at h
    exact h
  rw [heq]
  have hroot := (subtreeComparisonEnergy_bounds source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
    0 (by omega) PUnit.unit).1
  have hterminal := sum_le_sum (fun path (_ : path ∈ (univ : Finset (TreeLayer M K))) =>
    (subtreeComparisonEnergy_bounds source target hM U N P F A hsize hP hF hA hseed T hT root rootQ K (by omega) path).2)
  simp_rw [subtreeComparisonMass_terminal source target hM U N P F A hP T root rootQ K hheight hcapacity] at hterminal
  have hcost := comparison_frontier_cost_le_twice source target hM P hP
    (some (physicalSourceInterval source.length root, rootQ)) K K le_rfl hsmall
  linarith only [hroot, hterminal, hcost]

local notation "mass" => subtreeComparisonMass source target hM U N P F A hP T root rootQ
local notation "energy" => subtreeComparisonEnergy source target hM U N P F A hP T root rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

 theorem subtreeComparisonMass_step_stopped (d : ℕ) (path : TreeLayer M d)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    (∑ i : Fin M, mass (d + 1) (path, i)) = mass d path := by
  classical
  unfold subtreeComparisonMass comparisonSubtreeLift
  have hpoint (i : Fin M) :
      stoppedComparisonValue source target
        (if hd : root.1.val + (d + 1) ≤ J then fun q => (stageWarmupMass source target U N P F A T
          (physicalSubtreeNode root (d + 1) (path, i) hd, q) : ℝ) else fun _ => 0)
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

 theorem subtreeComparisonEnergy_step_stopped (d : ℕ) (path : TreeLayer M d)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    (∑ i : Fin M, energy (d + 1) (path, i)) = energy d path := by
  classical
  unfold subtreeComparisonEnergy subtreeComparisonMass comparisonSubtreeLift
  have hpoint (i : Fin M) :
      (comparisonStateGap source target (frontier (d + 1) (path, i))) ^ 2 /
        stoppedComparisonValue source target
          (if hd : root.1.val + (d + 1) ≤ J then fun q => (stageWarmupMass source target U N P F A T
            (physicalSubtreeNode root (d + 1) (path, i) hd, q) : ℝ) else fun _ => 0)
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

 theorem subtreeComparison_step_none (d : ℕ) (path : TreeLayer M d) (heq : frontier d path = none) :
    mass d path = 0 ∧ (∑ i : Fin M, mass (d + 1) (path, i)) = 0 ∧
      energy d path = 0 ∧ (∑ i : Fin M, energy (d + 1) (path, i)) = 0 := by
  have hnext (i : Fin M) : frontier (d + 1) (path, i) = none := by
    change comparisonStep source target hM P hP (frontier d path) i = none
    rw [heq]
    rfl
  simp only [subtreeComparisonEnergy, subtreeComparisonMass, comparisonSubtreeLift, heq, hnext,
    comparisonStateGap, stoppedComparisonValue, zero_pow (by decide : 2 ≠ 0), zero_div,
    sum_const_zero, and_self]

include hsize hF hA hseed hT in
 theorem subtreeComparisonMass_step_active (d : ℕ) (path : TreeLayer M d)
    (hd : root.1.val + d < J) (q : TargetInterval target.length)
    (heq : frontier d path = some (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le)) q)
    (i : Fin M) :
    let node := physicalSubtreeNode root d path hd.le
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    mass (d + 1) (path, i) = stageWarmupMass source target U N P F A T
      (physicalChild node hd i, comparisonChildren source target hM P hP
        (physicalSourceInterval source.length node) q hc i) := by
  exact comparisonSubtreeLift_step_active source target hM P hP _
    (fun node q hstop => by
      exact_mod_cast stageWarmupMass_at_stopped source target hM U N P F A hsize hP hF hA hseed
        T hT node q hstop) root rootQ d path hd q heq hactive i

include hsize hF hA hseed hT in
 theorem subtreeComparisonEnergy_step_active (d : ℕ) (path : TreeLayer M d)
    (hd : root.1.val + d < J) (q : TargetInterval target.length)
    (heq : frontier d path = some (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le)) q)
    (i : Fin M) :
    let node := physicalSubtreeNode root d path hd.le
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    let childQ := comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc i
    energy (d + 1) (path, i) =
      (stateLengthGap (physicalSource source (physicalChild node hd i)) target childQ) ^ 2 /
        (stageWarmupMass source target U N P F A T (physicalChild node hd i, childQ) : ℝ) := by
  dsimp only
  unfold subtreeComparisonEnergy
  rw [subtreeComparisonMass_step_active source target hM U N P F A hsize hP hF hA hseed T hT root rootQ
    d path hd q heq hactive i]
  change (comparisonStateGap source target (comparisonStep source target hM P hP
    (frontier d path) i)) ^ 2 / _ = _
  rw [heq]
  simp only [comparisonStep, dite_eq_right hactive, comparisonStateGap]
  rfl

end Warmup

end EditApproximation

end OAI
