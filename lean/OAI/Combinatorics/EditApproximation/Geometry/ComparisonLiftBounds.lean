import OAI.Combinatorics.EditApproximation.Geometry.ComparisonLift
import OAI.Combinatorics.EditApproximation.Refinement.StageTerminal

namespace OAI

/-! Actual stopped-tree warmup masses and their energy telescope bounds. -/

namespace EditApproximation

open Finset

noncomputable def comparisonStateGap {α : Type*} (source target : List α) :
    ComparisonState source.length target.length → ℝ
  | none => 0
  | some (parent, q) => stateLengthGap (substring source parent.lo parent.hi) target q

theorem comparisonPhysicalLift_bounds {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (F : ℝ) (hF : 1 ≤ F)
    (table : PhysicalEntry M J target.length → ℝ)
    (htable : ∀ state, 0 ≤ table state ∧ table state ≤
      2 * F * stateEditCost (physicalSource source state.1) target state.2)
    (rootQ : TargetInterval target.length) (d : ℕ) (path : TreeLayer M d) :
    0 ≤ comparisonPhysicalLift source target hM P hP table rootQ d path ∧
      comparisonPhysicalLift source target hM P hP table rootQ d path ≤
        2 * F * comparisonStateCost source target (comparisonFrontier source target hM P hP
          (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path) := by
  classical
  unfold comparisonPhysicalLift
  generalize heq : comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path = state
  cases state with
  | none => simp only [stoppedComparisonValue, comparisonStateCost, mul_zero, le_refl, and_self]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateCost]
      refine ⟨Nat.cast_nonneg _, ?_⟩
      have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * F by linarith) (Nat.cast_nonneg
        (stateEditCost (substring source parent.lo parent.hi) target q))
      simpa only [one_mul] using h
    · simp only [stoppedComparisonValue, ite_eq_right hstop, comparisonStateCost]
      split_ifs with hd
      · have hp := comparisonFrontier_active_source source target hM P hP rootQ d path parent q heq hstop
        have h := htable (⟨⟨d, by omega⟩, path⟩, q)
        simpa only [physicalSource, physicalSourceInterval, ← hp] using h
      · exact ⟨le_rfl, mul_nonneg (by linarith) (Nat.cast_nonneg _)⟩

theorem comparisonPhysicalLift_gap {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ)
    (htable : ∀ state, |stateLengthGap (physicalSource source state.1) target state.2| ≤ table state)
    (rootQ : TargetInterval target.length) (d : ℕ) (hd : d ≤ J) (path : TreeLayer M d) :
    |comparisonStateGap source target (comparisonFrontier source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path)| ≤
        comparisonPhysicalLift source target hM P hP table rootQ d path := by
  classical
  unfold comparisonPhysicalLift
  rw [dite_eq_left hd]
  generalize heq : comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path = state
  cases state with
  | none => simp only [comparisonStateGap, stoppedComparisonValue, abs_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [stoppedComparisonValue, ite_eq_left hstop, comparisonStateGap]
      exact stateEditCost_length_lower (substring source parent.lo parent.hi) target q
    · simp only [stoppedComparisonValue, ite_eq_right hstop, comparisonStateGap]
      have hp := comparisonFrontier_active_source source target hM P hP rootQ d path parent q heq hstop
      have h := htable (⟨⟨d, by omega⟩, path⟩, q)
      simpa only [physicalSource, physicalSourceInterval, ← hp] using h

theorem gap_energy_bounds {gap mass : ℝ} (hgap : |gap| ≤ mass) :
    0 ≤ gap ^ 2 / mass ∧ gap ^ 2 / mass ≤ mass := by
  have hm : 0 ≤ mass := (abs_nonneg _).trans hgap
  refine ⟨div_nonneg (sq_nonneg _) hm, ?_⟩
  by_cases hz : mass = 0
  · simp only [hz, div_zero, le_refl]
  · have hp : 0 < mass := lt_of_le_of_ne hm (Ne.symm hz)
    apply (div_le_iff₀ hp).2
    have hsq : gap ^ 2 ≤ mass ^ 2 := by
      simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg gap) hgap 2)
    simpa only [pow_two] using hsq

section Warmup

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

/-- The comparison mass is the actual averaged warmup at active states and
true cost at carried stopped states. -/
noncomputable def stageComparisonMass (d : ℕ) (path : TreeLayer M d) : ℝ :=
  comparisonPhysicalLift source target hM P hP
    (fun state => (stageWarmupMass source target U N P F A T state : ℝ)) rootQ d path

noncomputable def stageComparisonEnergy (d : ℕ) (path : TreeLayer M d) : ℝ :=
  (comparisonStateGap source target (comparisonFrontier source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path)) ^ 2 /
      stageComparisonMass source target hM U N P F A hP T rootQ d path

include hsize hF hA hseed hT in
 theorem stageComparisonMass_bounds (d : ℕ) (path : TreeLayer M d) :
    0 ≤ stageComparisonMass source target hM U N P F A hP T rootQ d path ∧
      stageComparisonMass source target hM U N P F A hP T rootQ d path ≤
        2 * F * comparisonStateCost source target (comparisonFrontier source target hM P hP
          (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path) := by
  exact comparisonPhysicalLift_bounds source target hM P hP F (by exact_mod_cast hF) _
    (fun state => by
      have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT state
      have hlower := ((le_max_right _ _).trans h.1).trans (Rat.cast_le.mpr h.2.1)
      have hupper : (stageWarmupMass source target U N P F A T state : ℝ) ≤
          ((2 * F * stateEditCost (physicalSource source state.1) target state.2 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (h.2.2.1.trans h.2.2.2)
      exact ⟨(abs_nonneg _).trans hlower, by simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hupper⟩)
    rootQ d path

include hsize hF hA hseed hT in
 theorem stageComparisonEnergy_bounds (d : ℕ) (hd : d ≤ J) (path : TreeLayer M d) :
    0 ≤ stageComparisonEnergy source target hM U N P F A hP T rootQ d path ∧
      stageComparisonEnergy source target hM U N P F A hP T rootQ d path ≤
        stageComparisonMass source target hM U N P F A hP T rootQ d path := by
  apply gap_energy_bounds
  exact comparisonPhysicalLift_gap source target hM P hP _
    (fun state => by
      have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT state
      exact ((le_max_right _ _).trans h.1).trans (Rat.cast_le.mpr h.2.1)) rootQ d hd path

include hsize hF hA hseed hT in
 theorem stageComparisonMass_root :
    stageComparisonMass source target hM U N P F A hP T rootQ 0 PUnit.unit =
      stageWarmupMass source target U N P F A T (⟨⟨0, by omega⟩, PUnit.unit⟩, rootQ) := by
  exact comparisonPhysicalLift_root source target hM P hP _
    (fun node q hstop => by
      exact_mod_cast stageWarmupMass_at_stopped source target hM U N P F A hsize hP hF hA hseed
        T hT node q hstop) rootQ

 theorem stageComparisonMass_terminal (hcapacity : source.length ≤ M ^ J) (path : TreeLayer M J) :
    stageComparisonMass source target hM U N P F A hP T rootQ J path =
      comparisonStateCost source target (comparisonFrontier source target hM P hP
        (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J path) := by
  exact comparisonPhysicalLift_terminal source target hM P hP _ rootQ hcapacity path

include hsize hF hA hseed hT in
 theorem stageComparisonEnergy_telescope (hcapacity : source.length ≤ M ^ J)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ d ∈ range J, ∑ path : TreeLayer M d,
      ((∑ i : Fin M, stageComparisonEnergy source target hM U N P F A hP T rootQ (d + 1) (path, i)) -
        stageComparisonEnergy source target hM U N P F A hP T rootQ d path)) ≤
      2 * comparisonStateCost source target (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) := by
  have htel := tree_frontier_telescope M J (stageComparisonEnergy source target hM U N P F A hP T rootQ)
  have heq : (∑ d ∈ range J, ∑ path : TreeLayer M d,
      ((∑ i : Fin M, stageComparisonEnergy source target hM U N P F A hP T rootQ (d + 1) (path, i)) -
        stageComparisonEnergy source target hM U N P F A hP T rootQ d path)) =
      (∑ path : TreeLayer M J, stageComparisonEnergy source target hM U N P F A hP T rootQ J path) -
        stageComparisonEnergy source target hM U N P F A hP T rootQ 0 PUnit.unit := by
    have h := congrArg Neg.neg htel
    simp only [← sum_neg_distrib, neg_sub] at h
    exact h
  rw [heq]
  have hroot := (stageComparisonEnergy_bounds source target hM U N P F A hsize hP hF hA hseed T hT rootQ
    0 (Nat.zero_le J) PUnit.unit).1
  have hterminal := sum_le_sum (fun path (_ : path ∈ (univ : Finset (TreeLayer M J))) =>
    (stageComparisonEnergy_bounds source target hM U N P F A hsize hP hF hA hseed T hT rootQ J le_rfl path).2)
  simp_rw [stageComparisonMass_terminal source target hM U N P F A hP T rootQ hcapacity] at hterminal
  have hcost := comparison_frontier_cost_le_twice source target hM P hP
    (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J J le_rfl hsmall
  linarith only [hroot, hterminal, hcost]

end Warmup

end EditApproximation

end OAI
