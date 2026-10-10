import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalJointProgram
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSeedTables

namespace OAI

/-! The local bounded-key random source implements the same whole-table
median pass as the complete program. Copies are independent, while all
entries within a copy retain their shared online and group draws. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Median

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau eta kappa delta : ℚ)
  (a S copies : ℕ)

/-- The executable local pass: scale and round each full-copy value, take
the upper median, and clamp each result to the common finite seed type. -/
noncomputable def physicalLocalMedianUpdateTable
    (draws : Fin copies → PhysicalLocalProgramDraw (R := R)
      source target U N P F A T exponent H Q tau) :
    ClampedPhysicalSeed M J target.length N := fun state =>
  ⟨finiteMedianSeed N copies
      (fun draw => ⌈(a : ℚ) * physicalLocalJointValue source target U N P F A T exponent H Q
        tau eta kappa delta draw state.1 S state.2⌉₊) draws,
    Nat.lt_succ_of_le (min_le_left _ _)⟩

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalLocalMedianUpdateTable_eq
    (draws : Fin copies → PhysicalLocalProgramDraw (R := R)
      source target U N P F A T exponent H Q tau) :
    physicalLocalMedianUpdateTable source target U N P F A T exponent H Q tau eta kappa delta
        a S copies draws =
      physicalMedianUpdateTable source target U N P F A T delta a S copies
        (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa)
        (fun i => physicalLocalProgramToComplete source target U N P F A T exponent H Q tau
          hsize hP hF hA hseed (draws i)) := by
  funext state
  apply Fin.ext
  change min N (upperMedian (List.ofFn fun i : Fin copies =>
    ⌈(a : ℚ) * physicalLocalJointValue source target U N P F A T exponent H Q
      tau eta kappa delta (draws i) state.1 S state.2⌉₊)) = _
  apply congrArg (fun values : Fin copies → ℕ => min N (upperMedian (List.ofFn values)))
  funext i
  rw [physicalLocalJointValue_eq source target U N P F A T exponent H Q tau eta kappa delta
    (draws i) hsize hP hF hA hseed]
  rfl

omit [NeZero R] in
/-- The restriction to used keys preserves independence between complete
program copies, as well as the law of each copy. -/
theorem physicalLocalProgramCopyDrawLaw_map :
    (Measure.pi fun _ : Fin copies => physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau).map
      (fun draws i => physicalLocalProgramToComplete source target U N P F A T exponent H Q tau
        hsize hP hF hA hseed (draws i)) =
      Measure.pi (fun _ : Fin copies => physicalProgramDrawLaw (R := R)
        source target U N P F A T exponent H Q tau) := by
  classical
  let : IsProbabilityMeasure (physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau) := by
    unfold physicalLocalProgramDrawLaw
    infer_instance
  have hmap := physicalLocalProgramDrawLaw_map (R := R)
    source target U N P F A T exponent H Q tau hsize hP hF hA hseed
  have hcopies := Measure.pi_map_pi
    (μ := fun _ : Fin copies => physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau)
    (f := fun _ => physicalLocalProgramToComplete source target U N P F A T exponent H Q tau
      hsize hP hF hA hseed)
    (fun _ => (measurable_of_finite _).aemeasurable)
  simpa only [hmap] using hcopies

include hsize hP hF hA hseed in
/-- Equality of the entire returned seed-table distribution. No independent
per-entry resampling is introduced by replacing complete copies with local
bounded-key copies. -/
theorem physicalLocalMedianUpdateTable_law :
    (Measure.pi fun _ : Fin copies => physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau).map
      (physicalLocalMedianUpdateTable source target U N P F A T exponent H Q tau eta kappa delta
        a S copies) =
      (Measure.pi fun _ : Fin copies => physicalProgramDrawLaw (R := R)
        source target U N P F A T exponent H Q tau).map
      (physicalMedianUpdateTable source target U N P F A T delta a S copies
        (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa)) := by
  classical
  rw [← physicalLocalProgramCopyDrawLaw_map source target U N P F A T exponent H Q tau copies
    hsize hP hF hA hseed]
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  congr 1
  funext draws
  exact physicalLocalMedianUpdateTable_eq source target U N P F A T exponent H Q tau eta kappa
    delta a S copies hsize hP hF hA hseed draws

include hsize hP hF hA hseed in
/-- Any whole-seed event, including the simultaneous good-seed event, has
the same probability for the actual local median pass. -/
theorem physicalLocalMedianUpdateTable_event
    (event : Set (ClampedPhysicalSeed M J target.length N)) :
    (Measure.pi fun _ : Fin copies => physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau).real
      {draws | physicalLocalMedianUpdateTable source target U N P F A T exponent H Q
        tau eta kappa delta a S copies draws ∈ event} =
      (Measure.pi fun _ : Fin copies => physicalProgramDrawLaw (R := R)
        source target U N P F A T exponent H Q tau).real
      {draws | physicalMedianUpdateTable source target U N P F A T delta a S copies
        (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa)
        draws ∈ event} := by
  classical
  have h := congrArg (fun law : Measure (ClampedPhysicalSeed M J target.length N) => law.real event)
    (physicalLocalMedianUpdateTable_law (R := R) source target U N P F A T exponent H Q tau eta kappa delta
      a S copies hsize hP hF hA hseed)
  rw [map_measureReal_apply (measurable_of_finite _) (Set.toFinite event).measurableSet,
    map_measureReal_apply (measurable_of_finite _) (Set.toFinite event).measurableSet] at h
  exact h

end Median

end EditApproximation

end OAI
