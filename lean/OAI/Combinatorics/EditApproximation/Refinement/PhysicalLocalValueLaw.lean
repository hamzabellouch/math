import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalJointProgram

namespace OAI

/-! The direct local program has the same returned-value law as the
complete refinement on each good incoming seed. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section ValueLaw

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau eta kappa delta : ℚ)

instance physicalLocalProgramDrawLaw_probability :
    IsProbabilityMeasure
      (physicalLocalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau) := by
  unfold physicalLocalProgramDrawLaw
  infer_instance

theorem physicalLocalJointValue_law
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    (physicalLocalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau).map
      (fun draw => physicalLocalJointValue source target U N P F A T exponent H Q tau eta kappa delta
        draw node t q) =
    (physicalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau).map
      (fun draw => physicalRefinement source target U N P F A T delta
        (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa draw)
        node t q) := by
  let complete := fun draw : PhysicalProgramDraw (R := R) source target U N P F A T exponent H Q tau =>
    physicalRefinement source target U N P F A T delta
      (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa draw) node t q
  let restrict := physicalLocalProgramToComplete (R := R) source target U N P F A T exponent H Q tau
    hsize hP hF hA hseed
  have heq : (fun draw => physicalLocalJointValue source target U N P F A T exponent H Q tau
      eta kappa delta draw node t q) = complete ∘ restrict := by
    funext draw
    exact physicalLocalJointValue_eq source target U N P F A T exponent H Q tau eta kappa delta
      draw hsize hP hF hA hseed node t q
  rw [heq, ← Measure.map_map (measurable_of_finite complete) (measurable_of_finite restrict)]
  rw [physicalLocalProgramDrawLaw_map source target U N P F A T exponent H Q tau
    hsize hP hF hA hseed]

end ValueLaw

end EditApproximation

end OAI
