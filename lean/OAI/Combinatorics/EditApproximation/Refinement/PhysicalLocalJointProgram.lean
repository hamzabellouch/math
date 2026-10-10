import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalProgramLaw
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRawOnlineProgram
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRawGroupProgram

namespace OAI

/-! Direct evaluation from the bounded joint random source agrees with
complete refinement. All complete-table indexing occurs in the proof. -/

namespace EditApproximation

section Joint

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalLocalProgramDraw (R := R) source target U N P F A T exponent H Q tau)

def physicalLocalJointValue (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) : ℚ :=
  physicalLocalRefinement source target U N P F exponent Q A tau delta T
    (fun label s => physicalRawGroupDraws M J N target.length exponent F Q R
      (fun key => draw (.inr key)) label (Fin.ofNat R (s - 1)))
    (physicalLocalOnline source target U N P F exponent H T A tau eta kappa
      (physicalRawOnlineIntegers source target U N P F A T exponent H tau
        (fun key => draw (.inl key)))) node t q

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

theorem physicalLocalJointValue_eq (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    physicalLocalJointValue source target U N P F A T exponent H Q tau eta kappa delta draw node t q =
      physicalRefinement source target U N P F A T delta
        (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa
          (physicalLocalProgramToComplete source target U N P F A T exponent H Q tau
            hsize hP hF hA hseed draw)) node t q := by
  unfold physicalLocalJointValue
  rw [physicalRawOnlineProgram_eq source target U N P F A T exponent H tau eta kappa
    (fun key => draw (.inl key)) hsize hP hF hA hseed]
  rw [physicalGroupStreamsOfRaw]
  rfl

end Joint

end EditApproximation

end OAI
