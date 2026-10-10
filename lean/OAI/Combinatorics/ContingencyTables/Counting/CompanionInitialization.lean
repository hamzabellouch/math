import OAI.Combinatorics.ContingencyTables.Counting.CompanionFactorialApplication
import OAI.Combinatorics.ContingencyTables.Transport.InitialTransversals

namespace OAI

/-! # Exact initial normalizer for the literal companion completion count -/

namespace ContingencyTables.CompanionInitialization

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def freeTotal (A : Instance I J) : ℝ :=
  ∏ a : ForestAssignmentSplit.FreeCell A.small A.T,
    ((A.b a.val.1 a.val.2+1:ℕ):ℝ)

theorem h_zero (A : Instance I J) (z : View A → ℕ) : h A 0 z=freeTotal A :=
  ForestCountIdentification.sourceMarginal_zero A.small A.T A.d A.b A.r A.c z

theorem denominator_eq (A : Instance I J) :
    CompanionFactorialApplication.denominator A=
      InitialTransversals.denominator (fun s : SmallCell A => A.b s.val.1 s.val.2) := by
  unfold CompanionFactorialApplication.denominator TwoLiftStates.denominator InitialTransversals.denominator
  simp_rw [label_width]

/-- C(0) is derived for the actual source f, using the finite
paired-transversal enumeration and the literal free-completion count. -/
theorem total_zero (A : Instance I J) :
    slotTotal pairs (f A 0) ∅=freeTotal A*∏ s : SmallCell A, ((A.b s.val.1 s.val.2:ℝ)+1) := by
  have he : f A 0=firstLift (group (labelCell A)) (fun _ => freeTotal A)
      (CompanionFactorialApplication.denominator A) := by
    funext S
    unfold f firstLift
    rw [h_zero]
  rw [he,denominator_eq]
  convert InitialTransversals.slotTotal_constant
    (fun s : SmallCell A => A.b s.val.1 s.val.2) (freeTotal A) using 1
  congr 1

end ContingencyTables.CompanionInitialization

end OAI
