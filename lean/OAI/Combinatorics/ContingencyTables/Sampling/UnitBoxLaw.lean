import OAI.Combinatorics.ContingencyTables.Sampling.ProfileBoxIndex
import OAI.Combinatorics.ContingencyTables.Sampling.UnitIntegerLaw
import OAI.Combinatorics.ContingencyTables.Transport.IntegerLawEmbedding
import OAI.Combinatorics.ContingencyTables.Machines.IntegerMatrixProgram

namespace OAI

/-! # The actual adaptive profile walk embedded in its enumerable box -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] unitStepCounts profileIndex

/-- Invalid vectors get harmless stationary rows. Every actual profile
row is exactly the computed sampler transition transported to the box. -/
def unitBoxStep (k : BoxIndex) : IntegerLaw BoxIndex (2^(s)) :=
  (profileAt r c e k).elim (IntegerLaw.point (2^(s)) k)
    (fun x => (unitStepCounts r c e x).push (profileIndex r c e))

lemma unitBoxStep_index (x : PaperStates r c) :
    unitBoxStep r c e (profileIndex r c e x)=
      (unitStepCounts r c e x).push (profileIndex r c e) := by
  unfold unitBoxStep
  rw [profileAt_index]
  rfl

lemma unitBoxWalk_count (x : PaperStates r c) (N : ℕ) (k : BoxIndex) :
    (IntegerLaw.walk (unitBoxStep r c e) (profileIndex r c e x) N).count k=
      ((unitWalkCounts r c e x N).push (profileIndex r c e)).count k :=
  IntegerLaw.walk_push_count (unitStepCounts r c e)
    (unitBoxStep r c e) (profileIndex r c e)
    (unitBoxStep_index r c e) x N k

lemma unitBoxWalk_actual_count (x y : PaperStates r c) (N : ℕ) :
    (IntegerLaw.walk (unitBoxStep r c e) (profileIndex r c e x) N).count
      (profileIndex r c e y)=(unitWalkCounts r c e x N).count y := by
  rw [unitBoxWalk_count]
  exact IntegerLaw.push_count_injective _ _ (profileIndex_injective r c e) y

/-- Matrix propagation computes all box masses, including the zero
masses of invalid vectors, without enumerating random histories. -/
lemma unitBox_iterate (x : PaperStates r c) (N : ℕ) :
    IntegerMatrixPrograms.iterate (N,
      (List.ofFn (fun target : BoxIndex => List.ofFn (fun source : BoxIndex =>
        (unitBoxStep r c e source).count target)),
       List.ofFn (fun k : BoxIndex => if k=profileIndex r c e x then 1 else 0)))=
      List.ofFn (fun k : BoxIndex =>
        ((unitWalkCounts r c e x N).push (profileIndex r c e)).count k) := by
  rw [IntegerMatrixPrograms.iterate_ofFn]
  apply congrArg List.ofFn
  funext k
  exact unitBoxWalk_count r c e x N k

end
end ContingencyTables.SmallGraphProfiles

end OAI
