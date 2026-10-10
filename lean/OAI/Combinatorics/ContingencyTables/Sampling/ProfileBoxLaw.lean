import OAI.Combinatorics.ContingencyTables.Sampling.ProfileBoxIndex
import OAI.Combinatorics.ContingencyTables.Transport.ListedIntegerLaw
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
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] listedStepCounts profileIndex

/-- Invalid vectors get harmless stationary rows. Every actual profile
row is exactly the computed sampler transition transported to the box. -/
def profileBoxStep (k : BoxIndex) : IntegerLaw BoxIndex (2^(s+f)) :=
  (profileAt r c e k).elim (IntegerLaw.point (2^(s+f)) k)
    (fun x => (listedStepCounts r c e hr hc b h hb x).push (profileIndex r c e))

lemma profileBoxStep_index (x : PaperStates r c) :
    profileBoxStep r c e hr hc b h hb (profileIndex r c e x)=
      (listedStepCounts r c e hr hc b h hb x).push (profileIndex r c e) := by
  unfold profileBoxStep
  rw [profileAt_index]
  rfl

lemma profileBoxWalk_count (x : PaperStates r c) (N : ℕ) (k : BoxIndex) :
    (IntegerLaw.walk (profileBoxStep r c e hr hc b h hb) (profileIndex r c e x) N).count k=
      ((listedWalkCounts r c e hr hc b h hb x N).push (profileIndex r c e)).count k :=
  IntegerLaw.walk_push_count (listedStepCounts r c e hr hc b h hb)
    (profileBoxStep r c e hr hc b h hb) (profileIndex r c e)
    (profileBoxStep_index r c e hr hc b h hb) x N k

lemma profileBoxWalk_actual_count (x y : PaperStates r c) (N : ℕ) :
    (IntegerLaw.walk (profileBoxStep r c e hr hc b h hb) (profileIndex r c e x) N).count
      (profileIndex r c e y)=(listedWalkCounts r c e hr hc b h hb x N).count y := by
  rw [profileBoxWalk_count]
  exact IntegerLaw.push_count_injective _ _ (profileIndex_injective r c e) y

/-- Matrix propagation computes all box masses, including the zero
masses of invalid vectors, without enumerating random histories. -/
lemma profileBox_iterate (x : PaperStates r c) (N : ℕ) :
    IntegerMatrixPrograms.iterate (N,
      (List.ofFn (fun target : BoxIndex => List.ofFn (fun source : BoxIndex =>
        (profileBoxStep r c e hr hc b h hb source).count target)),
       List.ofFn (fun k : BoxIndex => if k=profileIndex r c e x then 1 else 0)))=
      List.ofFn (fun k : BoxIndex =>
        ((listedWalkCounts r c e hr hc b h hb x N).push (profileIndex r c e)).count k) := by
  rw [IntegerMatrixPrograms.iterate_ofFn]
  apply congrArg List.ofFn
  funext k
  exact profileBoxWalk_count r c e hr hc b h hb x N k

end
end ContingencyTables.SmallGraphProfiles

end OAI
