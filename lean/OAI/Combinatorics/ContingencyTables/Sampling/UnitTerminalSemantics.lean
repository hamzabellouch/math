import OAI.Combinatorics.ContingencyTables.Sampling.UnitMatrixLaw
import OAI.Combinatorics.ContingencyTables.Sampling.UnitTrialCountProgram
import OAI.Combinatorics.ContingencyTables.Sampling.UnitOutputSemantics

namespace OAI

/-! # All-small trial counts from the computed matrix and terminal column -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c)) (b h : ℕ)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] stateCode stateCodeData matrixInput unitWalkCounts unitTrialCounts
  UnitCountPrograms.terminalEntry IntegerLaw.push

lemma successfulWeight_table (o : Option (Table r c)) (T : Table r c) :
    successfulWeight (matrixCode T.val,(o.map (fun A => matrixCode A.val),1))=
      if o=some T then 1 else 0 := by
  cases o with
  | none => rfl
  | some A =>
    unfold successfulWeight
    simp only [Option.map_some,Option.elim_some,Option.some.injEq]
    have he : matrixCode A.val=matrixCode T.val ↔ A=T := by
      constructor
      · intro he
        exact Subtype.ext (matrixCode_injective he)
      · rintro rfl
        rfl
    simp only [he]

lemma unit_terminalEntry_actual (hsmall : ∀ i j,paperSmall r c i j=true)
    (z x : PaperStates r c) (xs : List Bool) (T : Table r c) :
    UnitCountPrograms.terminalEntry (matrixInput r c e b h z xs,(stateCode r c e x,matrixCode T.val))=
      if stateTrial r c ⟨x,allSmallFibre r c hsmall x⟩=some T then 1 else 0 := by
  unfold UnitCountPrograms.terminalEntry UnitCountPrograms.terminalData terminalSourceInput
  dsimp only [sourceData,matrixData]
  unfold matrixInput
  rw [candidate_stateCodeData,unitOuterTrial r c e hsmall x]
  exact successfulWeight_table r c _ T

lemma unit_terminalColumn_ofFn (z : PaperStates r c) (xs : List Bool) (T : Table r c) :
    UnitCountPrograms.terminalColumn (matrixInput r c e b h z xs,matrixCode T.val)=
      List.ofFn (fun k : BoxIndex => UnitCountPrograms.terminalEntry
        (matrixInput r c e b h z xs,(boxCode k,matrixCode T.val))) := by
  have hv : profileBoxViews (matrixData (matrixInput r c e b h z xs))=List.ofFn
      (boxCode (m := m) (n := n) (q := q)) := by
    unfold matrixData matrixInput
    exact profileBoxViews_actual r c e z
  unfold UnitCountPrograms.terminalColumn
  dsimp only [Prod.fst]
  rw [hv,List.map_ofFn]
  rfl

lemma unitTrialCounts_count (hsmall : ∀ i j,paperSmall r c i j=true)
    (z : PaperStates r c) (N : ℕ) (T : Table r c) :
    (unitTrialCounts r c e hsmall z N).count (some T)=
      ∑ x,(unitWalkCounts r c e z N).count x*
        (if stateTrial r c ⟨x,allSmallFibre r c hsmall x⟩=some T then 1 else 0) := by
  unfold unitTrialCounts
  rw [IntegerLaw.push_count_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

lemma unit_terminal_dot_trial (hsmall : ∀ i j,paperSmall r c i j=true)
    (z : PaperStates r c) (xs : List Bool) (N : ℕ) (T : Table r c) :
    IntegerMatrixPrograms.dot
      (List.ofFn (fun k : BoxIndex =>
        ((unitWalkCounts r c e z N).push (profileIndex r c e)).count k),
       UnitCountPrograms.terminalColumn (matrixInput r c e b h z xs,matrixCode T.val))=
      (unitTrialCounts r c e hsmall z N).count (some T) := by
  rw [unit_terminalColumn_ofFn r c e b h z xs T,IntegerMatrixPrograms.dot_ofFn,IntegerLaw.sum_push_mul]
  change (∑ x,(unitWalkCounts r c e z N).count x*
    UnitCountPrograms.terminalEntry
      (matrixInput r c e b h z xs,(boxCode (profileIndex r c e x),matrixCode T.val)))=_
  simp_rw [boxCode_index,unit_terminalEntry_actual r c e b h hsmall]
  exact (unitTrialCounts_count r c e hsmall z N T).symm

lemma unit_trialCount_actual (htotal : ∑ i,r i=∑ j,c j)
    (hsmall : ∀ i j,paperSmall r c i j=true) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) (T : Table r c) :
    UnitCountPrograms.trialCount
      ((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),matrixCode T.val)=
      (unitTrialCounts r c e hsmall z N).count (some T) := by
  unfold UnitCountPrograms.trialCount UnitCountPrograms.walkCounts UnitCountPrograms.walkCountData
  rw [unit_profileMatrix_actual r c e b h htotal z xs hs,IntegerMatrixPrograms.fromPoint_ofFn]
  have he : List.ofFn (IntegerPropagation.numerators
      (fun i j : BoxIndex => (unitBoxStep r c e i).count j) (profileIndex r c e z) N)=
      List.ofFn (fun k : BoxIndex => ((unitWalkCounts r c e z N).push (profileIndex r c e)).count k) := by
    apply congrArg List.ofFn
    funext k
    exact unitBoxWalk_count r c e z N k
  rw [he]
  exact unit_terminal_dot_trial r c e b h hsmall z xs N T

end
end ContingencyTables.SmallGraphProfiles

end OAI
