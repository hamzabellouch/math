import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTerminalProgram
import OAI.Combinatorics.ContingencyTables.Machines.CachedTerminalSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileMatrixLaw
import OAI.Combinatorics.ContingencyTables.Transport.IntegerMatrixPoint

namespace OAI

/-! # Exact trial counts from matrix propagation and cached terminal weights -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical

lemma bind_count {A B : Type*} [Fintype A] [Fintype B]
    {Q R : ℕ} (p : IntegerLaw A Q) (K : A → IntegerLaw B R) (b : B) :
    (p.bind K).count b=∑ a,p.count a*(K a).count b := rfl

lemma sum_push_mul {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {Q : ℕ} (p : IntegerLaw A Q) (f : A → B) (w : B → ℕ) :
    (∑ b,(p.push f).count b*w b)=∑ a,p.count a*w (f a) := by
  change (∑ b,(∑ a,if f a=b then p.count a else 0)*w b)=_
  simp_rw [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end ContingencyTables.IntegerLaw

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

attribute [local irreducible] stateCode stateCodeData listedCompletionCounts listedWalkCounts
  listedTrialCounts prepareTransitionCache terminalCount matrixInput IntegerLaw.push

def terminalFibreCounts (x : PaperStates r c) : IntegerLaw (Option (Table r c)) (2^f) :=
  (listedCompletionCounts r c hr hc b h hb x).push (fun A => stateTrial r c ⟨x,A⟩)

lemma terminalEntry_actual (z x : PaperStates r c) (xs : List Bool) (T : Table r c) :
    terminalEntry (matrixInput r c e b h z xs,(stateCode r c e x,matrixCode T.val))=
      (terminalFibreCounts r c hr hc b h hb x).count (some T) := by
  unfold terminalEntry terminalEntryQuery terminalSourceInput entryCacheParameters
  dsimp only [sourceData,matrixData]
  unfold matrixInput
  rw [candidate_stateCodeData]
  exact terminalCount_actual r c e hr hc b h hb x T

lemma terminalColumn_ofFn (z : PaperStates r c) (xs : List Bool) (T : Table r c) :
    terminalColumn (matrixInput r c e b h z xs,matrixCode T.val)=
      List.ofFn (fun k : BoxIndex => terminalEntry
        (matrixInput r c e b h z xs,(boxCode k,matrixCode T.val))) := by
  have hv : profileBoxViews (matrixData (matrixInput r c e b h z xs))=List.ofFn
      (boxCode (m := m) (n := n) (q := q)) := by
    unfold matrixData matrixInput
    exact profileBoxViews_actual r c e z
  unfold terminalColumn
  dsimp only [Prod.fst]
  rw [hv,List.map_ofFn]
  rfl

lemma listedTrialCounts_count (z : PaperStates r c) (N : ℕ) (T : Table r c) :
    (listedTrialCounts r c e hr hc b h hb z N).count (some T)=
      ∑ x,(listedWalkCounts r c e hr hc b h hb z N).count x*
        (terminalFibreCounts r c hr hc b h hb x).count (some T) := by
  unfold listedTrialCounts terminalFibreCounts
  exact IntegerLaw.bind_count _ _ _

attribute [local irreducible] terminalFibreCounts

lemma terminal_dot_trial (z : PaperStates r c) (xs : List Bool) (N : ℕ) (T : Table r c) :
    IntegerMatrixPrograms.dot
      (List.ofFn (fun k : BoxIndex =>
        ((listedWalkCounts r c e hr hc b h hb z N).push (profileIndex r c e)).count k),
       terminalColumn (matrixInput r c e b h z xs,matrixCode T.val))=
      (listedTrialCounts r c e hr hc b h hb z N).count (some T) := by
  rw [terminalColumn_ofFn r c e b h z xs T,IntegerMatrixPrograms.dot_ofFn,
    IntegerLaw.sum_push_mul]
  change (∑ x,(listedWalkCounts r c e hr hc b h hb z N).count x*
    terminalEntry (matrixInput r c e b h z xs,(boxCode (profileIndex r c e x),matrixCode T.val)))=_
  simp_rw [boxCode_index,terminalEntry_actual r c e hr hc b h hb]
  exact (listedTrialCounts_count r c e hr hc b h hb z N T).symm

lemma fromPoint_trial_count (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) (T : Table r c) :
    IntegerMatrixPrograms.dot
      (IntegerMatrixPrograms.fromPoint (N,
        (profileMatrix (matrixInput r c e b h z xs),(profileIndex r c e z).val)),
       terminalColumn (matrixInput r c e b h z xs,matrixCode T.val))=
      (listedTrialCounts r c e hr hc b h hb z N).count (some T) := by
  unfold IntegerMatrixPrograms.fromPoint
  rw [profileMatrix_actual r c e hr hc b h hb htotal z xs hs,
    IntegerMatrixPrograms.pointVector_ofFn]
  rw [←profileMatrix_actual r c e hr hc b h hb htotal z xs hs,
    profileMatrix_walk r c e hr hc b h hb htotal z xs hs N]
  exact terminal_dot_trial r c e hr hc b h hb z xs N T

end
end ContingencyTables.SmallGraphProfiles

end OAI
