import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderRowDivision

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive ExtraTape
  | vertexCount | result
  deriving DecidableEq

instance : Fintype ExtraTape where
  elems := {.vertexCount, .result}
  complete tape := by cases tape <;> simp

abbrev Tape := MachineExpanderRow.Tape ⊕ ExtraTape

abbrev Alphabet : Tape → Type :=
  MachineEmbedding.Alphabet (fun _ : MachineExpanderRow.Tape => Bool)
    (fun _ : ExtraTape => Bool)

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  cases tape <;> exact inferInstanceAs (Fintype Bool)

inductive OuterLabel
  | initialize | vertexGuard | prepareRow | afterRow | reverseOutput | done
  deriving DecidableEq

instance : Fintype OuterLabel where
  elems := {.initialize, .vertexGuard, .prepareRow, .afterRow, .reverseOutput, .done}
  complete label := by cases label <;> simp

abbrev Label (d : Nat) := MachineExpanderRow.Label d ⊕ OuterLabel
abbrev Position (d : Nat) := Fin (rowFactor d)
abbrev State (ρ : Type) (d : Nat) := MachineExpanderRow.State ρ d × Position d
abbrev RowStatePrefix (ρ : Type) (d : Nat) :=
  (MachineExpanderRow.Ambient ρ d × Fin (degree d)) × Unit

def guardStates (ρ : Type) (d : Nat) :
    ((RowStatePrefix ρ d × Position d) × Option Bool) ≃ State ρ d where
  toFun s := ((s.1.1, s.2), s.1.2)
  invFun s := ((s.1.1, s.2), s.1.2)
  left_inv := by rintro ⟨⟨a, p⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨a, b⟩, p⟩; rfl

@[simp] theorem guardStates_apply (ρ : Type) (d : Nat)
    (s : (RowStatePrefix ρ d × Position d) × Option Bool) :
    guardStates ρ d s = ((s.1.1, s.2), s.1.2) := rfl

@[simp] theorem guardStates_symm_apply (ρ : Type) (d : Nat) (s : State ρ d) :
    (guardStates ρ d).symm s = ((s.1.1, s.2), s.1.2) := rfl

theorem rowFactor_pos {d : Nat} (positive : 0 < d) : 0 < rowFactor d := by
  have hq : 0 < degree d := Nat.mul_pos positive positive
  exact Nat.mul_pos (Nat.mul_pos hq hq) hq

def zeroPosition {d : Nat} (positive : 0 < d) : Position d :=
  ⟨0, rowFactor_pos positive⟩

def nextPosition {d : Nat} (positive : 0 < d) (p : Position d) : Position d :=
  ⟨(p.val + 1) % rowFactor d, Nat.mod_lt _ (rowFactor_pos positive)⟩

def positionPair {d : Nat} (p : Position d) : Fin (cloudSize d) × Fin (degree d) :=
  (rowIndex (cloudSize d) (degree d)).symm p

def caller {ρ : Type} {d : Nat} (s : State ρ d) : ρ := s.1.1.1.1.1

def boundaryState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) (p : Position d) : State ρ d :=
  (MachineExpanderRow.divisionState positive ambient
    (start H (positionPair p).1 (positionPair p).2) none, p)

def initialState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) : State ρ d :=
  boundaryState positive H ambient (zeroPosition positive)

def prepareState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  boundaryState positive H (caller s) s.2

def resetState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  initialState positive H (caller s)

def clearRegister {ρ : Type} {d : Nat} (s : State ρ d) : State ρ d :=
  ((s.1.1, none), s.2)

def advancePositionState {ρ : Type} {d : Nat} (positive : 0 < d)
    (s : State ρ d) : State ρ d := (s.1, nextPosition positive s.2)

def resetPositionState {ρ : Type} {d : Nat} (positive : 0 < d)
    (s : State ρ d) : State ρ d := (s.1, zeroPosition positive)

def vertexGuardCore {ρ : Type} {d : Nat} :
    TM2.Stmt Alphabet (Label d) ((RowStatePrefix ρ d × Position d) × Option Bool) :=
  .peek (.inr .vertexCount) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.pop (.inr .vertexCount) (fun s _ => (s.1, none))
        (.goto fun _ => .inr .prepareRow))
      (.load (fun s => (s.1, none)) (.goto fun _ => .inr .reverseOutput)))

variable {ρ : Type} [Fintype ρ]

def outerStatement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    OuterLabel → TM2.Stmt Alphabet (Label d) (State ρ d)
  | .initialize =>
    .push (.inl .inputVertex) (fun _ => false)
      (.load (resetState positive H) (.goto fun _ => .inr .vertexGuard))
  | .vertexGuard => MachineControl.statement id (guardStates ρ d) vertexGuardCore
  | .prepareRow =>
    .load (prepareState positive H) (.goto fun _ => .inl .initialize)
  | .afterRow =>
    .branch (fun s => decide (s.2.val + 1 < rowFactor d))
      (.load (advancePositionState positive) (.goto fun _ => .inr .prepareRow))
      (.push (.inl .inputVertex) (fun _ => true)
        (.load (resetPositionState positive) (.goto fun _ => .inr .vertexGuard)))
  | .reverseOutput =>
    MachineControl.statement id (guardStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := Alphabet) (Λ := Label d)
        (σ := RowStatePrefix ρ d × Position d) (.inl .output) (.inr .result) id false
        (.inr .reverseOutput) (some (.inr .done)))
  | .done => .halt

def rowReturn (d : Nat) : Option (Label d) := some (.inr .afterRow)

def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    Label d → TM2.Stmt Alphabet (Label d) (State ρ d) :=
  MachineEmbedding.program (rowReturn d) (MachineExpanderRow.program positive H)
    (outerStatement positive H)

@[simp] theorem program_row {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (label : MachineExpanderRow.Label d) :
    program (ρ := ρ) positive H (.inl label) =
      MachineEmbedding.statement (rowReturn d)
        (MachineExpanderRow.program positive H label) := rfl

@[simp] theorem program_outer {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (label : OuterLabel) :
    program (ρ := ρ) positive H (.inr label) = outerStatement positive H label := rfl

def rowExecution {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (position : Position d) (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg (fun _ : MachineExpanderRow.Tape => Bool)
      (MachineExpanderRow.Label d) (MachineExpanderRow.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderRow.program positive H)) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      (MachineEmbedding.configuration (rowReturn d) position extra a)
      (some (MachineEmbedding.configuration (rowReturn d) position extra b)) budget :=
  MachineComposition.embeddedExecution (rowReturn d) position extra
    (MachineExpanderRow.program positive H) (outerStatement positive H) execution

@[simp] theorem rowExecution_steps {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (position : Position d) (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg (fun _ : MachineExpanderRow.Tape => Bool)
      (MachineExpanderRow.Label d) (MachineExpanderRow.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderRow.program positive H)) a (some b) budget) :
    (rowExecution positive H position extra execution).steps = execution.steps := rfl

def rowTapes (vertex : Nat) (oldTable output : List Bool) : MachineExpanderRow.Tape → List Bool
  | .inputVertex => encodeWord vertex
  | .table => oldTable
  | .output => output
  | _ => []

def extraTapes (remaining : Nat) (countSuffix result : List Bool) : ExtraTape → List Bool
  | .vertexCount => encodeWord remaining ++ countSuffix
  | .result => result

def boundaryTapes (vertex remaining : Nat) (oldTable output countSuffix result : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (rowTapes vertex oldTable output) (extraTapes remaining countSuffix result)

def initialTapes (vertices : Nat) (oldTable countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes
    (fun tape => match tape with | .table => oldTable | _ => [])
    (extraTapes vertices countSuffix [])

def finalTapes (vertices : Nat) (oldTable output countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes vertices 0 oldTable [] countSuffix output

end IndependentSetsGames.Foundations.Complexity.MachineExpanderTable

end OAI
