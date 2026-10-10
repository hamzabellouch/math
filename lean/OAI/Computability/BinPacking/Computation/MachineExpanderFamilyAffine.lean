import OAI.Computability.BinPacking.Computation.MachineVertexPadding

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive ExtraTape
  | vertexCount | result
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.vertexCount, .result]

protected theorem ExtraTape.enumList_getElem?_ctorIdx_eq (x : ExtraTape) :
    ExtraTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := MachineExpanderRow.Tape ⊕ ExtraTape

abbrev Alphabet : Tape → Type :=
  MachineEmbedding.Alphabet (fun _ : MachineExpanderRow.Tape => Bool)
    (fun _ : ExtraTape => Bool)

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  cases tape <;> exact inferInstanceAs (Fintype Bool)

inductive OuterLabel
  | initialize | vertexGuard | prepareRow | afterRow | reverseOutput | done
  deriving DecidableEq

protected abbrev OuterLabel.enumList : List OuterLabel := [.initialize, .vertexGuard, .prepareRow,
  .afterRow, .reverseOutput, .done]

protected theorem OuterLabel.enumList_getElem?_ctorIdx_eq (x : OuterLabel) :
    OuterLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem OuterLabel.enumList_nodup : OuterLabel.enumList.Nodup := by decide

instance : Fintype OuterLabel where
  elems := ⟨OuterLabel.enumList, OuterLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

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

end BinPackingGames.Foundations.Complexity.MachineExpanderTable

namespace BinPackingGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

inductive ExtraTape
  | remainingLevel | currentSize | unaryScratch | tableReverse
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.remainingLevel, .currentSize,
  .unaryScratch, .tableReverse]

protected theorem ExtraTape.enumList_getElem?_ctorIdx_eq (x : ExtraTape) :
    ExtraTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := MachineExpanderTable.Tape ⊕ ExtraTape
abbrev Alphabet : Tape → Type :=
  MachineEmbedding.Alphabet MachineExpanderTable.Alphabet (fun _ : ExtraTape => Bool)
abbrev BoolAlphabet (_ : Tape) := Bool

theorem alphabet_eq : Alphabet = BoolAlphabet := by
  funext tape
  cases tape with
  | inl tape => cases tape <;> rfl
  | inr tape => rfl

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  rw [alphabet_eq]
  exact inferInstanceAs (Fintype Bool)

inductive AffinePhase
  | copyCount | multiplySize
  deriving DecidableEq

protected abbrev AffinePhase.enumList : List AffinePhase := [.copyCount, .multiplySize]

protected theorem AffinePhase.enumList_getElem?_ctorIdx_eq (x : AffinePhase) :
    AffinePhase.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem AffinePhase.enumList_nodup : AffinePhase.enumList.Nodup := by decide

instance : Fintype AffinePhase where
  elems := ⟨AffinePhase.enumList, AffinePhase.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive AffineLabel
  | seed | scan | restore
  deriving DecidableEq

protected abbrev AffineLabel.enumList : List AffineLabel := [.seed, .scan, .restore]

protected theorem AffineLabel.enumList_getElem?_ctorIdx_eq (x : AffineLabel) :
    AffineLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem AffineLabel.enumList_nodup : AffineLabel.enumList.Nodup := by decide

instance : Fintype AffineLabel where
  elems := ⟨AffineLabel.enumList, AffineLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive OuterLabel
  | initialize
  | levelGuard
  | affine (phase : AffinePhase) (label : AffineLabel)
  | clearOldTable | reverseResult | reverseTable | clearCurrentSize
  | drainInputVertex | drainVertexCount | done
  deriving DecidableEq, Fintype

abbrev Label (d : Nat) := MachineExpanderTable.Label d ⊕ OuterLabel
abbrev State (ρ : Type) (d : Nat) := MachineExpanderTable.State ρ d × Unit
abbrev RegisterAmbient (ρ : Type) (d : Nat) :=
  (MachineExpanderTable.RowStatePrefix ρ d × MachineExpanderTable.Position d) × Unit

def registerStates (ρ : Type) (d : Nat) :
    (RegisterAmbient ρ d × Option Bool) ≃ State ρ d where
  toFun s := (((s.1.1.1, s.2), s.1.1.2), s.1.2)
  invFun s := (((s.1.1.1, s.1.2), s.2), s.1.1.2)
  left_inv := by rintro ⟨⟨⟨a, p⟩, u⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨⟨a, b⟩, p⟩, u⟩; rfl

@[simp] theorem registerStates_apply (ρ : Type) (d : Nat)
    (s : RegisterAmbient ρ d × Option Bool) :
    registerStates ρ d s = (((s.1.1.1, s.2), s.1.1.2), s.1.2) := rfl

@[simp] theorem registerStates_symm_apply (ρ : Type) (d : Nat) (s : State ρ d) :
    (registerStates ρ d).symm s = (((s.1.1.1, s.1.2), s.2), s.1.1.2) := rfl

def caller {ρ : Type} {d : Nat} (s : State ρ d) : ρ :=
  MachineExpanderTable.caller s.1

def initialState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) : State ρ d :=
  (MachineExpanderTable.initialState positive H ambient, ())

def normalizeState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  initialState positive H (caller s)

def initialEncoding (d : Nat) : List Bool := encodeWords (rotationWords (initial d))

theorem initialEncoding_eq_family {d : Nat} (H : Table (cloudSize d) d) :
    initialEncoding d = encodeWords (rotationWords (family H 0)) := rfl

def tableTape : Tape := .inl (.inl .table)
def inputVertexTape : Tape := .inl (.inl .inputVertex)
def vertexCountTape : Tape := .inl (.inr .vertexCount)
def resultTape : Tape := .inl (.inr .result)

def affineSource : AffinePhase → Tape
  | .copyCount => .inr .currentSize
  | .multiplySize => inputVertexTape

def affineDestination : AffinePhase → Tape
  | .copyCount => vertexCountTape
  | .multiplySize => .inr .currentSize

def affineCoefficient (d : Nat) : AffinePhase → Nat
  | .multiplySize => cloudSize d
  | .copyCount => 1

def affineExit (d : Nat) : AffinePhase → Label d
  | .copyCount => .inl (.inr .initialize)
  | .multiplySize => .inr .drainInputVertex

def affineStatement {ρ : Type} {d : Nat} (phase : AffinePhase) :
    AffineLabel → TM2.Stmt BoolAlphabet (Label d) (State ρ d)
  | .seed =>
    MachineControl.statement id (registerStates ρ d)
      (MachineUnaryAffineAt.seed (Λ := Label d) (σ := RegisterAmbient ρ d)
        (affineDestination phase) 0 (.inr (.affine phase .scan)))
  | .scan =>
    MachineControl.statement id (registerStates ρ d)
      (MachineUnaryAffineAt.scan (Λ := Label d) (σ := RegisterAmbient ρ d)
        (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)))
  | .restore =>
    MachineControl.statement id (registerStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) (Λ := Label d)
        (σ := RegisterAmbient ρ d) (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)))

def drainStatement {ρ : Type} {d : Nat} (tape : Tape) (again next : OuterLabel) :
    TM2.Stmt BoolAlphabet (Label d) (State ρ d) :=
  MachineControl.statement id (registerStates ρ d)
    (MachineDrain.drain (Λ := Label d) (σ := RegisterAmbient ρ d)
      tape (.inr again) (some (.inr next)))

variable {ρ : Type} [Fintype ρ]

def boolOuterStatement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    OuterLabel → TM2.Stmt BoolAlphabet (Label d) (State ρ d)
  | .initialize =>
    Reduction.MachineSubstitution.pushWord tableTape (initialEncoding d).reverse
      (Reduction.MachineSubstitution.pushWord (.inr .currentSize) (encodeWord 1).reverse
        (.load (normalizeState positive H)
          (.goto fun _ => .inr .levelGuard)))
  | .levelGuard =>
    MachineControl.statement id (registerStates ρ d)
      (MachineUnaryCounter.guard (K := Tape) (Λ := Label d) (σ := RegisterAmbient ρ d)
        (.inr .remainingLevel) (.inr (.affine .copyCount .seed)) (.inr .done))
  | .affine phase label => affineStatement phase label
  | .clearOldTable => drainStatement tableTape .clearOldTable .reverseResult
  | .reverseResult =>
    MachineControl.statement id (registerStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) (Λ := Label d)
        (σ := RegisterAmbient ρ d) resultTape (.inr .tableReverse) id false
        (.inr .reverseResult) (some (.inr .reverseTable)))
  | .reverseTable =>
    MachineControl.statement id (registerStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) (Λ := Label d)
        (σ := RegisterAmbient ρ d) (.inr .tableReverse) tableTape id false
        (.inr .reverseTable) (some (.inr .clearCurrentSize)))
  | .clearCurrentSize =>
    drainStatement (.inr .currentSize) .clearCurrentSize (.affine .multiplySize .seed)
  | .drainInputVertex => drainStatement inputVertexTape .drainInputVertex .drainVertexCount
  | .drainVertexCount => drainStatement vertexCountTape .drainVertexCount .levelGuard
  | .done => .load (normalizeState positive H) .halt

def outerStatement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : OuterLabel) : TM2.Stmt Alphabet (Label d) (State ρ d) :=
  MachineAlphabetTransport.statement alphabet_eq.symm (boolOuterStatement positive H label)

def tableReturn (d : Nat) : Option (Label d) := some (.inr .clearOldTable)

def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (_growth : 1 < cloudSize d) : Label d → TM2.Stmt Alphabet (Label d) (State ρ d) :=
  MachineEmbedding.program (tableReturn d) (MachineExpanderTable.program positive H)
    (outerStatement positive H)

@[simp] theorem program_table {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (label : MachineExpanderTable.Label d) :
    program (ρ := ρ) positive H growth (.inl label) =
      MachineEmbedding.statement (tableReturn d)
        (MachineExpanderTable.program positive H label) := rfl

@[simp] theorem program_outer {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d) (label : OuterLabel) :
    program (ρ := ρ) positive H growth (.inr label) = outerStatement positive H label := rfl

def boolView {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) : Label d → TM2.Stmt BoolAlphabet (Label d) (State ρ d) :=
  MachineAlphabetTransport.program alphabet_eq (program positive H growth)

@[simp] theorem boolView_outer {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d) (label : OuterLabel) :
    boolView (ρ := ρ) positive H growth (.inr label) =
      boolOuterStatement positive H label := by
  change MachineAlphabetTransport.statement alphabet_eq
    (MachineAlphabetTransport.statement alphabet_eq.symm
      (boolOuterStatement positive H label)) = _
  exact MachineAlphabetTransport.statement_roundtrip alphabet_eq _

def tableExecution {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg MachineExpanderTable.Alphabet (MachineExpanderTable.Label d)
      (MachineExpanderTable.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderTable.program positive H)) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      (MachineEmbedding.configuration (tableReturn d) () extra a)
      (some (MachineEmbedding.configuration (tableReturn d) () extra b)) budget :=
  MachineComposition.embeddedExecution (tableReturn d) () extra
    (MachineExpanderTable.program positive H) (outerStatement positive H) execution

@[simp] theorem tableExecution_steps {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg MachineExpanderTable.Alphabet (MachineExpanderTable.Label d)
      (MachineExpanderTable.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderTable.program positive H)) a (some b) budget) :
    (tableExecution positive H growth extra execution).steps = execution.steps := rfl

def tableFrame (word : List Bool) : (tape : MachineExpanderTable.Tape) →
    List (MachineExpanderTable.Alphabet tape)
  | .inl .table => word
  | .inl _ => []
  | .inr _ => []

def extraFrame (remaining current : Nat) (levelSuffix : List Bool) : ExtraTape → List Bool
  | .remainingLevel => encodeWord remaining ++ levelSuffix
  | .currentSize => encodeWord current
  | _ => []

def boundaryTapes (remaining current : Nat) (word levelSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (tableFrame word) (extraFrame remaining current levelSuffix)

def initialTapes (level : Nat) (levelSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (tableFrame [])
    (fun tape => match tape with
      | .remainingLevel => encodeWord level ++ levelSuffix
      | _ => [])

def familyTapes {d : Nat} (H : Table (cloudSize d) d) (level : Nat)
    (levelSuffix : List Bool) : (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes 0 (vertexCount (degree d) level)
    (encodeWords (rotationWords (family H level))) levelSuffix

end BinPackingGames.Foundations.Complexity.MachineExpanderFamily

namespace BinPackingGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem caller_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    caller (boundaryState positive H ambient position) = ambient := rfl

@[simp] theorem prepareState_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    prepareState positive H (boundaryState positive H ambient position) =
      boundaryState positive H ambient position := rfl

@[simp] theorem clearRegister_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    clearRegister (boundaryState positive H ambient position) =
      boundaryState positive H ambient position := rfl

@[simp] theorem caller_prepareState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (prepareState positive H state) = caller state := rfl

@[simp] theorem caller_resetState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (resetState positive H state) = caller state := rfl

@[simp] theorem caller_clearRegister (state : State ρ d) :
    caller (clearRegister state) = caller state := rfl

@[simp] theorem caller_advancePositionState (positive : 0 < d) (state : State ρ d) :
    caller (advancePositionState positive state) = caller state := rfl

@[simp] theorem caller_resetPositionState (positive : 0 < d) (state : State ρ d) :
    caller (resetPositionState positive state) = caller state := rfl

theorem nextPosition_val_of_lt (positive : 0 < d) (position : Position d)
    (more : position.val + 1 < rowFactor d) :
    (nextPosition positive position).val = position.val + 1 := Nat.mod_eq_of_lt more

theorem boundaryTapes_update_count (vertex remaining next : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inr .vertexCount) (encodeWord next ++ countSuffix) =
      boundaryTapes vertex next oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;> simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

theorem boundaryTapes_increment_vertex (vertex remaining : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inl .inputVertex) (true :: encodeWord vertex) =
      boundaryTapes (vertex + 1) remaining oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update,
        encodeWord, List.replicate_succ]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

theorem initialTapes_initialize (vertices : Nat) (oldTable countSuffix : List Bool) :
    Function.update (initialTapes vertices oldTable countSuffix) (.inl .inputVertex) [false] =
      boundaryTapes 0 vertices oldTable [] countSuffix [] := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [initialTapes, boundaryTapes, rowTapes, MachineEmbedding.tapes,
        Function.update, encodeWord]
  · cases extra <;>
      simp [initialTapes, boundaryTapes, extraTapes, MachineEmbedding.tapes,
        Function.update]

variable [Fintype ρ]

theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .initialize), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetState positive H state,
        Function.update base (.inl .inputVertex) (false :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .initialize)) state base) = _
  rw [program_outer]
  rfl

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertices : Nat) (oldTable countSuffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .initialize), state, initialTapes vertices oldTable countSuffix⟩ =
      some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        boundaryTapes 0 vertices oldTable [] countSuffix []⟩ := by
  have h := initializeStep positive H (initialTapes vertices oldTable countSuffix) state
  have input : initialTapes vertices oldTable countSuffix (.inl .inputVertex) = [] := rfl
  simp only [input, resetState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize vertices oldTable countSuffix))

theorem vertexGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        Function.update base (.inr .vertexCount) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord, List.replicate_succ]

theorem vertexGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord]

theorem vertexGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex (remaining + 1) oldTable output countSuffix result⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ := by
  simpa only [boundaryTapes_update_count] using
    vertexGuard_succStep positive H
      (boundaryTapes vertex (remaining + 1) oldTable output countSuffix result)
      state remaining countSuffix rfl

theorem vertexGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex : Nat) (oldTable output countSuffix result : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ :=
  vertexGuard_zeroStep positive H
    (boundaryTapes vertex 0 oldTable output countSuffix result) state countSuffix rfl

theorem prepareRowStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .prepareRow), state, base⟩ =
      some ⟨some (.inl .initialize), prepareState positive H state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .prepareRow)) state base) = _
  rw [program_outer]
  rfl

theorem afterRow_moreStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (more : state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .prepareRow), advancePositionState positive state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, more]

theorem afterRow_lastStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        Function.update base (.inl .inputVertex) (true :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, last]

theorem afterRow_last_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H)
      ⟨some (.inr .afterRow), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        boundaryTapes (vertex + 1) remaining oldTable output countSuffix result⟩ := by
  have input : boundaryTapes vertex remaining oldTable output countSuffix result
      (.inl .inputVertex) = encodeWord vertex := rfl
  have h := afterRow_lastStep positive H
    (boundaryTapes vertex remaining oldTable output countSuffix result) state last
  simp only [input] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), resetPositionState positive state, tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (boundaryTapes_increment_vertex vertex remaining oldTable output countSuffix result))

theorem reverseOutput_consStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (symbol : Bool) (word : List Bool) (source : base (.inl .output) = symbol :: word) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
        Function.update (Function.update base (.inl .output) word)
          (.inr .result) (symbol :: base (.inr .result))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, source]

theorem reverseOutput_nilStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (source : base (.inl .output) = []) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have same : Function.update base (.inl .output) [] = base := by
    simpa only [source] using Function.update_eq_self (.inl .output) base
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, clearRegister, source, same]

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .done)) state base) = _
  rw [program_outer]
  rfl

end BinPackingGames.Foundations.Complexity.MachineExpanderTable

namespace BinPackingGames.Foundations.Complexity.MachineExpanderFamily

section

open Turing

def boolWord : (tape : Tape) → List Bool → List (Alphabet tape)
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def toBoolWord : (tape : Tape) → List (Alphabet tape) → List Bool
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def fromBoolTapes (base : Tape → List Bool) : (tape : Tape) → List (Alphabet tape) :=
  fun tape => boolWord tape (base tape)

def toBoolTapes (base : (tape : Tape) → List (Alphabet tape)) : Tape → List Bool :=
  fun tape => toBoolWord tape (base tape)

@[simp] theorem toBoolWord_boolWord (tape : Tape) (word : List Bool) :
    toBoolWord tape (boolWord tape word) = word := by
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem boolWord_toBoolWord (tape : Tape) (word : List (Alphabet tape)) :
    boolWord tape (toBoolWord tape word) = word := by
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem toBool_fromBool (base : Tape → List Bool) :
    toBoolTapes (fromBoolTapes base) = base := by
  funext tape
  exact toBoolWord_boolWord tape (base tape)

@[simp] theorem fromBool_toBool (base : (tape : Tape) → List (Alphabet tape)) :
    fromBoolTapes (toBoolTapes base) = base := by
  funext tape
  exact boolWord_toBoolWord tape (base tape)

private theorem transport_tapes_apply {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : (k : K) → List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem toBoolTapes_eq_transport (base : (tape : Tape) → List (Alphabet tape)) :
    toBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq base := by
  funext tape
  rw [transport_tapes_apply]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem fromBoolTapes_eq_transport (base : Tape → List Bool) :
    fromBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq.symm base := by
  funext tape
  rw [transport_tapes_apply]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem fromBoolTapes_update (base : Tape → List Bool) (tape : Tape) (word : List Bool) :
    fromBoolTapes (Function.update base tape word) =
      Function.update (fromBoolTapes base) tape (boolWord tape word) := by
  funext k
  by_cases h : k = tape
  · subst k
    simp [fromBoolTapes]
  · simp [fromBoolTapes, h]

@[simp] theorem toBoolTapes_update (base : (tape : Tape) → List (Alphabet tape))
    (tape : Tape) (word : List (Alphabet tape)) :
    toBoolTapes (Function.update base tape word) =
      Function.update (toBoolTapes base) tape (toBoolWord tape word) := by
  funext k
  by_cases h : k = tape
  · subst k
    simp [toBoolTapes]
  · simp [toBoolTapes, h]

theorem configuration_fromBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : Tape → List Bool) :
    MachineAlphabetTransport.configuration alphabet_eq.symm ⟨label, state, base⟩ =
      ⟨label, state, fromBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, fromBoolTapes_eq_transport]

theorem configuration_toBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : (tape : Tape) → List (Alphabet tape)) :
    MachineAlphabetTransport.configuration alphabet_eq ⟨label, state, base⟩ =
      ⟨label, state, toBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, toBoolTapes_eq_transport]

end

section

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem controlStatementInverse {K Λ σ τ : Type} {Γ : K → Type}
    (states : σ ≃ τ) (q : TM2.Stmt Γ Λ σ) :
    MachineControl.statement id states.symm (MachineControl.statement id states q) = q := by
  induction q <;>
    simp_all only [MachineControl.statement, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, id_eq]

theorem controlTrace {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (states : σ ≃ τ) (target : Λ → TM2.Stmt Γ Λ τ)
    (n : Nat) (start finish : TM2.Cfg Γ Λ σ)
    (run : (advance (TM2.step (MachineControl.program (Equiv.refl Λ) states.symm target)))^[n]
      (some start) = some finish) :
    (advance (TM2.step target))^[n]
      (some (MachineControl.configuration id states start)) =
      some (MachineControl.configuration id states finish) := by
  let source := MachineControl.program (Equiv.refl Λ) states.symm target
  have roundtrip : MachineControl.program (Equiv.refl Λ) states source = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact controlStatementInverse states.symm _
  have simulation : ∀ a b, TM2.step source a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states source a
    rw [roundtrip, hab] at h
    exact h
  exact liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (MachineControl.configuration id states) simulation n start finish run

theorem controlDrainTrace {K Λ σ τ : Type} [DecidableEq K]
    (states : (σ × Option Bool) ≃ τ) (source : K) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (code : target again = MachineControl.statement id states
      (MachineDrain.drain source again exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none), Function.update base source []⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = MachineDrain.drain source again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact controlStatementInverse states _
  have run := MachineDrain.drainTrace source again exit raw atRaw base (base source) ambient register
  simp only [Function.update_eq_self] at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id] using
    controlTrace states target ((base source).length + 1) _ _ run

theorem controlTransferTrace {K Λ σ τ : Type} [DecidableEq K]
    (states : (σ × Option Bool) ≃ τ) (source destination : K)
    (distinct : source ≠ destination) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (code : target again = MachineControl.statement id states
      (Reduction.MachineTransfer.loopAt source destination id false again exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none),
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = Reduction.MachineTransfer.loopAt source destination id false again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact controlStatementInverse states _
  have run := Reduction.MachineTransfer.transferAt_fromTapes source destination distinct id false
    again exit raw atRaw base ambient register
  unfold Reduction.MachineTransfer.nextAt at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id,
    List.map_id] using controlTrace states target ((base source).length + 1) _ _ run

variable {ρ : Type} {d : Nat}

def clearRegister (state : State ρ d) : State ρ d :=
  (MachineExpanderTable.clearRegister state.1, state.2)

@[simp] theorem registerStates_reset (state : State ρ d) :
    registerStates ρ d (((registerStates ρ d).symm state).1, none) =
      clearRegister state := rfl

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

@[simp] theorem caller_clearRegister (state : State ρ d) :
    caller (clearRegister state) = caller state := rfl

@[simp] theorem clearRegister_position (state : State ρ d) :
    (clearRegister state).1.2 = state.1.2 := rfl

@[simp] theorem clearRegister_register (state : State ρ d) :
    (clearRegister state).1.1.2 = none := rfl

variable [Fintype ρ]

theorem boolTraceActual (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (n : Nat)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : (advance (TM2.step (boolView positive H growth)))^[n] (some start) = some finish) :
    (advance (TM2.step (program positive H growth)))^[n]
      (some (MachineAlphabetTransport.configuration alphabet_eq.symm start)) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.successfulTrace alphabet_eq.symm
    (boolView positive H growth) n start finish run
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip] using h

theorem drainBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source : Tape) (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again = drainStatement source again next)
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state, Function.update base source []⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (MachineDrain.drain source (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
    rfl
  have h := controlDrainTrace (registerStates ρ d) source (.inr again) (some (.inr next))
    (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

theorem transferBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source destination : Tape) (distinct : source ≠ destination)
    (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) source destination id false
          (.inr again) (some (.inr next))))
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state,
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt source destination id false
          (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
  have h := controlTransferTrace (registerStates ρ d) source destination distinct
    (.inr again) (some (.inr next)) (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

def installedTapes (base : Tape → List Bool) (newWord : List Bool) : Tape → List Bool :=
  Function.update
    (Function.update
      (Function.update (Function.update base tableTape newWord) resultTape [])
      (.inr .tableReverse) [])
    (.inr .currentSize) []

def cleanedCounterTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update base inputVertexTape []) vertexCountTape []

theorem installTableBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (newWord : List Bool)
    (resultWord : base resultTape = newWord) (reverseEmpty : base (.inr .tableReverse) = [])
    (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base tableTape).length + 2 * newWord.length + (base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        installedTapes base newWord⟩ := by
  let b0 := Function.update base tableTape []
  let b1 := Function.update (Function.update b0 resultTape []) (.inr .tableReverse) newWord.reverse
  let b2 := Function.update (Function.update b1 (.inr .tableReverse) []) tableTape newWord
  let b3 := Function.update b2 (.inr .currentSize) []
  have h0 := drainBoolTrace positive H growth tableTape .clearOldTable .reverseResult rfl base state
  have b0Result : b0 resultTape = newWord := by
    simpa [b0, tableTape, resultTape] using resultWord
  have b0Reverse : b0 (.inr .tableReverse) = [] := by
    simpa [b0, tableTape] using reverseEmpty
  have h1 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseResult), clearRegister state, b0⟩) =
      some ⟨some (.inr .reverseTable), clearRegister state, b1⟩ := by
    simpa only [b0Result, b0Reverse, List.append_nil, Reduction.MachineTransfer.tapesAt,
      clearRegister_idempotent] using
      transferBoolTrace positive H growth resultTape (.inr .tableReverse) (by decide)
        .reverseResult .reverseTable rfl b0 (clearRegister state)
  have b1Reverse : b1 (.inr .tableReverse) = newWord.reverse := by simp [b1]
  have b1Table : b1 tableTape = [] := by simp [b1, b0, tableTape, resultTape]
  have h2 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseTable), clearRegister state, b1⟩) =
      some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩ := by
    simpa only [b1Reverse, b1Table, List.reverse_reverse, List.length_reverse,
      List.append_nil, Reduction.MachineTransfer.tapesAt, clearRegister_idempotent] using
      transferBoolTrace positive H growth (.inr .tableReverse) tableTape (by decide)
        .reverseTable .clearCurrentSize rfl b1 (clearRegister state)
  have b2Current : b2 (.inr .currentSize) = base (.inr .currentSize) := by
    simp [b2, b1, b0, tableTape, resultTape]
  have h3 : (advance (TM2.step (boolView positive H growth)))^[
      (base (.inr .currentSize)).length + 1]
      (some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state, b3⟩ := by
    simpa only [b2Current, clearRegister_idempotent] using
      drainBoolTrace positive H growth (.inr .currentSize) .clearCurrentSize
        (.affine .multiplySize .seed) rfl b2 (clearRegister state)
  have final : b3 = installedTapes base newWord := by
    funext tape
    rcases tape with table | extra
    · rcases table with row | tableExtra
      · cases row <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
      · cases tableExtra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
    · cases extra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
  rw [show (base tableTape).length + 2 * newWord.length +
        (base (.inr .currentSize)).length + 4 =
      ((base (.inr .currentSize)).length + 1) +
        ((newWord.length + 1) + ((newWord.length + 1) + ((base tableTape).length + 1))) by omega,
    Function.iterate_add_apply _ ((base (.inr .currentSize)).length + 1),
    Function.iterate_add_apply _ (newWord.length + 1) ((newWord.length + 1) + ((base tableTape).length + 1)),
    Function.iterate_add_apply _ (newWord.length + 1) ((base tableTape).length + 1),
    h0, h1, h2, h3, final]

theorem cleanupCountersBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base inputVertexTape).length + (base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state, cleanedCounterTapes base⟩ := by
  have h0 := drainBoolTrace positive H growth inputVertexTape .drainInputVertex .drainVertexCount
    rfl base state
  have count : (Function.update base inputVertexTape []) vertexCountTape = base vertexCountTape := by
    simp [inputVertexTape, vertexCountTape]
  have h1 := drainBoolTrace positive H growth vertexCountTape .drainVertexCount .levelGuard
    rfl (Function.update base inputVertexTape []) (clearRegister state)
  simp only [count, clearRegister_idempotent] at h1
  rw [show (base inputVertexTape).length + (base vertexCountTape).length + 2 =
      ((base vertexCountTape).length + 1) + ((base inputVertexTape).length + 1) by omega,
    Function.iterate_add_apply, h0]
  exact h1

theorem installTableTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base tableTape).length + 2 * newWord.length +
          (toBoolTapes base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩ := by
  have h := installTableBoolTrace positive H growth (toBoolTapes base) newWord resultWord reverseEmpty state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

theorem cleanupCountersTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩ := by
  have h := cleanupCountersBoolTrace positive H growth (toBoolTapes base) state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

def installTableInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), state, base⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩)
      ((toBoolTapes base tableTape).length + 2 * newWord.length +
        (toBoolTapes base (.inr .currentSize)).length + 4) where
  steps := (toBoolTapes base tableTape).length + 2 * newWord.length +
    (toBoolTapes base (.inr .currentSize)).length + 4
  evals_in_steps := installTableTrace positive H growth base newWord resultWord reverseEmpty state
  steps_le_m := Nat.le_refl _

def cleanupCountersInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), state, base⟩
      (some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩)
      ((toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2) where
  steps := (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2
  evals_in_steps := cleanupCountersTrace positive H growth base state
  steps_le_m := Nat.le_refl _

end

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem affine_source_ne_scratch (phase : AffinePhase) :
    affineSource phase ≠ .inr .unaryScratch := by cases phase <;> decide

theorem affine_source_ne_destination (phase : AffinePhase) :
    affineSource phase ≠ affineDestination phase := by cases phase <;> decide

theorem affine_scratch_ne_destination (phase : AffinePhase) :
    (.inr .unaryScratch : Tape) ≠ affineDestination phase := by cases phase <;> decide

def affineResultTapes (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    (tape : Tape) → List (Alphabet tape) :=
  Function.update base (affineDestination phase)
    (boolWord (affineDestination phase)
      (encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase)))

theorem affineResultTapes_other (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (tape : Tape)
    (different : tape ≠ affineDestination phase) :
    affineResultTapes d phase base n tape = base tape := by
  simp [affineResultTapes, different]

theorem affineResultTapes_source (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    affineResultTapes d phase base n (affineSource phase) = base (affineSource phase) :=
  affineResultTapes_other d phase base n _ (affine_source_ne_destination phase)

theorem affineResultTapes_scratch (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    affineResultTapes d phase base n (.inr .unaryScratch) = base (.inr .unaryScratch) :=
  affineResultTapes_other d phase base n _ (affine_scratch_ne_destination phase)

theorem affineResultTapes_destination (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    toBoolTapes (affineResultTapes d phase base n) (affineDestination phase) =
      encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase) := by
  simp [affineResultTapes, toBoolTapes]

variable {ρ : Type} [Fintype ρ] {d : Nat}

theorem affinePhaseBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (sourceWord : base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        Function.update base (affineDestination phase)
          (encodeWord (affineCoefficient d phase * n) ++ base (affineDestination phase))⟩ := by
  let states := registerStates ρ d
  let target := boolView (ρ := ρ) positive H growth
  let sourceProgram := MachineControl.program (Equiv.refl (Label d)) states.symm target
  have atSeed : sourceProgram (.inr (.affine phase .seed)) =
      MachineUnaryAffineAt.seed (affineDestination phase) 0 (.inr (.affine phase .scan)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .seed))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atScan : sourceProgram (.inr (.affine phase .scan)) =
      MachineUnaryAffineAt.scan (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .scan))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atRestore : sourceProgram (.inr (.affine phase .restore)) =
      Reduction.MachineTransfer.loopAt (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .restore))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have raw := MachineUnaryAffineAt.seededAffineTrace
    (affineSource phase) (.inr .unaryScratch) (affineDestination phase)
    (affine_source_ne_scratch phase) (affine_source_ne_destination phase)
    (affine_scratch_ne_destination phase) (affineCoefficient d phase) 0
    (.inr (.affine phase .seed)) (.inr (.affine phase .scan)) (.inr (.affine phase .restore))
    (some (affineExit d phase)) sourceProgram atSeed atScan atRestore base n suffix
    sourceWord scratchEmpty (states.symm state).1 (states.symm state).2
  have run := controlTrace states target (2 * (n + 1) + 1) _ _ raw
  simpa only [states, target, MachineControl.configuration, Option.map_some, id_eq, Prod.mk.eta,
    Equiv.apply_symm_apply, Nat.add_zero, registerStates_reset] using run

theorem affinePhaseTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩ := by
  have raw := affinePhaseBoolTrace positive H growth phase (toBoolTapes base) n suffix
    sourceWord scratchEmpty state
  have transported := boolTraceActual positive H growth (2 * (n + 1) + 1) _ _ raw
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    affineResultTapes] using transported

def affinePhaseInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine phase .seed)), state, base⟩
      (some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩) (2 * (n + 1) + 1) where
  steps := 2 * (n + 1) + 1
  evals_in_steps := affinePhaseTrace positive H growth phase base n suffix sourceWord scratchEmpty state
  steps_le_m := Nat.le_refl _

def copyCountInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base (.inr .currentSize) = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base vertexCountTape = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .copyCount .seed)), state, base⟩
      (some ⟨some (.inl (.inr .initialize)), clearRegister state,
        Function.update base vertexCountTape (encodeWord n)⟩) (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .copyCount base n []
    (by simpa only [affineSource, toBoolTapes, toBoolWord, List.append_nil] using sourceWord)
    scratchEmpty state
  change base (.inl (.inr .vertexCount)) = [] at destinationEmpty
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    Nat.one_mul, vertexCountTape, boolWord, toBoolTapes, toBoolWord,
    destinationEmpty, List.append_nil] using run

def multiplySizeInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base inputVertexTape = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base (.inr .currentSize) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .multiplySize .seed)), state, base⟩
      (some ⟨some (.inr .drainInputVertex), clearRegister state,
        Function.update base (.inr .currentSize) (encodeWord (cloudSize d * n))⟩)
      (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .multiplySize base n []
    (by simpa only [affineSource, inputVertexTape, toBoolTapes, toBoolWord,
      List.append_nil] using sourceWord)
    scratchEmpty state
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    boolWord, toBoolTapes, toBoolWord, destinationEmpty, List.append_nil] using run

end BinPackingGames.Foundations.Complexity.MachineExpanderFamily

end OAI
