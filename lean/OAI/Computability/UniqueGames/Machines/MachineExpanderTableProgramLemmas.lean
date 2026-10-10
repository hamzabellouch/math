import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineControlLemmas
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineExpanderRowDivision
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineUnaryAffineAt

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

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

/-- Static movement of the bit register to the last product coordinate. -/
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

/-- A fresh row call, with its residue and bit register reset. -/
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

/-- The unary guard specialized to the concrete extra tape. The zero delimiter
is retained; both branches clear the bit register. Its dependent alphabet is
the same alphabet used by the embedded row program. -/
def vertexGuardCore {ρ : Type} {d : Nat} :
    TM2.Stmt Alphabet (Label d) ((RowStatePrefix ρ d × Position d) × Option Bool) :=
  .peek (.inr .vertexCount) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.pop (.inr .vertexCount) (fun s _ => (s.1, none))
        (.goto fun _ => .inr .prepareRow))
      (.load (fun s => (s.1, none)) (.goto fun _ => .inr .reverseOutput)))

variable {ρ : Type} [Fintype ρ]

/-- Actual statements for the table loop. No unbounded natural number is
stored in the state or evaluated by a state-update function. -/
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

/-- The complete finite program. The vertex count is supplied on a tape,
while the small table and all finite control types depend only on fixed `d`. -/
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

/-- Every transition of an actual row run embeds with its original cost,
preserving the position and both extra tapes, including its return jump. -/
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

/-- Before initialization, only the old table and remaining-count word are
populated. The program itself creates the initial vertex delimiter. -/
def initialTapes (vertices : Nat) (oldTable countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes
    (fun tape => match tape with | .table => oldTable | _ => [])
    (extraTapes vertices countSuffix [])

def finalTapes (vertices : Nat) (oldTable output countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes vertices 0 oldTable [] countSuffix output

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

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

/-- All physical tapes contain Booleans. This equality changes the static
type presentation only; no runtime symbol conversion is performed. -/
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

/-- The literal used by initialization is exactly the actual family's base. -/
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

/-- Uniform-alphabet presentation of the actual outer code. All arithmetic
parameters here are fixed program constants; runtime sizes are scanned. -/
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

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
