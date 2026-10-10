import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineUnaryAffine
import OAI.Combinatorics.IndependentSets.Expansion.ExpanderTableWords
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderTableProgram
import OAI.Combinatorics.IndependentSets.Machines.MachineAlphabetTransport

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

inductive ExtraTape
  | remainingLevel | currentSize | unaryScratch | tableReverse
  deriving DecidableEq

instance : Fintype ExtraTape where
  elems := {.remainingLevel, .currentSize, .unaryScratch, .tableReverse}
  complete tape := by cases tape <;> simp

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

instance : Fintype AffinePhase where
  elems := {.copyCount, .multiplySize}
  complete phase := by cases phase <;> simp

inductive AffineLabel
  | seed | scan | restore
  deriving DecidableEq

instance : Fintype AffineLabel where
  elems := {.seed, .scan, .restore}
  complete label := by cases label <;> simp

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

end IndependentSetsGames.Foundations.Complexity.MachineExpanderFamily

end OAI
