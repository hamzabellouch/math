import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineFixedBlockMap
import OAI.Combinatorics.IndependentSets.Machines.MachineStateEquiv
import OAI.Combinatorics.IndependentSets.Machines.MachineAlphabetTransport
import OAI.Combinatorics.IndependentSets.Machines.MachineUnaryLess
import OAI.Combinatorics.IndependentSets.Machines.Alphabet

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow
open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
variable {K Λ σ : Type} [DecidableEq K]
abbrev SelectAlphabet (_ : SelectTape) := Bool

theorem selectAlphabet_eq : RawSelectAlphabet = SelectAlphabet := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => rfl

def selectToBoolWord : (k : SelectTape) → List (RawSelectAlphabet k) → List Bool
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def selectToBoolTapes (base : ∀ k, List (RawSelectAlphabet k)) : SelectTape → List Bool :=
  fun k => selectToBoolWord k (base k)

private theorem alphabet_tapes_apply {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : ∀ k, List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem selectToBoolTapes_eq (base : ∀ k, List (RawSelectAlphabet k)) :
    selectToBoolTapes base = MachineAlphabetTransport.tapes selectAlphabet_eq base := by
  funext k
  rw [alphabet_tapes_apply]
  cases k with
  | inl k => cases k <;> rfl
  | inr k => rfl

abbrev SelectState (σ : Type) := MachineUnaryLessAt.State (σ × MachineCloudSelect.Phase)

def selectStateEquiv (σ : Type) : (MachineCloudSelect.State σ × Unit) ≃ SelectState σ where
  toFun s := (((s.1.1.1.1, s.1.2), s.1.1.1.2), s.1.1.2)
  invFun s := ((((s.1.1.1, s.1.2), s.2), s.1.1.2), ())
  left_inv s := by rcases s with ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, ⟨⟩⟩; rfl
  right_inv s := by rcases s with ⟨⟨⟨a, b⟩, c⟩, d⟩; rfl

def selectScratch : SelectTape := .inl (.inl .scratch)
def selectQuery : SelectTape := .inl (.inl .target)
def selectOutput : SelectTape := .inl (.inr ())

def compareSlots : Fin 4 ↪ SelectTape where
  toFun i := ![.inr .localIndex, .inr .cloudSize, .inr .savedLeft, .inr .savedRight] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def subtractSlots : Fin 4 ↪ SelectTape where
  toFun i := ![.inr .localWork, .inr .sizeWork, .inr .savedLeft, .inr .savedRight] i
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

inductive SelectCopy
  | oldLocal | oldOwner | dummyLocal | dummySize | dummyDifference
  deriving DecidableEq

instance : Fintype SelectCopy where
  elems := {.oldLocal, .oldOwner, .dummyLocal, .dummySize, .dummyDifference}
  complete kind := by cases kind <;> simp

inductive SelectAdd
  | prefixOffset | darts
  deriving DecidableEq

instance : Fintype SelectAdd where
  elems := {.prefixOffset, .darts}
  complete kind := by cases kind <;> simp

inductive SelectAddStage | scan | restore
  deriving DecidableEq

instance : Fintype SelectAddStage where
  elems := {.scan, .restore}
  complete stage := by cases stage <;> simp

inductive SelectControl
  | compare (stage : MachineUnaryLessAt.Label)
  | choose
  | copy (kind : SelectCopy) (stage : MachineUnaryAffineAt.Label)
  | subtract
  | add (kind : SelectAdd) (stage : SelectAddStage)
  | cleanup (i : Fin 5)
  deriving DecidableEq, Fintype

abbrev SelectLabel := MachineCloudSelect.Label ⊕ SelectControl

def copySource : SelectCopy → SelectTape
  | .oldLocal | .dummyLocal => .inr .localIndex
  | .oldOwner => .inr .owner
  | .dummySize => .inr .cloudSize
  | .dummyDifference => .inr .localWork

def copyDestination : SelectCopy → SelectTape
  | .oldLocal | .oldOwner => selectQuery
  | .dummyLocal => .inr .localWork
  | .dummySize => .inr .sizeWork
  | .dummyDifference => selectOutput

def afterCopy : SelectCopy → SelectLabel
  | .oldLocal => .inr (.copy .oldOwner .seed)
  | .oldOwner => .inl (.inr .initialize)
  | .dummyLocal => .inr (.copy .dummySize .seed)
  | .dummySize => .inr .subtract
  | .dummyDifference => .inr (.add .prefixOffset .scan)

def addSource : SelectAdd → SelectTape
  | .prefixOffset => .inr .prefixOffset
  | .darts => .inr .darts

def afterAdd : SelectAdd → SelectLabel
  | .prefixOffset => .inr (.add .darts .scan)
  | .darts => .inr (.cleanup 0)

def cleanupTape (i : Fin 5) : SelectTape :=
  ![selectQuery, .inr .localWork, .inr .sizeWork, .inr .savedLeft, .inr .savedRight] i

def afterCleanup (i : Fin 5) : Option SelectLabel :=
  if h : i.val + 1 < 5 then some (.inr (.cleanup ⟨i.val + 1, h⟩)) else none

def selectControl : SelectControl → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ)
  | .compare stage => MachineUnaryLessAt.statement compareSlots
      (fun s => .inr (.compare s)) (some (.inr .choose)) stage
  | .choose => .branch (fun s => s.1.2)
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .oldLocal .seed)))
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .dummyLocal .seed)))
  | .copy kind .seed => MachineUnaryAffineAt.seed (copyDestination kind) 0
      (.inr (.copy kind .scan))
  | .copy kind .scan => MachineUnaryAffineAt.scan (copySource kind) selectScratch
      (copyDestination kind) 1 (.inr (.copy kind .scan)) (.inr (.copy kind .restore))
  | .copy kind .restore => Reduction.MachineTransfer.loopAt selectScratch (copySource kind)
      id false (.inr (.copy kind .restore)) (some (afterCopy kind))
  | .subtract => MachineUnaryLessAt.scan subtractSlots (.inr .subtract)
      (.inr (.copy .dummyDifference .seed))
  | .add kind .scan => MachineUnaryAffineAt.scan (addSource kind) selectScratch selectOutput 1
      (.inr (.add kind .scan)) (.inr (.add kind .restore))
  | .add kind .restore => Reduction.MachineTransfer.loopAt selectScratch (addSource kind)
      id false (.inr (.add kind .restore)) (some (afterAdd kind))
  | .cleanup i => MachineDrain.drain (cleanupTape i) (.inr (.cleanup i)) (afterCleanup i)

def rawSelectProgram : SelectLabel → TM2.Stmt RawSelectAlphabet SelectLabel (SelectState σ) :=
  MachineStateEquiv.program (selectStateEquiv σ)
    (MachineEmbedding.program (some (.inr (.cleanup 0))) MachineCloudSelect.program
      (fun control => MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl control))))

def selectProgram : SelectLabel → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ) :=
  MachineAlphabetTransport.program selectAlphabet_eq rawSelectProgram

@[simp] theorem selectProgram_control (l : SelectControl) :
    selectProgram (σ := σ) (.inr l) = selectControl l := by
  change MachineAlphabetTransport.statement selectAlphabet_eq
    (MachineStateEquiv.statement (selectStateEquiv σ)
      (MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl l)))) = _
  have h := MachineStateEquiv.statement_symm_statement (selectStateEquiv σ).symm
    (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl (σ := σ) l))
  simp only [Equiv.symm_symm] at h
  rw [h]
  exact MachineAlphabetTransport.statement_roundtrip selectAlphabet_eq _

def selectCleanState (ambient : σ) (register : Option Bool) : SelectState σ :=
  (((ambient, .checking), false), register)

theorem selectComparisonTrace (base : SelectTape → List Bool) (j k : Nat)
    (hj : base (.inr .localIndex) = encodeWord j)
    (hk : base (.inr .cloudSize) = encodeWord k)
    (hl : base (.inr .savedLeft) = []) (hr : base (.inr .savedRight) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[MachineUnaryLessAt.steps j k + 1]
      (some ⟨some (.inr (.compare .scan)), selectCleanState ambient register, base⟩) =
      some ⟨some (.inr (.copy (if j < k then .oldLocal else .dummyLocal) .seed)),
        selectCleanState ambient none, base⟩ := by
  have h := MachineUnaryLessAt.lessThanTrace compareSlots
    (fun l => .inr (.compare l)) (some (.inr .choose)) selectProgram
    (fun l => by rw [selectProgram_control]; rfl)
    base j k [] [] (by change base (.inr .localIndex) = _; simpa only [List.append_nil] using hj)
    (by change base (.inr .cloudSize) = _; simpa only [List.append_nil] using hk) hl hr
    (ambient, MachineCloudSelect.Phase.checking) false register
  simp only [selectCleanState]
  rw [Function.iterate_succ_apply', h, advance_some]
  change some (TM2.stepAux (selectProgram (.inr .choose)) _ _) = _
  rw [selectProgram_control]
  by_cases hlt : j < k <;> simp [selectControl, TM2.stepAux, hlt]

theorem selectCopyTrace (kind : SelectCopy) (base : SelectTape → List Bool)
    (a : Nat) (hword : base (copySource kind) = encodeWord a)
    (hscratch : base selectScratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[2 * (a + 1) + 1]
      (some ⟨some (.inr (.copy kind .seed)), selectCleanState ambient register, base⟩) =
      some ⟨some (afterCopy kind), selectCleanState ambient none,
        Function.update base (copyDestination kind)
          (encodeWord a ++ base (copyDestination kind))⟩ := by
  have h₁ : copySource kind ≠ selectScratch := by cases kind <;> decide
  have h₂ : copySource kind ≠ copyDestination kind := by cases kind <;> decide
  have h₃ : selectScratch ≠ copyDestination kind := by cases kind <;> decide
  simpa only [Nat.one_mul, Nat.add_zero, selectCleanState] using
    MachineUnaryAffineAt.seededAffineTrace (copySource kind) selectScratch (copyDestination kind)
      h₁ h₂ h₃ 1 0 (.inr (.copy kind .seed)) (.inr (.copy kind .scan))
      (.inr (.copy kind .restore)) (some (afterCopy kind)) selectProgram
      (by rw [selectProgram_control]; rfl) (by rw [selectProgram_control]; rfl)
      (by rw [selectProgram_control]; rfl) base a [] (by simpa using hword) hscratch
      ((ambient, MachineCloudSelect.Phase.checking), false) register

theorem selectAddTrace (kind : SelectAdd) (base : SelectTape → List Bool)
    (a b : Nat) (hword : base (addSource kind) = encodeWord a)
    (houtput : base selectOutput = encodeWord b) (hscratch : base selectScratch = [])
    (ambient : σ) :
    (advance (TM2.step selectProgram))^[2 * (a + 1)]
      (some ⟨some (.inr (.add kind .scan)), selectCleanState ambient none, base⟩) =
      some ⟨some (afterAdd kind), selectCleanState ambient none,
        Function.update base selectOutput (encodeWord (a + b))⟩ := by
  have h₁ : addSource kind ≠ selectScratch := by cases kind <;> decide
  have h₂ : addSource kind ≠ selectOutput := by cases kind <;> decide
  have h₃ : selectScratch ≠ selectOutput := by decide
  have frame (n : Nat) : MachineUnaryAffineAt.tapes (addSource kind) selectScratch selectOutput
      base (encodeWord a ++ []) [] (encodeWord n ++ []) =
        Function.update base selectOutput (encodeWord n) := by
    simp only [List.append_nil]
    rw [← hword, ← hscratch]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have h := MachineUnaryAffineAt.affineTrace (addSource kind) selectScratch selectOutput
    h₁ h₂ h₃ 1 (.inr (.add kind .scan)) (.inr (.add kind .restore))
    (some (afterAdd kind)) selectProgram
    (by rw [selectProgram_control]; rfl) (by rw [selectProgram_control]; rfl)
    base a b [] [] ((ambient, MachineCloudSelect.Phase.checking), false) none
  rw [frame, frame] at h
  rw [← houtput, Function.update_eq_self] at h
  simpa only [Nat.one_mul, selectCleanState] using h

abbrev CoreTape := Fin 27
abbrev CoreState (σ : Type) (q : Nat) :=
  (σ × (MachineFixedBlockMap.Buffer 4096 ×
    (Fin q × (Bool × MachineCloudSelect.Phase)))) × Option Bool

inductive CoreLabel (q : Nat)
  | rotor (stage : RotorLabel q)
  | select (stage : SelectLabel)
  | finish (stage : FinishLabel)
  | cleanup (i : Fin 10)
  deriving DecidableEq, Fintype

def coreEntry (q : Nat) : CoreLabel q := .rotor (.lookup .seed)

theorem selectCloudTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v))
    (extra : SelectExtraTape → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[MachineCloudSelect.cloudSelectSteps t v i []]
      (some ⟨some (.inl (.inr .initialize)), selectCleanState ambient register,
        selectToBoolTapes (MachineEmbedding.tapes
          (MachineCloudSelect.memory (GraphTables.tableBits t) []
            (MachineCloudSelect.queryWord v.val i.val []) [] [] [] []) extra)⟩) =
      some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
        selectToBoolTapes (MachineEmbedding.tapes
          (MachineCloudSelect.memory (GraphTables.tableBits t) []
            (MachineCloudSelect.queryWord v.val i.val []) [] [] []
            (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val)) extra)⟩ := by
  let source := MachineCloudSelect.program (σ := σ)
  let more := fun c => MachineStateEquiv.statement (selectStateEquiv σ).symm
    (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl (σ := σ) c))
  let caller := MachineEmbedding.program (some (.inr (.cleanup 0))) source more
  let embed := MachineEmbedding.configuration (K := MachineCloudSelect.Tape)
    (Γ := MachineCloudSelect.Alphabet) (σ := MachineCloudSelect.State σ)
    (some (Sum.inr (SelectControl.cleanup 0)) : Option SelectLabel) () extra
  have sourceRun := MachineCloudSelect.cloudSelectTrace t v i [] [] ambient register
  have lifted := liftSuccessfulTrace (TM2.step source) (TM2.step caller) embed
    (MachineEmbedding.step_simulation (some (.inr (.cleanup 0))) () extra source more)
    _ _ _ sourceRun
  have transported := MachineStateEquiv.trace (selectStateEquiv σ) caller _ _ _ lifted
  have boolean := MachineAlphabetTransport.successfulTrace selectAlphabet_eq
    (MachineStateEquiv.program (selectStateEquiv σ) caller) _ _ _ transported
  simp only [embed, MachineCloudSelect.cfg, MachineStateEquiv.configuration, MachineEmbedding.configuration,
    MachineEmbedding.label, selectStateEquiv, List.append_nil,
    MachineAlphabetTransport.configuration_mk, ← selectToBoolTapes_eq] at boolean
  convert boolean using 1 <;> rfl

def selectExtraMemory (j v k offset m : Nat)
    (savedLeft savedRight localWork sizeWork : List Bool) :
    SelectExtraTape → List Bool
  | .localIndex => encodeWord j
  | .owner => encodeWord v
  | .cloudSize => encodeWord k
  | .prefixOffset => encodeWord offset
  | .darts => encodeWord m
  | .savedLeft => savedLeft
  | .savedRight => savedRight
  | .localWork => localWork
  | .sizeWork => sizeWork

def selectMemory (graph : List Bool) (j v k offset m : Nat)
    (query output savedLeft savedRight localWork sizeWork : List Bool) :
    SelectTape → List Bool :=
  selectToBoolTapes (MachineEmbedding.tapes
    (MachineCloudSelect.memory graph [] query [] [] [] output)
    (selectExtraMemory j v k offset m savedLeft savedRight localWork sizeWork))

@[simp] theorem selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectQuery = query := rfl

@[simp] theorem selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectOutput = output := rfl

@[simp] theorem selectMemory_scratch (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectScratch = [] := rfl

@[simp] theorem selectMemory_extra (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) (z : SelectExtraTape) :
    selectMemory graph j v k o m query output a b c d (.inr z) =
      selectExtraMemory j v k o m a b c d z := rfl

@[simp] theorem update_selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectQuery word =
      selectMemory graph j v k o m word output a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectOutput word =
      selectMemory graph j v k o m query word a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_local (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .localWork) word =
      selectMemory graph j v k o m query output a b word d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_size (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .sizeWork) word =
      selectMemory graph j v k o m query output a b c word := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_left (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedLeft) word =
      selectMemory graph j v k o m query output word b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_right (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedRight) word =
      selectMemory graph j v k o m query output a word c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

theorem selectCleanupTrace (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) (ambient : σ) :
    (advance (TM2.step selectProgram))^[query.length + c.length + d.length + a.length + b.length + 5]
      (some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
        selectMemory graph j v k o m query output a b c d⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory graph j v k o m [] output [] [] [] []⟩ := by
  have h0 := MachineDrain.drainTrace selectQuery (.inr (.cleanup 0))
    (some (.inr (.cleanup 1))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m query output a b c d) query
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_query] at h0
  have h1 := MachineDrain.drainTrace (.inr .localWork) (.inr (.cleanup 1))
    (some (.inr (.cleanup 2))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b c d) c
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_local] at h1
  have h2 := MachineDrain.drainTrace (.inr .sizeWork) (.inr (.cleanup 2))
    (some (.inr (.cleanup 3))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b [] d) d
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_size] at h2
  have h3 := MachineDrain.drainTrace (.inr .savedLeft) (.inr (.cleanup 3))
    (some (.inr (.cleanup 4))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b [] []) a
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_left] at h3
  have h4 := MachineDrain.drainTrace (.inr .savedRight) (.inr (.cleanup 4))
    none selectProgram (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output [] b [] []) b
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_right] at h4
  have total := joinTrace (joinTrace (joinTrace (joinTrace h0 h1) h2) h3) h4
  have hn : query.length + c.length + d.length + a.length + b.length + 5 =
      ((((query.length + 1) + (c.length + 1)) + (d.length + 1)) + (a.length + 1)) +
        (b.length + 1) := by omega
  rw [hn]
  exact total

end IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
