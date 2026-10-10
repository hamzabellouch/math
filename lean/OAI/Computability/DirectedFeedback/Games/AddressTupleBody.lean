import Mathlib
import OAI.Computability.DirectedFeedback.Games.UniformReduction

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount
abbrev Rows (k : Nat) := List (MachineOutcomeRows.Row k (4*k) (1+9*k))
abbrev Slots (k s d noiseCount : Nat) := AddressMachineSpace.addressEdgeSlots k s d noiseCount
abbrev BodyState (k : Nat) := AddressMachineSpace.State k
abbrev CleanupLabel (k s d noiseCount : Nat) :=
  AddressTupleCleanup.Label k s d noiseCount
abbrev RowLabel (k s d noiseCount : Nat) (rows : Rows k) :=
  MachineOutcomeRows.Label (Slots k s d noiseCount) rows
abbrev Label (k s d noiseCount : Nat) (rows : Rows k) :=
  MachineSourceTuple.Label k ⊕ (Unit ⊕
    (RowLabel k s d noiseCount rows ⊕ (CleanupLabel k s d noiseCount ⊕ Unit)))

instance labelFintype (rows : Rows k) : Fintype (Label k s d noiseCount rows) := by
  unfold Label CleanupLabel RowLabel
  infer_instance

variable {rows : Rows k}

def sourceLabels (labels : Label k s d noiseCount rows → Λ) : MachineSourceTuple.Label k → Λ :=
  fun l => labels (.inl l)
def rhsLabel (labels : Label k s d noiseCount rows → Λ) : Λ := labels (.inr (.inl ()))
def rowLabels (labels : Label k s d noiseCount rows → Λ) : RowLabel k s d noiseCount rows → Λ :=
  fun l => labels (.inr (.inr (.inl l)))
def cleanupLabels (labels : Label k s d noiseCount rows → Λ) : CleanupLabel k s d noiseCount → Λ :=
  fun l => labels (.inr (.inr (.inr (.inl l))))
def resetLabel (labels : Label k s d noiseCount rows → Λ) : Λ :=
  labels (.inr (.inr (.inr (.inr ()))))

def main (rows : Rows k) : Label k s d noiseCount rows := .inl (MachineSourceTuple.labelAt 0)

def reset (exit : Option Λ) : TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k) :=
  .load (fun _ => initialState k) (MachineFieldTemplate.jump exit)

def instruction (rows : Rows k) (labels : Label k s d noiseCount rows → Λ) (exit : Option Λ) :
    Label k s d noiseCount rows →
      TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k)
  | .inl l => MachineSubroutine.statement (sourceLabels labels) (some (rhsLabel labels))
      (MachineSourceTuple.program l)
  | .inr (.inl _) => MachineRhsLoad.statement (rhsField k s d noiseCount)
      (some (rowLabels labels (.inl ())))
  | .inr (.inr (.inl l)) => MachineOutcomeRows.instruction (Slots k s d noiseCount) rows
      (rowLabels labels)
      (AddressTupleCleanup.entry k s d noiseCount (cleanupLabels labels) (some (resetLabel labels))) l
  | .inr (.inr (.inr (.inl l))) => AddressTupleCleanup.instruction k s d noiseCount
      (cleanupLabels labels) (some (resetLabel labels)) l
  | .inr (.inr (.inr (.inr _))) => reset exit

def program (rows : Rows k) : Label k s d noiseCount rows →
    TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) (Label k s d noiseCount rows) (BodyState k) :=
  instruction rows id none

def rhs (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) : Fin k → Bool :=
  fun j => F.equations[(tuple j).val].rhs

def loaded (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  MachineSourceTuple.stageTapes F tuple base k

def tupleBits (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) : List Bool :=
  (MachineOutcomeRows.selected rows (rhs F tuple)).flatMap (MachineOutcomeRows.payload B C values)

noncomputable def emitted (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  MachineAddressEdge.appended (Slots k s d noiseCount) (loaded F tuple base)
    (tupleBits rows B C values F tuple)

noncomputable def finalTapes (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  AddressTupleCleanup.cleared k s d noiseCount (emitted rows B C values F tuple base)

structure Ready (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Prop where
  source : base .source = SourceEncoding.inputBits F
  saved : ∀j, base (.savedIndex j) = encodeWord (tuple j).val
  index : base .index = []
  work : base .work = []
  scratch : base .scratch = []
  copy : base .copyScratch = []
  fields : ∀j slot, base (.field j slot) = []

noncomputable def budget (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Nat :=
  (k * (10 * (SourceEncoding.inputBits F).length + 20) + 1) + 1 +
    ((MachineOutcomeRows.rowCosts (Slots k s d noiseCount) B C values
      (MachineOutcomeRows.selected rows (rhs F tuple)) (loaded F tuple base)).sum + 1) +
    AddressTupleCleanup.budget k s d noiseCount (emitted rows B C values F tuple base) + 1

noncomputable def run (rows : Rows k) (labels : Label k s d noiseCount rows → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction rows labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (oldRhs : Fin k → Bool) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (valid : MachineOutcomeRows.Invariant (Slots k s d noiseCount) B C values
      (MachineOutcomeRows.selected rows (rhs F tuple)) (loaded F tuple base)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main rows)), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, finalTapes rows B C values F tuple base⟩)
      (budget rows B C values F tuple base) := by
  have sourceRun := MachineSourceTuple.placedLoadUnaryInTime
    (sourceLabels labels) (some (rhsLabel labels)) P (fun l => atLabels (.inl l))
    F tuple base ready.source ready.saved ready.index ready.work ready.scratch ready.copy (oldRhs, ())
  have rhsRun := MachineRhsLoad.loadInTime (rhsField k s d noiseCount)
    (rhsLabel labels) (some (rowLabels labels (.inl ()))) P (atLabels (.inr (.inl ())))
    (((oldRhs, ()), ()), none) (loaded F tuple base) (rhs F tuple) (fun _ => [])
    (by
      intro j
      change loaded F tuple base (MachineSourceTuple.rhsField j) = _
      rw [loaded, MachineSourceTuple.output_rhs]
      change encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++
        base (.field j 3) = _
      rw [ready.fields j 3]
      rfl)
  have rowsRun := MachineOutcomeRows.phaseInTime (Slots k s d noiseCount) rows
    (rowLabels labels)
    (AddressTupleCleanup.entry k s d noiseCount (cleanupLabels labels) (some (resetLabel labels)))
    P (fun l => atLabels (.inr (.inr (.inl l))))
    (loaded F tuple base) (rhs F tuple) () none B C values valid
  have cleanupRun := AddressTupleCleanup.execution k s d noiseCount
    (cleanupLabels labels) (some (resetLabel labels)) P
    (fun l => atLabels (.inr (.inr (.inr (.inl l)))))
    (emitted rows B C values F tuple base) (((rhs F tuple), ()), ()) none
  simp only [MachineDrainMany.finalRegister_none] at cleanupRun
  have resetRun : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (resetLabel labels), ((((rhs F tuple), ()), ()), none),
        finalTapes rows B C values F tuple base⟩
      (some ⟨exit, initialState k, finalTapes rows B C values F tuple base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step P ⟨some (resetLabel labels), _, _⟩ = _
    change some (TM2.stepAux (P (resetLabel labels)) _ _) = _
    rw [show P (resetLabel labels) = reset exit from atLabels (.inr (.inr (.inr (.inr ()))))]
    cases exit <;> rfl
  have first := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ sourceRun rhsRun
  have second := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ first rowsRun
  have third := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ second cleanupRun
  have last := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ third resetRun
  refine { steps := last.steps, evals_in_steps := last.evals_in_steps, steps_le_m := ?_ }
  exact last.steps_le_m.trans (by dsimp only [budget]; omega)

def source (F : SourceEncoding.Input) : ActualSource.Source :=
  ActualSource.Source.ofList F.equations F.nonempty

theorem rhs_eq_actual (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) :
    rhs F tuple = AddressOutcomeSpecs.rhsBits (source F) tuple := rfl

theorem canonicalValues_eq_actual (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) :
    AddressTupleLoaded.canonicalValues F tuple =
      CanonicalBodyTemplate.sourceFields tuple (ActualGame.names (source F)) := by
  funext j
  apply congrArg (fun names => CanonicalBodyTemplate.recordFields names (tuple j).val)
  funext slot
  fin_cases slot <;> rfl

theorem tupleBits_actual (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (T : NoiseTables.Table s d) :
    tupleBits (AddressOutcomeSpecs.rows k T)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple =
      AddressOutcomeSpecs.tupleBits (source F) k T tuple := by
  unfold tupleBits
  rw [rhs_eq_actual, canonicalValues_eq_actual]
  exact AddressOutcomeSpecs.tuplePayload_actual (source F) k T tuple

theorem actualInvariant (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (T : NoiseTables.Table s d) (base : Arena k s d noiseCount → List Bool)
    (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) (B C : Nat)
    (hB : base (headerTape k s d noiseCount .baseValue) = encodeWord B)
    (hC : base (headerTape k s d noiseCount .capacity) = encodeWord C) :
    MachineOutcomeRows.Invariant (Slots k s d noiseCount) B C
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
      (loaded F tuple base) := by
  constructor
  · exact AddressTupleLoaded.loaded_clean F tuple base clean
  · exact AddressTupleLoaded.loaded_radix F tuple base B hB
  · exact AddressTupleLoaded.loaded_capacity F tuple base C hC
  · intro spec member
    have fields := AddressTupleLoaded.loaded_savedFields F tuple base ready.saved ready.fields
    change (fun i => loaded F tuple base (MachineAddressEdge.addressSlots
      (Slots k s d noiseCount) (.field i))) = _ at fields
    rw [fields]
    exact AddressOutcomeSpecs.correct_rows T (AddressTupleLoaded.canonicalValues F tuple)
      (rhs F tuple) spec member

noncomputable def run_fixed_rows (T : NoiseTables.Table s d)
    (labels : Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool) (B C : Nat)
    (hB : base (headerTape k s d noiseCount .baseValue) = encodeWord B)
    (hC : base (headerTape k s d noiseCount .capacity) = encodeWord C) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k,
        finalTapes (AddressOutcomeSpecs.rows k T) B C
          (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base⟩)
      (budget (AddressOutcomeSpecs.rows k T) B C
        (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base) :=
  run (AddressOutcomeSpecs.rows k T) labels exit P atLabels F tuple base ready oldRhs B C
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
    (actualInvariant F tuple T base ready clean B C hB hC)

theorem finalTapes_eq (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base) :
    finalTapes rows B C values F tuple base = MachineAddressEdge.appended
      (Slots k s d noiseCount) base (tupleBits rows B C values F tuple) :=
  AddressTupleFrame.cleared_appended_loaded F tuple base ready.index ready.work ready.fields _

noncomputable def run_actual (T : NoiseTables.Table s d)
    (labels : Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      (budget (AddressOutcomeSpecs.rows k T)
        (CanonicalAddress.base F.«variables» F.equations.length s d)
        (AddressGame.bodyCapacity (source F) k s d)
        (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base) := by
  have actual := run_fixed_rows T labels exit P atLabels F tuple base ready clean oldRhs
    (CanonicalAddress.base F.«variables» F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d) hB hC
  rw [finalTapes_eq _ _ _ _ F tuple base ready, tupleBits_actual] at actual
  exact actual

theorem saved_of_current (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (currentWords : ∀j, base (current k s d noiseCount j) = encodeWord (digits j).val) :
    ∀j, base (.savedIndex j) = encodeWord (digits j.rev).val := by
  intro j
  simpa only [AddressMachineSpace.current_rev] using currentWords j.rev

end DFVSGames.Integration.AddressTupleBody
end

section

namespace DFVSGames.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration
open MachineComposition

noncomputable section

abbrev Tape (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :=
  AddressMachineSpace.Tape k s d T.vectors.length
abbrev State (k : Nat) := AddressMachineSpace.State k

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

def accumulator : Tape k T := AddressMachineSpace.headerTape k s d T.vectors.length .reversed
def output : Tape k T := AddressMachineSpace.finalOutput k s d T.vectors.length

theorem accumulator_ne_output : accumulator k T ≠ output k T :=
  AddressMachineSpace.headerTape_ne_finalOutput k s d T.vectors.length .reversed

def clearKeys : List (Tape k T) := by
  classical
  exact ((Finset.univ : Finset (Tape k T)).filter
    (fun tape : Tape k T => tape ≠ accumulator k T ∧ tape ≠ output k T)).toList

@[simp] theorem mem_clearKeys (tape : Tape k T) :
    tape ∈ clearKeys k T ↔ tape ≠ accumulator k T ∧ tape ≠ output k T := by
  classical
  simp [clearKeys]

@[simp] theorem accumulator_not_mem_clearKeys : accumulator k T ∉ clearKeys k T := by simp
@[simp] theorem output_not_mem_clearKeys : output k T ∉ clearKeys k T := by simp

theorem clearKeys_covers (tape : Tape k T) (ha : tape ≠ accumulator k T)
    (ho : tape ≠ output k T) : tape ∈ clearKeys k T := (mem_clearKeys k T tape).2 ⟨ha,ho⟩

theorem clearKeys_nodup : (clearKeys k T).Nodup := by
  unfold clearKeys
  exact Finset.nodup_toList _

abbrev HeaderLabel := MachineAddressHeaders.Label k s d T.vectors.length
abbrev BodyLabel := Integration.AddressTupleBody.Label k s d T.vectors.length
  (AddressOutcomeSpecs.rows k T)
abbrev FinishLabel := SourceRuntimeFinish.Label (clearKeys k T)

inductive Label (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
  | header (localLabel : HeaderLabel k T)
  | initialize (localLabel : MachineOdometerInit.Label k)
  | body (localLabel : BodyLabel k T)
  | check (digit : Fin k)
  | reset (digit : Fin k)
  | finishStart
  | finish (localLabel : FinishLabel k T)
  deriving DecidableEq, Fintype

def headerLabels : HeaderLabel k T → Label k T := Label.header
def initializeLabels : MachineOdometerInit.Label k → Label k T := Label.initialize
def bodyLabels : BodyLabel k T → Label k T := Label.body
def finishLabels : FinishLabel k T → Label k T := Label.finish

def start : Label k T := .header (.inl .copyOut)
def initializeStart : Label k T := MachineOdometerInit.labelAt (initializeLabels k T) 0
def bodyStart : Label k T := .body (Integration.AddressTupleBody.main (AddressOutcomeSpecs.rows k T))
def checkLabel (j : Fin k) : Label k T := .check j
def resetLabel (j : Fin k) : Label k T := .reset j
def finishStart : Label k T := .finishStart

def next (r : Nat) : Label k T :=
  if h : r < k then checkLabel k T ⟨r,h⟩ else finishStart k T

def resetAt (r : Nat) : Label k T :=
  if h : r < k then resetLabel k T ⟨r,h⟩ else finishStart k T

@[simp] theorem next_lt (r : Nat) (h : r < k) :
    next k T r = checkLabel k T ⟨r,h⟩ := by simp [next,h]
@[simp] theorem next_ge (r : Nat) (h : k ≤ r) : next k T r = finishStart k T := by
  simp [next, Nat.not_lt.mpr h]
@[simp] theorem resetAt_lt (r : Nat) (h : r < k) :
    resetAt k T r = resetLabel k T ⟨r,h⟩ := by simp [resetAt,h]

def program : Label k T → TM2.Stmt (fun _ : Tape k T => Bool) (Label k T) (State k)
  | .header l => MachineAddressHeaders.statement
      (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (headerLabels k T) (some (initializeStart k T)) l
  | .initialize l => MachineOdometerInit.statement
      (AddressMachineSpace.odometerSlots k s d T.vectors.length)
      (initializeLabels k T) (some (bodyStart k T)) l
  | .body l => Integration.AddressTupleBody.instruction (AddressOutcomeSpecs.rows k T)
      (bodyLabels k T) (some (next k T 0)) l
  | .check j => MachineTupleOdometer.increment
      (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (bodyStart k T) (resetLabel k T j)
  | .reset j => MachineTupleOdometer.reset
      (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (resetLabel k T j) (next k T (j.val+1))
  | .finishStart => MachineFieldTemplate.jump
      (SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T))
  | .finish l => SourceRuntimeFinish.statement (clearKeys k T) (accumulator k T) (output k T)
      (AddressMachineSpace.initialState k).1 (finishLabels k T) none l

@[simp] theorem atHeader (l : HeaderLabel k T) : program k T (headerLabels k T l) =
    MachineAddressHeaders.statement (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (headerLabels k T) (some (initializeStart k T)) l := rfl

@[simp] theorem atInitialize (l : MachineOdometerInit.Label k) :
    program k T (initializeLabels k T l) =
      MachineOdometerInit.statement (AddressMachineSpace.odometerSlots k s d T.vectors.length)
        (initializeLabels k T) (some (bodyStart k T)) l := rfl

@[simp] theorem atBody (l : BodyLabel k T) : program k T (bodyLabels k T l) =
    Integration.AddressTupleBody.instruction (AddressOutcomeSpecs.rows k T)
      (bodyLabels k T) (some (next k T 0)) l := rfl

@[simp] theorem atCheck (j : Fin k) : program k T (checkLabel k T j) =
    MachineTupleOdometer.increment (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (bodyStart k T) (resetLabel k T j) := rfl

@[simp] theorem atReset (j : Fin k) : program k T (resetLabel k T j) =
    MachineTupleOdometer.reset (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (resetLabel k T j) (next k T (j.val+1)) := rfl

@[simp] theorem atFinish (l : FinishLabel k T) : program k T (finishLabels k T l) =
    SourceRuntimeFinish.statement (clearKeys k T) (accumulator k T) (output k T)
      (AddressMachineSpace.initialState k).1 (finishLabels k T) none l := rfl

theorem finishStartStep (state : State k) (base : Tape k T → List Bool) :
    TM2.step (program k T) ⟨some (finishStart k T),state,base⟩ =
      some ⟨SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T),state,base⟩ := by
  change some (TM2.stepAux (MachineFieldTemplate.jump
    (SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T))) state base) = _
  cases SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T) <;> rfl

def finishStartInTime (state : State k) (base : Tape k T → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program k T))
      ⟨some (finishStart k T),state,base⟩
      (some ⟨SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T),state,base⟩) 1 where
  steps := 1
  evals_in_steps := finishStartStep k T state base
  steps_le_m := Nat.le_refl _

def machine : FinTM2 where
  K := Tape k T
  k₀ := .source
  k₁ := output k T
  Γ := fun _ => Bool
  Λ := Label k T
  main := start k T
  σ := State k
  initialState := AddressMachineSpace.initialState k
  m := program k T

@[simp] theorem machine_main : (machine k T).main = start k T := rfl
@[simp] theorem machine_program : (machine k T).m = program k T := rfl
@[simp] theorem machine_initialState : (machine k T).initialState = AddressMachineSpace.initialState k := rfl
@[simp] theorem machine_input : (machine k T).k₀ = (MachineSourceTuple.Tape.source : Tape k T) := rfl
@[simp] theorem machine_output : (machine k T).k₁ = output k T := rfl

def inputAlphabet : (machine k T).Γ (machine k T).k₀ ≃ Bool := Equiv.refl Bool
def outputAlphabet : (machine k T).Γ (machine k T).k₁ ≃ Bool := Equiv.refl Bool

def inputTapes (bits : List Bool) : Tape k T → List Bool :=
  Function.update (fun _ => []) .source bits

def outputTapes (bits : List Bool) : Tape k T → List Bool :=
  SourceRuntimeFinish.canonicalTapes (output k T) bits

@[simp] theorem inputTapes_source (bits : List Bool) : inputTapes k T bits .source = bits := by
  simp [inputTapes]

@[simp] theorem inputTapes_other (bits : List Bool) (tape : Tape k T) (h : tape ≠ .source) :
    inputTapes k T bits tape = [] := by simp [inputTapes,h]

@[simp] theorem outputTapes_output (bits : List Bool) : outputTapes k T bits (output k T) = bits := by
  simp [outputTapes, SourceRuntimeFinish.canonicalTapes]

@[simp] theorem outputTapes_other (bits : List Bool) (tape : Tape k T) (h : tape ≠ output k T) :
    outputTapes k T bits tape = [] := by simp [outputTapes,SourceRuntimeFinish.canonicalTapes,h]

theorem initList_eq (bits : List Bool) : initList (machine k T) bits =
    ⟨some (start k T),AddressMachineSpace.initialState k,inputTapes k T bits⟩ := by
  change (⟨some (start k T),AddressMachineSpace.initialState k,
    (initList (machine k T) bits).stk⟩ : (machine k T).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨some (start k T),AddressMachineSpace.initialState k,tapes⟩ : (machine k T).Cfg))
  dsimp only [machine]
  funext tape
  by_cases h : tape = .source
  · subst tape; simp [initList,inputTapes]
  · simp [initList,inputTapes,h]

theorem haltList_eq (bits : List Bool) : haltList (machine k T) bits =
    ⟨none,AddressMachineSpace.initialState k,outputTapes k T bits⟩ := by
  change (⟨none,AddressMachineSpace.initialState k,
    (haltList (machine k T) bits).stk⟩ : (machine k T).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨none,AddressMachineSpace.initialState k,tapes⟩ : (machine k T).Cfg))
  dsimp only [machine]
  funext tape
  by_cases h : tape = output k T
  · subst tape; simp [haltList,outputTapes,SourceRuntimeFinish.canonicalTapes]
  · simp [haltList,outputTapes,SourceRuntimeFinish.canonicalTapes,h]

end
end DFVSGames.Reduction.AddressMachineProgram
end

section

namespace DFVSGames.Reduction.AddressOdometerSchedule

open Turing
open DFVSGames.Foundations.Complexity MachineTupleOdometer
open DFVSGames.Foundations.Hastad
open MachineTransfer

noncomputable section

abbrev Tape := AddressMachineSpace.Tape

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def current (k s d noiseCount : Nat) (i : Fin k) : Tape k s d noiseCount :=
  AddressMachineSpace.current k s d noiseCount i

def remaining (k s d noiseCount : Nat) (i : Fin k) : Tape k s d noiseCount :=
  AddressMachineSpace.remaining k s d noiseCount i

def accumulator (k s d noiseCount : Nat) : Tape k s d noiseCount :=
  AddressMachineSpace.headerTape k s d noiseCount .reversed

def currentAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then current k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

def remainingAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then remaining k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

@[simp] theorem current_eq_iff (i j : Fin k) :
    current k s d noiseCount i = current k s d noiseCount j ↔ i = j := by
  simp [current, AddressMachineSpace.current]
@[simp] theorem remaining_eq_iff (i j : Fin k) :
    remaining k s d noiseCount i = remaining k s d noiseCount j ↔ i = j := by
  simp [remaining, AddressMachineSpace.remaining]
@[simp] theorem current_ne_remaining (i j : Fin k) :
    current k s d noiseCount i ≠ remaining k s d noiseCount j :=
  AddressMachineSpace.current_ne_remaining k s d noiseCount i j
@[simp] theorem remaining_ne_current (i j : Fin k) :
    remaining k s d noiseCount i ≠ current k s d noiseCount j :=
  Ne.symm (current_ne_remaining j i)
@[simp] theorem accumulator_ne_current (i : Fin k) :
    accumulator k s d noiseCount ≠ current k s d noiseCount i :=
  AddressMachineSpace.headerTape_ne_current k s d noiseCount .reversed i
@[simp] theorem accumulator_ne_remaining (i : Fin k) :
    accumulator k s d noiseCount ≠ remaining k s d noiseCount i :=
  AddressMachineSpace.headerTape_ne_remaining k s d noiseCount .reversed i
@[simp] theorem current_ne_accumulator (i : Fin k) :
    current k s d noiseCount i ≠ accumulator k s d noiseCount := Ne.symm (accumulator_ne_current i)
@[simp] theorem remaining_ne_accumulator (i : Fin k) :
    remaining k s d noiseCount i ≠ accumulator k s d noiseCount := Ne.symm (accumulator_ne_remaining i)

def setDigits (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape k s d noiseCount → List Bool) : Tape k s d noiseCount → List Bool
  | .savedIndex i => if h : i.rev.val < q then encodeWord (digits ⟨i.rev.val, h⟩)
      else base (.savedIndex i)
  | .extra (.inr (.inr (.inl i))) => if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (.extra (.inr (.inr (.inl i))))
  | tape => base tape

def setAcc (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    Tape k s d noiseCount → List Bool := Function.update base (accumulator k s d noiseCount) bits

def putDigit (i : Fin k) (base : Tape k s d noiseCount → List Bool) (a r : Nat) :
    Tape k s d noiseCount → List Bool :=
  digitTapes (current k s d noiseCount i) (remaining k s d noiseCount i) base a r [] []

@[simp] theorem setDigits_current (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (i : Fin k) :
    setDigits m digits base (current k s d noiseCount i) =
      if h : i.val < q then encodeWord (digits ⟨i.val, h⟩) else base (current k s d noiseCount i) := by
  simp [setDigits, current, AddressMachineSpace.current]
@[simp] theorem setDigits_remaining (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (i : Fin k) :
    setDigits m digits base (remaining k s d noiseCount i) =
      if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (remaining k s d noiseCount i) := rfl

theorem setDigits_other (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (tape : Tape k s d noiseCount)
    (hc : ∀ i, tape ≠ current k s d noiseCount i)
    (hr : ∀ i, tape ≠ remaining k s d noiseCount i) : setDigits m digits base tape = base tape := by
  cases tape with
  | savedIndex i => exact (hc i.rev (by simp [current, AddressMachineSpace.current])).elim
  | extra e =>
    rcases e with a | a
    · rfl
    · rcases a with a | a
      · rfl
      · rcases a with i | unused
        · exact (hr i rfl).elim
        · rfl
  | _ => rfl

private theorem digitCases_inline_AddressOdometerSchedule {P : Tape k s d noiseCount → Prop} (tape : Tape k s d noiseCount)
    (hc : ∀ i, P (current k s d noiseCount i))
    (hr : ∀ i, P (remaining k s d noiseCount i))
    (other : ∀ tape, (∀ i, tape ≠ current k s d noiseCount i) →
      (∀ i, tape ≠ remaining k s d noiseCount i) → P tape) : P tape := by
  classical
  by_cases h : ∃ i, tape = current k s d noiseCount i
  · obtain ⟨i, rfl⟩ := h; exact hc i
  · by_cases h' : ∃ i, tape = remaining k s d noiseCount i
    · obtain ⟨i, rfl⟩ := h'; exact hr i
    · exact other tape (fun i hi => h ⟨i, hi⟩) (fun i hi => h' ⟨i, hi⟩)

@[simp] theorem setDigits_zero (m : Nat) (digits : Fin 0 → Nat)
    (base : Tape k s d noiseCount → List Bool) : setDigits m digits base = base := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp
  · intro i; simp
  · intro tape hc hr; exact setDigits_other m digits base tape hc hr

@[simp] theorem setDigits_accumulator (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) :
    setDigits m digits base (accumulator k s d noiseCount) = base (accumulator k s d noiseCount) := rfl

@[simp] theorem setAcc_self (base : Tape k s d noiseCount → List Bool) :
    setAcc base (base (accumulator k s d noiseCount)) = base := by simp [setAcc]
@[simp] theorem setAcc_setAcc (base : Tape k s d noiseCount → List Bool) (first second : List Bool) :
    setAcc (setAcc base first) second = setAcc base second := by simp [setAcc]
@[simp] theorem setAcc_apply (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    setAcc base bits (accumulator k s d noiseCount) = bits := by simp [setAcc]

theorem setDigits_setAcc (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc base bits) = setAcc (setDigits m digits base) bits := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [setDigits_other m digits _ tape hc hr, setAcc, ha]

@[simp] theorem putDigit_current (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (i : Fin k) :
    putDigit j base a r (current k s d noiseCount i) =
      if i = j then encodeWord a else base (current k s d noiseCount i) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Function.update_apply]
@[simp] theorem putDigit_remaining (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (i : Fin k) :
    putDigit j base a r (remaining k s d noiseCount i) =
      if i = j then encodeWord r else base (remaining k s d noiseCount i) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Function.update_apply]

theorem putDigit_other (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (tape : Tape k s d noiseCount)
    (hc : tape ≠ current k s d noiseCount j) (hr : tape ≠ remaining k s d noiseCount j) :
    putDigit j base a r tape = base tape := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hc, hr]

@[simp] theorem putDigit_accumulator (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) : putDigit j base a r (accumulator k s d noiseCount) =
      base (accumulator k s d noiseCount) := by
  apply putDigit_other <;> simp

theorem putDigit_setAcc (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (bits : List Bool) :
    putDigit j (setAcc base bits) a r = setAcc (putDigit j base a r) bits := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [putDigit_other j _ a r tape (hc j) (hr j), setAcc, ha]

theorem setDigits_putDigit (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (a r : Nat) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a r := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro tape hc hr
    simp [setDigits_other m digits _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m (Fin.snoc digits a) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a (m - 1 - a) := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro tape hc hr
    simp [setDigits_other m _ _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc_base (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a (m - 1 - a)) =
      setDigits m (Fin.snoc digits a) base := by
  rw [setDigits_putDigit, setDigits_snoc]

@[simp] theorem setDigits_savedIndex (m : Nat) (digits : Fin k → Nat)
    (base : Tape k s d noiseCount → List Bool) (j : Fin k) :
    setDigits m digits base (.savedIndex j) = encodeWord (digits j.rev) := by
  have h : j.rev.val < k := j.rev.isLt
  simp only [setDigits, h, dite_eq_left]

@[simp] theorem setAcc_other (base : Tape k s d noiseCount → List Bool)
    (bits : List Bool) (tape : Tape k s d noiseCount)
    (h : tape ≠ accumulator k s d noiseCount) : setAcc base bits tape = base tape := by
  simp [setAcc, h]

def allBits {q : ℕ} (bits : (Fin q → Fin m) → List Bool) : List Bool :=
  (tupleOrder m q).flatMap bits

def blockPrefix (blocks : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => blockPrefix blocks n ++ blocks n

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

def blocks {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) (d : ℕ) : List Bool :=
  if h : d < m then allBits (fun c => bits (Fin.snoc c ⟨d, h⟩)) else []

theorem blockPrefix_all {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) :
    blockPrefix (blocks bits) m = allBits bits := by
  rw [blockPrefix_eq_ofFn]
  simp only [blocks, Fin.isLt, ↓reduceDIte, allBits, tupleOrder_snoc]
  simp only [List.flatMap_assoc, List.flatMap_map]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]

def configuration (label : Λ) (canonical : σ) (tapes : Tape k s d noiseCount → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ := ⟨some label, (canonical, none), tapes⟩

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ)
    {q : ℕ} (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc base ((bits c).reverse ++ output))))

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (digit : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c digit i).val) =
      Fin.snoc (fun i => (c i).val) digit.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) : Configuration (Tape k s d noiseCount) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc base ((allBits bits).reverse ++ base (accumulator k s d noiseCount))))

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ k)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (accumulator k s d noiseCount))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt k s d noiseCount)
      (remaining := remainingAt k s d noiseCount) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical base bits) count rfl rfl hrun
    refine ⟨tree, ?_⟩
    unfold NestedCycle.LeafBound
    exact hcount
  | succ q ih =>
    have hqu : q < k := by omega
    let schedule : CycleSchedule (Tape k s d noiseCount) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (accumulator k s d noiseCount))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
            (checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.register schedule.base), tree.LeafBound B := by
      let digit : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c digit)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (accumulator k s d noiseCount)))
        digit.val (m - 1 - digit.val)
      have hrem : m - 1 - digit.val = r.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = digit.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = digit.val + 1 := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, digit.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c digit) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical childBase childBits =
          checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
            schedule.ambient schedule.register schedule.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_accumulator, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) schedule children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, schedule,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        finalConfiguration (next (q + 1)) canonical base bits := by
      simp only [cycleExit, finalConfiguration, configuration, schedule, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
        (cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B : ℕ) (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin k → Fin m) → List Bool)
    (atCheck : ∀ i, i < k → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < k → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) k bodyLabel canonical base)
      (some (finalConfiguration (next k) canonical base bits))
      ((B + 2 * k) * m ^ k)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical
    positive B k (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

@[simp] theorem initial_current (base : Tape k s d noiseCount → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin k) :
    (initialConfiguration (m := m) k bodyLabel canonical base).stk (current k s d noiseCount i) =
      encodeWord 0 := by simp [initialConfiguration, configuration]

@[simp] theorem initial_remaining (base : Tape k s d noiseCount → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin k) :
    (initialConfiguration (m := m) k bodyLabel canonical base).stk (remaining k s d noiseCount i) =
      encodeWord (m - 1) := by simp [initialConfiguration, configuration]

@[simp] theorem final_current (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) (i : Fin k) :
    (finalConfiguration exitLabel canonical base bits).stk (current k s d noiseCount i) =
      encodeWord 0 := by simp [finalConfiguration, configuration]

@[simp] theorem final_remaining (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) (i : Fin k) :
    (finalConfiguration exitLabel canonical base bits).stk (remaining k s d noiseCount i) =
      encodeWord (m - 1) := by simp [finalConfiguration, configuration]

@[simp] theorem final_accumulator (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical base bits).stk (accumulator k s d noiseCount) =
      ((tupleOrder m k).flatMap bits).reverse ++ base (accumulator k s d noiseCount) := by
  simp [finalConfiguration, configuration, allBits]

theorem final_other (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ) (bits : (Fin k → Fin m) → List Bool)
    (tape : Tape k s d noiseCount)
    (hc : ∀ i, tape ≠ current k s d noiseCount i)
    (hr : ∀ i, tape ≠ remaining k s d noiseCount i)
    (ha : tape ≠ accumulator k s d noiseCount) :
    (finalConfiguration exitLabel canonical base bits).stk tape = base tape := by
  simp only [finalConfiguration, configuration, setDigits_other m _ _ tape hc hr,
    setAcc_other _ _ tape ha]

end
end DFVSGames.Reduction.AddressOdometerSchedule
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
