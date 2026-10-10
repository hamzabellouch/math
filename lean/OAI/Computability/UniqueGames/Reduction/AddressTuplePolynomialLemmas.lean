import OAI.Computability.UniqueGames.Machines.MachineTupleOdometer
import OAI.Computability.UniqueGames.PCP.SourceLoopInitLemmas
import OAI.Computability.UniqueGames.PCP.SourceRuntimeSpace
import OAI.Computability.UniqueGames.Reduction.AddressMachineSpace
import OAI.Computability.UniqueGames.Reduction.AddressTupleBody
import OAI.Computability.UniqueGames.Reduction.AddressTupleBudget

namespace OAI


namespace UniqueGamesTheorem.Integration.AddressTuplePolynomial

open Turing Reduction Foundations.Complexity
open AddressTupleBody AddressMachineSpace


variable {k s d noiseCount : Nat} {Λ : Type}

noncomputable def run_actual (T : NoiseTables.Table s d)
    (labels : AddressTupleBody.Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : AddressTupleBody.Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀ l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : AddressTupleBody.Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.variables F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have actual := AddressTupleBody.run_actual T labels exit P atLabels F tuple base
    ready clean oldRhs hB hC
  exact {
    steps := actual.steps
    evals_in_steps := actual.evals_in_steps
    steps_le_m := actual.steps_le_m.trans
      (AddressTupleBudget.budget_le_timePolynomial F tuple T base ready clean)
  }

/-- The explicit iterated transition trace and its uniform bound, for callers
that compose traces directly instead of runtime-witness structures. -/
theorem trace_actual (T : NoiseTables.Table s d)
    (labels : AddressTupleBody.Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : AddressTupleBody.Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀ l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : AddressTupleBody.Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.variables F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    ∃ steps ≤ (AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length,
      (MachineComposition.advance (TM2.step P))^[steps]
        (some ⟨some (labels (main (AddressOutcomeSpecs.rows k T))),
          (((oldRhs, ()), ()), none), base⟩) =
        some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
          base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩ := by
  have actual := run_actual T labels exit P atLabels F tuple base ready clean oldRhs hB hC
  exact ⟨actual.steps, actual.steps_le_m, actual.evals_in_steps⟩

end UniqueGamesTheorem.Integration.AddressTuplePolynomial



namespace UniqueGamesTheorem.Reduction.AddressMachineProgram

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

/-- The finalizer visits every other tape in a fixed finite order. -/
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

/-- Header, digit initialization, physical tuple body, carry loops, and complete
finalization are placed in a single actual finite transition program. -/
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

/-- This bridge has no data-dependent action and costs exactly one transition. -/
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

/-- All alphabets and registers are finite. Counts live solely on Bool stacks. -/
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

/-- Identity alphabet encodings at both ends of the concrete machine. -/
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
  funext tape
  by_cases h : tape = .source
  · subst tape; simp [initList,machine,inputTapes]; rfl
  · simp [initList,machine,inputTapes]
    erw [dite_eq_right h, Function.update_of_ne h]

theorem haltList_eq (bits : List Bool) : haltList (machine k T) bits =
    ⟨none,AddressMachineSpace.initialState k,outputTapes k T bits⟩ := by
  change (⟨none,AddressMachineSpace.initialState k,
    (haltList (machine k T) bits).stk⟩ : (machine k T).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨none,AddressMachineSpace.initialState k,tapes⟩ : (machine k T).Cfg))
  funext tape
  by_cases h : tape = output k T
  · subst tape; simp [haltList,machine,outputTapes,SourceRuntimeFinish.canonicalTapes]; rfl
  · simp [haltList,machine,outputTapes,SourceRuntimeFinish.canonicalTapes]
    erw [dite_eq_right h, Function.update_of_ne h]

end
end UniqueGamesTheorem.Reduction.AddressMachineProgram



/-!
The actual address machine's final bridge, cleanup, reversal, and halt. The
polynomial cleanup bound follows from space used by the supplied actual prefix
execution. The complete reduction supplies that prefix in `MachineAddressGame`.
-/

namespace UniqueGamesTheorem.Reduction.AddressMachineFinish

open Turing Foundations.Complexity Foundations.Hastad


noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def timePolynomial (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (AddressMachineProgram.machine k T)
    (AddressMachineProgram.clearKeys k T).length (prefixTime + 1)

/-- Finish the concrete program, including its one-step finalizer entry bridge.
The runtime bound uses all actual intermediate tapes, with no output-size or
private-space assumption. -/
def completePrefix (input : List Bool) (prefixTime : Polynomial Nat)
    (base : AddressMachineProgram.Tape k T → List Bool)
    (execution : StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) input)
      (some ⟨some (AddressMachineProgram.finishStart k T),
        AddressMachineSpace.initialState k, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base (AddressMachineProgram.output k T) = []) :
    TM2OutputsInTime (AddressMachineProgram.machine k T) input
      (some (base (AddressMachineProgram.accumulator k T)).reverse)
      ((timePolynomial k T prefixTime).eval input.length) := by
  let bridge := AddressMachineProgram.finishStartInTime k T
    (AddressMachineSpace.initialState k) base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) input)
      (some ⟨SourceRuntimeFinish.entry (AddressMachineProgram.clearKeys k T)
          (AddressMachineProgram.finishLabels k T), AddressMachineSpace.initialState k, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using
        joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime
    (AddressMachineProgram.clearKeys k T)
    (AddressMachineProgram.accumulator k T) (AddressMachineProgram.output k T)
    (AddressMachineProgram.accumulator_ne_output k T)
    (AddressMachineProgram.accumulator_not_mem_clearKeys k T)
    (AddressMachineProgram.output_not_mem_clearKeys k T)
    (AddressMachineProgram.clearKeys_covers k T)
    (AddressMachineSpace.initialState k).1 (AddressMachineProgram.finishLabels k T) none
    (AddressMachineProgram.program k T) (AddressMachineProgram.atFinish k T)
    base outputEmpty (AddressMachineSpace.initialState k).1 none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (AddressMachineProgram.machine k T)
    input (prefixTime + 1) prefixRun
    (AddressMachineProgram.clearKeys k T)
    (AddressMachineProgram.accumulator k T) (AddressMachineProgram.output k T)
    (AddressMachineProgram.accumulator_not_mem_clearKeys k T)
    (AddressMachineProgram.output_not_mem_clearKeys k T)
    (AddressMachineProgram.clearKeys_covers k T) base outputEmpty (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
    (initList (AddressMachineProgram.machine k T) input)
    (some (haltList (AddressMachineProgram.machine k T)
      (base (AddressMachineProgram.accumulator k T)).reverse)) _
  rw [AddressMachineProgram.haltList_eq]
  exact run

end
end UniqueGamesTheorem.Reduction.AddressMachineFinish

end OAI
