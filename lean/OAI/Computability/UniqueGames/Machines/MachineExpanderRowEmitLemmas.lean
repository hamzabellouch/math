import OAI.Computability.UniqueGames.Machines.FinalCNFLoopLemmas

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

section

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

/-- One scaled scan/restore, one bounded offset, the delimiter, and final jump. -/
def emitSteps (n : Nat) : Nat := 3 * (n + 1) + 6

theorem affinePlan_bits {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) (ambient : σ) :
    Emitter.prefixBits (affinePlan coefficient offset) (fun _ : Fin 1 => n) ambient 3 =
      encodeWord (coefficient * n + (offset ambient).val) := by
  change Emitter.prefixBits
    (Emitter.listCommands (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset))
    (fun _ : Fin 1 => n) ambient
    (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset).length = _
  rw [Emitter.bits_listCommands, Emitter.affineCommands_bits]
  simp [Emitter.affineValue]

theorem affinePlan_steps {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) :
    Emitter.prefixSteps (affinePlan coefficient offset) (fun _ : Fin 1 => n) 3 + 1 =
      emitSteps n := by
  simp [affinePlan, Emitter.prefixSteps, Emitter.commandAt, Emitter.listCommands,
    Emitter.affineCommands, Emitter.commandSteps, emitSteps]

/-- Every tape except the accumulator is literally retained. -/
def emittedWord {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) : K → List Bool :=
  Function.update base target ((encodeWord value).reverse ++ base target)

@[simp] theorem emittedWord_target {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) :
    emittedWord target base value target = (encodeWord value).reverse ++ base target := by
  simp [emittedWord]

theorem emittedWord_other {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat)
    (tape : K) (different : tape ≠ target) :
    emittedWord target base value tape = base tape := by
  simp [emittedWord, different]

variable {ρ : Type} [Fintype ρ] {d : Nat}

@[simp] theorem program_firstEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.firstEmit label) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => Tape.inputVertex)
        .emitScratch .queryReverse Label.firstEmit (some Label.firstReverse) label := rfl

@[simp] theorem program_secondEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.secondEmit label) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => Tape.quotientFirst)
        .emitScratch .queryReverse Label.secondEmit (some Label.secondReverse) label := rfl

@[simp] theorem program_outputEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (rowFactor d)) :
    program (ρ := ρ) positive H (.outputEmit label) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => Tape.quotientSecond)
        .emitScratch .output Label.outputEmit (some (Label.cleanup 0)) label := rfl

section Embedded

variable {K Λ : Type} [DecidableEq K]

/-- The code premise identifies concrete statements in a caller's program;
it does not assume any phase execution. -/
theorem firstEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.firstEmit l)) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
        (some (labels .firstReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.firstEmit k)) (some (labels .firstReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [firstPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, firstAddress] using run

theorem secondEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.secondEmit l)) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
        (some (labels .secondReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.secondEmit k)) (some (labels .secondReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [secondPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, secondAddress] using run

theorem outputEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.outputEmit l)) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
        (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
        (some (labels (.cleanup 0))) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
    (ports .emitScratch) (ports .output)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.outputEmit k)) (some (labels (.cleanup 0))) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [outputPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, outputAddress] using run

def firstEmitInTimeAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))), ((ambient, ()), none), base⟩
      (some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := firstEmitTraceAt positive H ports portsInjective labels exit target atLabels
    n base source scratch ambient
  steps_le_m := Nat.le_refl _

def secondEmitInTimeAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))), ((ambient, ()), none), base⟩
      (some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := secondEmitTraceAt positive H ports portsInjective labels exit target atLabels
    n base source scratch ambient
  steps_le_m := Nat.le_refl _

def outputEmitInTimeAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))), ((ambient, ()), none), base⟩
      (some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := outputEmitTraceAt positive H ports portsInjective labels exit target atLabels
    n base source scratch ambient
  steps_le_m := Nat.le_refl _

end Embedded

theorem firstEmitTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .inputVertex = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step (program positive H)))^[emitSteps n]
      (some ⟨some (.firstEmit (Emitter.labelAt 3 _ 0 .entry)),
        ((ambient, ()), none), base⟩) =
      some ⟨some .firstReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (firstAddress n ambient.1.2)⟩ := by
  exact firstEmitTraceAt positive H id Function.injective_id id none (program positive H)
    (fun _ => rfl) n base source scratch ambient

theorem secondEmitTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientFirst = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step (program positive H)))^[emitSteps n]
      (some ⟨some (.secondEmit (Emitter.labelAt 3 _ 0 .entry)),
        ((ambient, ()), none), base⟩) =
      some ⟨some .secondReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (secondAddress n ambient.1.2)⟩ := by
  exact secondEmitTraceAt positive H id Function.injective_id id none (program positive H)
    (fun _ => rfl) n base source scratch ambient

theorem outputEmitTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientSecond = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step (program positive H)))^[emitSteps n]
      (some ⟨some (.outputEmit (Emitter.labelAt 3 _ 0 .entry)),
        ((ambient, ()), none), base⟩) =
      some ⟨some (.cleanup 0), ((ambient, ()), none),
        emittedWord .output base (outputAddress n ambient.1.2)⟩ := by
  exact outputEmitTraceAt positive H id Function.injective_id id none (program positive H)
    (fun _ => rfl) n base source scratch ambient

def firstEmitInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .inputVertex = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.firstEmit (Emitter.labelAt 3 _ 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨some .firstReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (firstAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := firstEmitTrace positive H n base source scratch ambient
  steps_le_m := Nat.le_refl _

def secondEmitInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientFirst = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.secondEmit (Emitter.labelAt 3 _ 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨some .secondReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (secondAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := secondEmitTrace positive H n base source scratch ambient
  steps_le_m := Nat.le_refl _

def outputEmitInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientSecond = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.outputEmit (Emitter.labelAt 3 _ 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨some (.cleanup 0), ((ambient, ()), none),
        emittedWord .output base (outputAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := outputEmitTrace positive H n base source scratch ambient
  steps_le_m := Nat.le_refl _

end

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

def lookupPhaseLabel {d : Nat} (second : Bool)
    (l : MachinePreservingLookupClean.Label) : Label d :=
  if second then .secondLookup l else .firstLookup l

def scanPhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondScan else .firstScan

def reversePhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondReverse else .firstReverse

def lookupPhasePort {d : Nat} (second : Bool) (control : Control d) : Fin (degree d) :=
  if second then secondOffset control else firstOffset control

def lookupPhaseAddress {d : Nat} (second : Bool) (vertex : Nat) (control : Control d) : Nat :=
  if second then secondAddress vertex control else firstAddress vertex control

theorem lookupPhaseAddress_eq_rowIndex {v d : Nat} (second : Bool)
    (vertex : Fin v) (control : Control d) :
    lookupPhaseAddress second vertex.val control =
      (rowIndex v (degree d) (vertex, lookupPhasePort second control)).val := by
  cases second
  · exact firstAddress_eq_rowIndex vertex control
  · exact secondAddress_eq_rowIndex vertex control

theorem lookupTape_injective : Function.Injective lookupTape := by decide

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

/-- The exact cleaned tape state produced by either lookup. -/
def lookupResultTapes (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) : K → List Bool :=
  MachinePreservingLookup.initialTapes (ports ∘ lookupTape) base 0 indexSuffix []
    (encodeWord value ++ base (ports .lookupOutput))

theorem lookupResultTapes_index (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .queryIndex) =
      encodeWord 0 ++ indexSuffix := by
  apply MachineLookup.tapes_index
  · exact fun h => (by decide : Tape.queryIndex ≠ .lookupWork) (distinct h)
  · exact fun h => (by decide : Tape.queryIndex ≠ .lookupOutput) (distinct h)

theorem lookupResultTapes_work (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .lookupWork) = [] := by
  apply MachineLookup.tapes_source
  exact fun h => (by decide : Tape.lookupWork ≠ .lookupOutput) (distinct h)

theorem lookupResultTapes_output (ports : Tape → K)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .lookupOutput) =
      encodeWord value ++ base (ports .lookupOutput) := by
  apply MachineLookup.tapes_destination

/-- Every tape outside the query, work, and lookup-output roles is retained. -/
theorem lookupResultTapes_other (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) (p : K)
    (hi : p ≠ ports .queryIndex) (hw : p ≠ ports .lookupWork)
    (ho : p ≠ ports .lookupOutput) :
    lookupResultTapes ports base value indexSuffix p = base p := by
  exact MachineLookup.tapes_other _ _ _ p hi hw ho _ _ _ _

theorem lookupResultTapes_table (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .table) = base (ports .table) := by
  apply lookupResultTapes_other
  all_goals intro h; have := distinct h; cases this

theorem lookupResultTapes_restore (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .lookupRestore) =
      base (ports .lookupRestore) := by
  apply lookupResultTapes_other
  all_goals intro h; have := distinct h; cases this

section Lookup

variable {v d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool) (G : Table v (degree d))
    (tableWord : base (ports .table) = encodeWords (rotationWords G))
    (scratchEmpty : base (ports .lookupRestore) = [])
    (x : Fin v × Fin (degree d)) (indexSuffix : List Bool)
    (counterWord : base (ports .queryIndex) =
      encodeWord (rowIndex v (degree d) x).val ++ indexSuffix)
    (workEmpty : base (ports .lookupWork) = [])
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code tableWord scratchEmpty counterWord workEmpty

/-- Actual first/second lookup execution on a stored graph row. The selected
reverse index is obtained from `rotationWords_getElem?`, not a caller premise. -/
theorem lookupPhaseTrace :
    (advance (TM2.step target))^[MachinePreservingLookupClean.steps
        (rotationWords G) (rowIndex v (degree d) x).val]
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩) =
      some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩ := by
  apply MachinePreservingLookupClean.traceAt_fromTapes (ports ∘ lookupTape)
    (distinct.comp lookupTape_injective)
    (fun l => labels (lookupPhaseLabel second l)) (some (labels (scanPhaseLabel second)))
    target
  · intro l
    cases second
    · exact code (.firstLookup l)
    · exact code (.secondLookup l)
  · exact tableWord
  · exact scratchEmpty
  · exact rotationWords_getElem? G (rowIndex v (degree d) x)
  · exact counterWord
  · exact workEmpty

/-- A linear bound in the original encoded table length for the same actual
phase. This includes the copy, restore, lookup, and residual cleanup. -/
def lookupPhaseInTime :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩
      (some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩)
      (6 * (encodeWords (rotationWords G)).length + 4) where
  steps := MachinePreservingLookupClean.steps (rotationWords G) (rowIndex v (degree d) x).val
  evals_in_steps := lookupPhaseTrace second positive H ports distinct labels exit target code
    base G tableWord scratchEmpty x indexSuffix counterWord workEmpty ambient register
  steps_le_m := MachinePreservingLookupClean.steps_le (rotationWords G) _ _
    (rotationWords_getElem? G (rowIndex v (degree d) x))

end Lookup

variable {d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool)
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code

/-- The reversal consumes the reverse query word and prepends its forward
encoding to the index tape, retaining every other tape and finite state. -/
theorem reversePhaseTrace :
    (advance (TM2.step target))^[(base (ports .queryReverse)).length + 1]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩ := by
  have h := Reduction.MachineTransfer.transferAt_fromTapes
    (ports .queryReverse) (ports .queryIndex)
    (fun h => (by decide : Tape.queryReverse ≠ .queryIndex) (distinct h))
    id false (labels (reversePhaseLabel second))
    (some (labels (lookupPhaseLabel second (.run .copyFirst)))) target
    (by cases second <;> exact code _) base ambient register
  unfold Reduction.MachineTransfer.nextAt at h
  unfold advance
  simpa only [List.map_id] using h

def reversePhaseInTime :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩)
      ((base (ports .queryReverse)).length + 1) where
  steps := (base (ports .queryReverse)).length + 1
  evals_in_steps := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  steps_le_m := Nat.le_refl _

/-- Reversing an actual emitted unary field takes exactly `index + 2` steps.
This includes consuming the field's delimiter and leaving the reversal loop. -/
theorem reversePhaseTrace_unary (index : Nat) (suffix : List Bool)
    (queryWord : base (ports .queryReverse) = (encodeWord index).reverse)
    (indexWord : base (ports .queryIndex) = suffix) :
    (advance (TM2.step target))^[index + 2]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          (encodeWord index ++ suffix)⟩ := by
  have h := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  simpa only [queryWord, indexWord, List.length_reverse, encodeWord_length,
    List.reverse_reverse, Nat.add_assoc] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
