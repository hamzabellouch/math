import OAI.Computability.UniqueGames.Reduction.AddressOutcomeSpecs
import OAI.Computability.UniqueGames.Reduction.AddressTupleCleanupLemmas
import OAI.Computability.UniqueGames.Reduction.MachineAddressEdgeLemmas

namespace OAI


namespace UniqueGamesTheorem.Integration.AddressTupleBody

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
      (CanonicalAddress.base F.variables F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple =
      AddressOutcomeSpecs.tupleBits (source F) k T tuple := by
  unfold tupleBits
  rw [rhs_eq_actual, canonicalValues_eq_actual]
  exact AddressOutcomeSpecs.tuplePayload_actual (source F) k T tuple

/-- All generic template-correctness obligations are discharged from the
actual loader's canonical field values and the checked fixed-row specs. -/
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

/-- Actual fixed-row execution. Physical readiness and stored header values
are its only data hypotheses; no template or body-execution premise remains. -/
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
      encodeWord (CanonicalAddress.base F.variables F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      (budget (AddressOutcomeSpecs.rows k T)
        (CanonicalAddress.base F.variables F.equations.length s d)
        (AddressGame.bodyCapacity (source F) k s d)
        (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base) := by
  have actual := run_fixed_rows T labels exit P atLabels F tuple base ready clean oldRhs
    (CanonicalAddress.base F.variables F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d) hB hC
  rw [finalTapes_eq _ _ _ _ F tuple base ready, tupleBits_actual] at actual
  exact actual

theorem saved_of_current (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (currentWords : ∀j, base (current k s d noiseCount j) = encodeWord (digits j).val) :
    ∀j, base (.savedIndex j) = encodeWord (digits j.rev).val := by
  intro j
  simpa only [AddressMachineSpace.current_rev] using currentWords j.rev

end UniqueGamesTheorem.Integration.AddressTupleBody

end OAI
