import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.CanonicalWordTemplate

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

namespace DFVSGames.Integration.AddressTupleLoaded

open DFVSGames.Reduction DFVSGames.Foundations.Complexity

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

variable {k s d noiseCount : Nat}

def fieldAssignment (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool
  | .field j slot => encodeWord
      ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) ++
        baseArena (.field j slot)
  | tape => baseArena tape

theorem stageTapes_eq (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hindex : baseArena .index = []) (hwork : baseArena .work = []) :
    MachineSourceTuple.stageTapes F tuple baseArena k = fieldAssignment F tuple baseArena := by
  funext tape
  cases tape with
  | index => exact (MachineSourceTuple.stageTapes_clean F tuple baseArena k hindex hwork).1.trans hindex.symm
  | work => exact (MachineSourceTuple.stageTapes_clean F tuple baseArena k hindex hwork).2.trans hwork.symm
  | field j slot =>
    simp only [MachineSourceTuple.stageTapes_field, ite_eq_left j.isLt, fieldAssignment]
  | source =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | scratch =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | copyScratch =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | savedIndex j =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | extra value =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)

theorem fieldAssignment_frame (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (tape : Arena k s d noiseCount)
    (hfield : ∀ j slot, tape ≠ .field j slot) :
    fieldAssignment F tuple baseArena tape = baseArena tape := by
  cases tape <;> simp_all [fieldAssignment]

theorem loaded_frame (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hindex : baseArena .index = []) (hwork : baseArena .work = [])
    (tape : Arena k s d noiseCount) (hfield : ∀ j slot, tape ≠ .field j slot) :
    MachineSourceTuple.stageTapes F tuple baseArena k tape = baseArena tape := by
  rw [stageTapes_eq F tuple baseArena hindex hwork]
  exact fieldAssignment_frame F tuple baseArena tape hfield

theorem loaded_field (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.field j slot) =
      encodeWord ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) := by
  rw [MachineSourceTuple.stageTapes_field, ite_eq_left j.isLt, hempty, List.append_nil]

theorem loaded_source (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsource : baseArena .source = SourceEncoding.inputBits F) :
    MachineSourceTuple.stageTapes F tuple baseArena k .source = SourceEncoding.inputBits F :=
  (MachineSourceTuple.output_source F tuple baseArena).trans hsource

theorem loaded_extra (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (extra : AddressMachineSpace.Extra k s d noiseCount) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.extra extra) = baseArena (.extra extra) :=
  MachineSourceTuple.stageTapes_frame F tuple baseArena k _
    (by simp) (by simp) (by intros; simp)

theorem loaded_header (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (header : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.headerTape k s d noiseCount header) =
        baseArena (AddressMachineSpace.headerTape k s d noiseCount header) :=
  AddressMachineSpace.tupleOutput_headerTape k s d noiseCount F tuple baseArena header

theorem loaded_radix (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (B : Nat)
    (hB : baseArena (AddressMachineSpace.headerTape k s d noiseCount .baseValue) = encodeWord B) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        .radix) = encodeWord B := by
  rw [AddressMachineSpace.addressSlots_radix, loaded_header, hB]

theorem loaded_capacity (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (C : Nat)
    (hC : baseArena (AddressMachineSpace.headerTape k s d noiseCount .capacity) = encodeWord C) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.capacityTape (AddressMachineSpace.addressEdgeSlots k s d noiseCount)) =
        encodeWord C := by
  rw [AddressMachineSpace.addressSlots_capacity, loaded_header, hC]

theorem loaded_current (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.current k s d noiseCount j) =
        baseArena (AddressMachineSpace.current k s d noiseCount j) :=
  MachineSourceTuple.output_savedIndex F tuple baseArena j.rev

theorem loaded_remaining (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.remaining k s d noiseCount j) =
        baseArena (AddressMachineSpace.remaining k s d noiseCount j) :=
  loaded_extra F tuple baseArena _

theorem loaded_finalOutput (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.finalOutput k s d noiseCount) =
        baseArena (AddressMachineSpace.finalOutput k s d noiseCount) :=
  loaded_extra F tuple baseArena _

theorem loaded_loaderWork (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hindex : baseArena .index = []) (hwork : baseArena .work = [])
    (hscratch : baseArena .scratch = []) (hcopy : baseArena .copyScratch = []) :
    MachineSourceTuple.stageTapes F tuple baseArena k .index = [] ∧
      MachineSourceTuple.stageTapes F tuple baseArena k .work = [] ∧
      MachineSourceTuple.stageTapes F tuple baseArena k .scratch = [] ∧
      MachineSourceTuple.stageTapes F tuple baseArena k .copyScratch = [] := by
  have clean := MachineSourceTuple.stageTapes_clean F tuple baseArena k hindex hwork
  refine ⟨clean.1, clean.2, ?_, ?_⟩
  · exact (MachineSourceTuple.stageTapes_frame F tuple baseArena k .scratch
      (by simp) (by simp) (by intros; simp)).trans hscratch
  · exact (MachineSourceTuple.stageTapes_frame F tuple baseArena k .copyScratch
      (by simp) (by simp) (by intros; simp)).trans hcopy

theorem loaded_privateAddress (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.privateAddress k s d noiseCount tape) =
        baseArena (AddressMachineSpace.privateAddress k s d noiseCount tape) :=
  loaded_extra F tuple baseArena _

theorem loaded_clean (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (clean : MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      baseArena) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      (MachineSourceTuple.stageTapes F tuple baseArena k) := by
  constructor
  · constructor
    · exact (loaded_privateAddress F tuple baseArena .reversed).trans clean.address.reversed
    · exact (loaded_privateAddress F tuple baseArena .forward).trans clean.address.forward
    · exact (loaded_privateAddress F tuple baseArena .copyScratch).trans clean.address.copyScratch
    · exact (loaded_privateAddress F tuple baseArena .accA).trans clean.address.accA
    · exact (loaded_privateAddress F tuple baseArena .accB).trans clean.address.accB
    · exact (loaded_privateAddress F tuple baseArena .counter).trans clean.address.counter
    · exact (loaded_privateAddress F tuple baseArena .hornerScratch).trans clean.address.hornerScratch
    · intro j
      exact (loaded_privateAddress F tuple baseArena (.digit j)).trans (clean.address.digit j)
  · exact (loaded_privateAddress F tuple baseArena .output).trans clean.work

theorem loaded_rhs (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.rhsField k s d noiseCount j) =
        encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) := by
  rw [AddressMachineSpace.tupleOutput_rhs]
  change _ ++ baseArena (.field j 3) = _
  rw [hempty, List.append_nil]

theorem loaded_name (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 3) :
    MachineSourceTuple.stageTapes F tuple baseArena k (MachineSourceTuple.nameField j slot) =
      encodeWord (MachineSourceTuple.equationName F.equations[(tuple j).val] slot) := by
  rw [MachineSourceTuple.output_name]
  change _ ++ baseArena (.field j (MachineSourceTuple.nameSlot slot)) = _
  rw [hempty, List.append_nil]

theorem loaded_occurrence (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val) (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.savedIndex j) = encodeWord (tuple j).val :=
  MachineSourceTuple.output_savedIndex_unary F tuple baseArena hsaved j

def canonicalValues (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (j : Fin k) : Fin 4 → Nat :=
  CanonicalBodyTemplate.recordFields
    (MachineSourceTuple.equationName F.equations[(tuple j).val]) (tuple j).val

theorem loaded_canonicalField (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.canonicalField k s d noiseCount j slot) =
        encodeWord (canonicalValues F tuple j slot) := by
  fin_cases slot
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 0
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 1
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 2
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields] using
      loaded_occurrence F tuple baseArena hsaved j

theorem loaded_savedFields (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) :
    (fun i => MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (.field i))) = CanonicalBodyMachine.savedFields (canonicalValues F tuple) := by
  funext i
  change MachineSourceTuple.stageTapes F tuple baseArena k
    (AddressMachineSpace.canonicalField k s d noiseCount
      ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2) = _
  exact loaded_canonicalField F tuple baseArena hsaved hempty _ _

end DFVSGames.Integration.AddressTupleLoaded
end

section

namespace DFVSGames.Integration.AddressTupleCleanup

open Turing DFVSGames.Reduction DFVSGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

def loadedFields : List (AddressMachineSpace.Tape k s d noiseCount) :=
  List.ofFn (fun i : Fin (4 * k) =>
    MachineSourceTuple.Tape.field ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2)

@[simp] theorem loadedFields_length : (loadedFields k s d noiseCount).length = 4 * k := by
  simp only [loadedFields, List.length_ofFn]

theorem mem_loadedFields (tape : AddressMachineSpace.Tape k s d noiseCount) :
    tape ∈ loadedFields k s d noiseCount ↔
      ∃ position : Fin k, ∃ slot : Fin 4, tape = .field position slot := by
  unfold loadedFields
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact ⟨((CanonicalBodyMachine.fieldEquiv k).symm i).1,
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2, hi.symm⟩
  · rintro ⟨position, slot, rfl⟩
    apply List.mem_ofFn.mpr
    refine ⟨CanonicalBodyMachine.fieldEquiv k (position, slot), ?_⟩
    simp only [Equiv.symm_apply_apply]

abbrev Label := MachineDrainMany.Label (loadedFields k s d noiseCount)

noncomputable abbrev cleared (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.finalTapes (loadedFields k s d noiseCount) base

noncomputable abbrev steps (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.steps (loadedFields k s d noiseCount) base

noncomputable abbrev budget (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.lengthSum (loadedFields k s d noiseCount) base + 4 * k

@[simp] theorem cleared_field (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (position : Fin k) (slot : Fin 4) :
    cleared k s d noiseCount base (.field position slot) = [] :=
  MachineDrainMany.finalTapes_mem (loadedFields k s d noiseCount) base (.field position slot)
    ((mem_loadedFields k s d noiseCount _).2 ⟨position, slot, rfl⟩)

theorem cleared_outside (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (tape : AddressMachineSpace.Tape k s d noiseCount)
    (outside : ∀ position : Fin k, ∀ slot : Fin 4, tape ≠ .field position slot) :
    cleared k s d noiseCount base tape = base tape := by
  apply MachineDrainMany.finalTapes_not_mem
  intro h
  obtain ⟨position, slot, same⟩ := (mem_loadedFields k s d noiseCount tape).1 h
  exact outside position slot same

@[simp] theorem cleared_source (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .source = base .source := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_savedIndex
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) (position : Fin k) :
    cleared k s d noiseCount base (.savedIndex position) = base (.savedIndex position) := by
  apply cleared_outside
  intro other slot h
  cases h

@[simp] theorem cleared_extra (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (extra : AddressMachineSpace.Extra k s d noiseCount) :
    cleared k s d noiseCount base (.extra extra) = base (.extra extra) := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_index (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .index = base .index := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_work (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .work = base .work := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_scratch (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .scratch = base .scratch := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_copyScratch (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .copyScratch = base .copyScratch := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_headerTape
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (header : MachineAddressHeaders.Arithmetic.Control) :
    cleared k s d noiseCount base (AddressMachineSpace.headerTape k s d noiseCount header) =
      base (AddressMachineSpace.headerTape k s d noiseCount header) := by
  simpa only [AddressMachineSpace.headerTape, AddressMachineSpace.headerArithmeticSlots] using
    cleared_extra k s d noiseCount base (.inl (.inl header))

@[simp] theorem cleared_current (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (position : Fin k) :
    cleared k s d noiseCount base (AddressMachineSpace.current k s d noiseCount position) =
      base (AddressMachineSpace.current k s d noiseCount position) := by
  simpa only [AddressMachineSpace.current] using
    cleared_savedIndex k s d noiseCount base position.rev

@[simp] theorem cleared_remaining (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (position : Fin k) :
    cleared k s d noiseCount base (AddressMachineSpace.remaining k s d noiseCount position) =
      base (AddressMachineSpace.remaining k s d noiseCount position) := by
  simpa only [AddressMachineSpace.remaining] using
    cleared_extra k s d noiseCount base (.inr (.inr (.inl position)))

@[simp] theorem cleared_finalOutput
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base (AddressMachineSpace.finalOutput k s d noiseCount) =
      base (AddressMachineSpace.finalOutput k s d noiseCount) := by
  simpa only [AddressMachineSpace.finalOutput] using
    cleared_extra k s d noiseCount base (.inr (.inr (.inr ())))

theorem steps_le (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    steps k s d noiseCount base ≤ budget k s d noiseCount base := by
  simpa only [loadedFields_length] using
    MachineDrainMany.steps_le (loadedFields k s d noiseCount) base

theorem steps_le_uniform (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (bound : Nat) (h : ∀ tape, (base tape).length ≤ bound) :
    steps k s d noiseCount base ≤ 4 * k * (bound + 1) := by
  simpa only [loadedFields_length] using
    MachineDrainMany.steps_le_uniform (loadedFields k s d noiseCount) base bound h

variable {Λ : Type}

abbrev entry (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :=
  MachineDrainMany.entry (loadedFields k s d noiseCount) labels exit

def instruction (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :
    Label k s d noiseCount → TM2.Stmt
      (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool) Λ (AddressMachineSpace.State k) :=
  MachineDrainMany.instruction (loadedFields k s d noiseCount) labels exit

theorem trace (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[steps k s d noiseCount base]
      (some ⟨entry k s d noiseCount labels exit, (control, register), base⟩) =
    some ⟨exit, (control, MachineDrainMany.finalRegister (loadedFields k s d noiseCount) register),
      cleared k s d noiseCount base⟩ :=
  MachineDrainMany.trace (loadedFields k s d noiseCount) labels exit program atLabels
    base control register

theorem trace_clean (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) :
    (MachineComposition.advance (TM2.step program))^[steps k s d noiseCount base]
      (some ⟨entry k s d noiseCount labels exit, (control, none), base⟩) =
    some ⟨exit, (control, none), cleared k s d noiseCount base⟩ := by
  simpa only [MachineDrainMany.finalRegister_none] using
    trace k s d noiseCount labels exit program atLabels base control none

noncomputable def execution (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry k s d noiseCount labels exit, (control, register), base⟩
      (some ⟨exit,
        (control, MachineDrainMany.finalRegister (loadedFields k s d noiseCount) register),
        cleared k s d noiseCount base⟩) (budget k s d noiseCount base) where
  steps := steps k s d noiseCount base
  evals_in_steps := trace k s d noiseCount labels exit program atLabels base control register
  steps_le_m := steps_le k s d noiseCount base

end DFVSGames.Integration.AddressTupleCleanup
end

section

namespace DFVSGames.Integration.AddressTupleFrame

open DFVSGames.Reduction DFVSGames.Foundations.Complexity

variable {k s d noiseCount : Nat}

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

theorem cleared_outputTapes (base : Arena k s d noiseCount → List Bool)
    (output : Arena k s d noiseCount) (bits : List Bool)
    (outside : ∀ j : Fin k, ∀ slot : Fin 4, output ≠ .field j slot) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineFieldTemplate.outputTapes base output bits) =
      MachineFieldTemplate.outputTapes
        (AddressTupleCleanup.cleared k s d noiseCount base) output bits := by
  funext tape
  by_cases h : tape = output
  · subst tape
    rw [AddressTupleCleanup.cleared_outside k s d noiseCount _ output outside,
      MachineFieldTemplate.outputTapes_output, MachineFieldTemplate.outputTapes_output,
      AddressTupleCleanup.cleared_outside k s d noiseCount base output outside]
  · rw [MachineFieldTemplate.outputTapes_other _ output bits tape h]
    change MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount)
        (MachineFieldTemplate.outputTapes base output bits) tape =
      MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount) base tape
    rw [MachineDrainMany.finalTapes_apply, MachineDrainMany.finalTapes_apply,
      MachineFieldTemplate.outputTapes_other base output bits tape h]

theorem cleared_appended (base : Arena k s d noiseCount → List Bool) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          base bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (AddressTupleCleanup.cleared k s d noiseCount base) bits := by
  apply cleared_outputTapes
  intro j slot
  simp [AddressMachineSpace.addressSlots_output, AddressMachineSpace.headerTape,
    ]

theorem cleared_fieldAssignment (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hfields : ∀ j slot, base (.field j slot) = []) :
    AddressTupleCleanup.cleared k s d noiseCount
      (AddressTupleLoaded.fieldAssignment F tuple base) = base := by
  funext tape
  cases tape <;> simp [AddressTupleLoaded.fieldAssignment, hfields]

theorem cleared_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) :
    AddressTupleCleanup.cleared k s d noiseCount
      (MachineSourceTuple.stageTapes F tuple base k) = base := by
  rw [AddressTupleLoaded.stageTapes_eq F tuple base hindex hwork]
  exact cleared_fieldAssignment F tuple base hfields

theorem cleared_appended_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          (MachineSourceTuple.stageTapes F tuple base k) bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        base bits := by
  rw [cleared_appended, cleared_loaded F tuple base hindex hwork hfields]

noncomputable abbrev finalTapes (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (bits : List Bool) :
    Arena k s d noiseCount → List Bool :=
  AddressTupleCleanup.cleared k s d noiseCount
    (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      (MachineSourceTuple.stageTapes F tuple base k) bits)

section Frame

variable (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
  (base : Arena k s d noiseCount → List Bool)
  (hindex : base .index = []) (hwork : base .work = [])
  (hfields : ∀ j slot, base (.field j slot) = []) (bits : List Bool)

include hindex hwork hfields

theorem finalTapes_other (tape : Arena k s d noiseCount)
    (hne : tape ≠ MachineAddressEdge.outputTape
      (AddressMachineSpace.addressEdgeSlots k s d noiseCount)) :
    finalTapes F tuple base bits tape = base tape := by
  rw [finalTapes, cleared_appended_loaded F tuple base hindex hwork hfields bits]
  exact MachineAddressEdge.appended_other _ base bits tape hne

theorem finalTapes_source : finalTapes F tuple base bits .source = base .source := by
  apply finalTapes_other F tuple base hindex hwork hfields bits
  simp [AddressMachineSpace.addressSlots_output, AddressMachineSpace.headerTape,
    ]

theorem finalTapes_current (j : Fin k) :
    finalTapes F tuple base bits (AddressMachineSpace.current k s d noiseCount j) =
      base (AddressMachineSpace.current k s d noiseCount j) := by
  apply finalTapes_other F tuple base hindex hwork hfields bits
  simpa only [AddressMachineSpace.addressSlots_output] using
    (AddressMachineSpace.headerTape_ne_current k s d noiseCount .reversed j).symm

theorem finalTapes_remaining (j : Fin k) :
    finalTapes F tuple base bits (AddressMachineSpace.remaining k s d noiseCount j) =
      base (AddressMachineSpace.remaining k s d noiseCount j) := by
  apply finalTapes_other F tuple base hindex hwork hfields bits
  simpa only [AddressMachineSpace.addressSlots_output] using
    (AddressMachineSpace.headerTape_ne_remaining k s d noiseCount .reversed j).symm

theorem finalTapes_header (header : MachineAddressHeaders.Arithmetic.Control)
    (hne : header ≠ .reversed) :
    finalTapes F tuple base bits (AddressMachineSpace.headerTape k s d noiseCount header) =
      base (AddressMachineSpace.headerTape k s d noiseCount header) := by
  apply finalTapes_other F tuple base hindex hwork hfields bits
  intro same
  apply hne
  exact (AddressMachineSpace.headerTape_eq_iff k s d noiseCount header .reversed).mp same

theorem finalTapes_radix :
    finalTapes F tuple base bits (MachineAddressEdge.addressSlots
        (AddressMachineSpace.addressEdgeSlots k s d noiseCount) .radix) =
      base (MachineAddressEdge.addressSlots
        (AddressMachineSpace.addressEdgeSlots k s d noiseCount) .radix) := by
  rw [finalTapes, cleared_appended_loaded F tuple base hindex hwork hfields bits]
  exact MachineAddressEdge.appended_address _ base bits .radix

theorem finalTapes_capacity :
    finalTapes F tuple base bits (MachineAddressEdge.capacityTape
        (AddressMachineSpace.addressEdgeSlots k s d noiseCount)) =
      base (MachineAddressEdge.capacityTape
        (AddressMachineSpace.addressEdgeSlots k s d noiseCount)) := by
  rw [finalTapes, cleared_appended_loaded F tuple base hindex hwork hfields bits]
  exact MachineAddressEdge.appended_capacity _ base bits

theorem finalTapes_output :
    finalTapes F tuple base bits (MachineAddressEdge.outputTape
        (AddressMachineSpace.addressEdgeSlots k s d noiseCount)) =
      bits.reverse ++ base (MachineAddressEdge.outputTape
        (AddressMachineSpace.addressEdgeSlots k s d noiseCount)) := by
  rw [finalTapes, cleared_appended_loaded F tuple base hindex hwork hfields bits]
  exact MachineAddressEdge.appended_output _ base bits

theorem finalTapes_clean
    (clean : MachineAddressEdge.Clean
      (AddressMachineSpace.addressEdgeSlots k s d noiseCount) base) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      (finalTapes F tuple base bits) := by
  rw [finalTapes, cleared_appended_loaded F tuple base hindex hwork hfields bits]
  exact MachineAddressEdge.Clean.appended _ base clean bits

end Frame

end DFVSGames.Integration.AddressTupleFrame
end

section

namespace DFVSGames.Reduction.MachineRhsLoad

open Turing
open DFVSGames.Foundations.Complexity

abbrev State (k : Nat) (σ : Type) := (((Fin k → Bool) × σ) × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

def rhs {k σ} (state : State k σ) : Fin k → Bool := state.1.1.1

def setRhs {k σ} (state : State k σ) (values : Fin k → Bool) : State k σ :=
  (((values, state.1.1.2), state.1.2), state.2)

@[simp] theorem rhs_setRhs {k σ} (state : State k σ) (values : Fin k → Bool) :
    rhs (setRhs state values) = values := rfl

@[simp] theorem setRhs_setRhs {k σ} (state : State k σ)
    (first second : Fin k → Bool) : setRhs (setRhs state first) second = setRhs state second := rfl

@[simp] theorem setRhs_same {k σ} (state : State k σ) : setRhs state (rhs state) = state := rfl

def fill {k : Nat} (values initial : Fin k → Bool) (cells : List (Fin k)) : Fin k → Bool :=
  cells.foldl (fun current i => Function.update current i (values i)) initial

theorem fill_apply {k : Nat} (values initial : Fin k → Bool) (cells : List (Fin k))
    (i : Fin k) : fill values initial cells i = if i ∈ cells then values i else initial i := by
  induction cells generalizing initial with
  | nil => simp [fill]
  | cons j cells ih =>
    change fill values (Function.update initial j (values j)) cells i = _
    rw [ih]
    by_cases hi : i ∈ cells
    · simp [hi]
    · by_cases hij : i = j
      · subst j; simp [hi]
      · simp [hi, hij]

theorem fill_all {k : Nat} (values initial : Fin k → Bool) :
    fill values initial (List.finRange k) = values := by
  funext i
  rw [fill_apply]
  simp only [List.mem_finRange, ↓reduceIte]

section Program

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State k σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def peekChain (field : Fin k → K) (exit : Option Λ) :
    List (Fin k) → TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | [] => finish exit
  | i :: rest =>
    .peek (field i) (fun state head =>
      setRhs state (Function.update (rhs state) i (head.getD false)))
      (peekChain field exit rest)

def statement (field : Fin k → K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State k σ) := peekChain field exit (List.finRange k)

def readRhs (field : Fin k → K) (tapes : K → List Bool) : Fin k → Bool :=
  fun i => (tapes (field i)).head?.getD false

theorem stepAux_peekChain (field : Fin k → K) (exit : Option Λ)
    (cells : List (Fin k)) (state : State k σ) (tapes : K → List Bool) :
    TM2.stepAux (peekChain field exit cells) state tapes =
      ⟨exit, setRhs state (fill (readRhs field tapes) (rhs state) cells), tapes⟩ := by
  induction cells generalizing state with
  | nil => cases exit <;> rfl
  | cons i rest ih =>
    simp only [peekChain, TM2.stepAux]
    rw [ih]
    rfl

theorem stepAux_statement (field : Fin k → K) (exit : Option Λ)
    (state : State k σ) (tapes : K → List Bool) :
    TM2.stepAux (statement field exit) state tapes =
      ⟨exit, setRhs state (readRhs field tapes), tapes⟩ := by
  rw [statement, stepAux_peekChain, fill_all]

omit [DecidableEq K] in
theorem readRhs_of_unary (field : Fin k → K) (tapes : K → List Bool)
    (values : Fin k → Bool) (suffix : Fin k → List Bool)
    (encoded : ∀ i, tapes (field i) = encodeWord (if values i then 1 else 0) ++ suffix i) :
    readRhs field tapes = values := by
  funext i
  rw [readRhs, encoded]
  cases values i <;> rfl

theorem loadStep (field : Fin k → K) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atEntry : program entry = statement field exit)
    (state : State k σ) (tapes : K → List Bool) (values : Fin k → Bool)
    (suffix : Fin k → List Bool)
    (encoded : ∀ i, tapes (field i) = encodeWord (if values i then 1 else 0) ++ suffix i) :
    TM2.step program ⟨some entry, state, tapes⟩ =
      some ⟨exit, setRhs state values, tapes⟩ := by
  change some (TM2.stepAux (program entry) state tapes) = _
  rw [atEntry, stepAux_statement, readRhs_of_unary field tapes values suffix encoded]

def loadInTime (field : Fin k → K) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atEntry : program entry = statement field exit)
    (state : State k σ) (tapes : K → List Bool) (values : Fin k → Bool)
    (suffix : Fin k → List Bool)
    (encoded : ∀ i, tapes (field i) = encodeWord (if values i then 1 else 0) ++ suffix i) :
    StateTransition.EvalsToInTime (TM2.step program) ⟨some entry, state, tapes⟩
      (some ⟨exit, setRhs state values, tapes⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      loadStep field entry exit program atEntry state tapes values suffix encoded
  steps_le_m := Nat.le_refl _

omit [DecidableEq K] in
theorem peekChain_pushBound (field : Fin k → K) (exit : Option Λ) (cells : List (Fin k)) :
    Runtime.statementPushBound (peekChain (σ := σ) field exit cells) = 0 := by
  induction cells with
  | nil => cases exit <;> rfl
  | cons i rest ih => exact ih

omit [DecidableEq K] in
theorem statement_pushBound (field : Fin k → K) (exit : Option Λ) :
    Runtime.statementPushBound (statement (σ := σ) field exit) = 0 :=
  peekChain_pushBound field exit (List.finRange k)

end Program

end DFVSGames.Reduction.MachineRhsLoad
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
