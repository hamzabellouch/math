import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas
import OAI.Computability.UniqueGames.Reduction.MachineAddressEdgeLemmas
import OAI.Computability.UniqueGames.Reduction.MachineAddressHeaders
import OAI.Computability.UniqueGames.Reduction.SourceEquationLookupLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.AddressMachineSpace

open UniqueGamesTheorem.Foundations.Complexity

abbrev Extra (k s d noiseCount : Nat) :=
  MachineAddressHeaders.Arithmetic.Layout k s d noiseCount ⊕
    (MachineTemplateAddress.Tape (4 * k) (1 + 9 * k) ⊕ (Fin k ⊕ Unit))

abbrev Tape (k s d noiseCount : Nat) :=
  MachineSourceTuple.Tape k (Extra k s d noiseCount)

abbrev Control (k : Nat) := ((Fin k → Bool) × Unit) × Unit
abbrev State (k : Nat) := Control k × Option Bool

def initialState (k : Nat) : State k := (((fun _ => false, ()), ()), none)

variable (k s d noiseCount : Nat)

def headerArithmeticSlots : MachineAddressHeaders.Arithmetic.Layout k s d noiseCount ↪
    Tape k s d noiseCount where
  toFun a := .extra (.inl a)
  inj' := by intro a b h; exact Sum.inl.inj (MachineSourceTuple.Tape.extra.inj h)

def headerTape (c : MachineAddressHeaders.Arithmetic.Control) : Tape k s d noiseCount :=
  .extra (.inl (.inl c))

@[simp] theorem headerTape_eq_iff (a b : MachineAddressHeaders.Arithmetic.Control) :
    headerTape k s d noiseCount a = headerTape k s d noiseCount b ↔ a = b := by
  simp [headerTape]

def fullHeaderSlots : MachineAddressHeaders.Layout k s d noiseCount ↪ Tape k s d noiseCount where
  toFun
    | .inl 0 => .source
    | .inl 1 => .work
    | .inr a => headerArithmeticSlots k s d noiseCount a
  inj' := by
    rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> cases h <;> rfl
    · fin_cases a <;> cases h
    · fin_cases b <;> cases h
    · exact congrArg Sum.inr ((headerArithmeticSlots k s d noiseCount).injective h)

@[simp] theorem fullHeaderSlots_source : fullHeaderSlots k s d noiseCount (.inl 0) = .source := rfl
@[simp] theorem fullHeaderSlots_work : fullHeaderSlots k s d noiseCount (.inl 1) = .work := rfl
@[simp] theorem fullHeaderSlots_arithmetic (a : MachineAddressHeaders.Arithmetic.Layout k s d noiseCount) :
    fullHeaderSlots k s d noiseCount (.inr a) = headerArithmeticSlots k s d noiseCount a := rfl

@[simp] theorem arithmeticSlots_fullHeaderSlots :
    MachineAddressHeaders.arithmeticSlots (fullHeaderSlots k s d noiseCount) =
      headerArithmeticSlots k s d noiseCount := by ext a; rfl

def prefixSlots : Fin 5 ↪ Tape k s d noiseCount :=
  MachineAddressHeaders.prefixSlots (fullHeaderSlots k s d noiseCount)

@[simp] theorem prefixSlots_source : prefixSlots k s d noiseCount 0 = .source := rfl
@[simp] theorem prefixSlots_work : prefixSlots k s d noiseCount 1 = .work := rfl
@[simp] theorem prefixSlots_variables :
    prefixSlots k s d noiseCount 2 = headerTape k s d noiseCount .variableCount := rfl
@[simp] theorem prefixSlots_occurrences :
    prefixSlots k s d noiseCount 3 = headerTape k s d noiseCount .occurrenceCount := rfl
@[simp] theorem prefixSlots_scratch :
    prefixSlots k s d noiseCount 4 = headerTape k s d noiseCount .scratch := rfl

def canonicalField (position : Fin k) (slot : Fin 4) : Tape k s d noiseCount :=
  if slot = 3 then .savedIndex position else .field position slot

def rhsField (position : Fin k) : Tape k s d noiseCount := .field position 3

@[simp] theorem canonicalField_occurrence (position : Fin k) :
    canonicalField k s d noiseCount position 3 = .savedIndex position := by simp [canonicalField]

@[simp] theorem canonicalField_name (position : Fin k) (slot : Fin 3) :
    canonicalField k s d noiseCount position (MachineSourceTuple.nameSlot slot) =
      MachineSourceTuple.nameField position slot := by
  have hs : MachineSourceTuple.nameSlot slot ≠ (3 : Fin 4) := by
    intro h
    have hv := congrArg Fin.val h
    have bound := slot.isLt
    simp only [MachineSourceTuple.nameSlot] at hv
    omega
  simp [canonicalField, hs, MachineSourceTuple.nameField]

theorem canonicalField_ne_rhsField (position other : Fin k) (slot : Fin 4) :
    canonicalField k s d noiseCount position slot ≠ rhsField k s d noiseCount other := by
  by_cases h : slot = 3 <;> simp [canonicalField, rhsField, h]

def privateAddress (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    Tape k s d noiseCount := .extra (.inr (.inl tape))

def edgeSlot : MachineAddressEdge.Tape (4 * k) (1 + 9 * k) → Tape k s d noiseCount
  | .inl (.field i) => canonicalField k s d noiseCount
      ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2
  | .inl .radix => headerTape k s d noiseCount .baseValue
  | .inl tape => privateAddress k s d noiseCount tape
  | .inr i => if i = 0 then headerTape k s d noiseCount .capacity
      else headerTape k s d noiseCount .reversed

/-- A partial inverse proves separation without a default element of `Fin k`.
It therefore applies unchanged at `k = 0`. -/
private def edgeDecode : Tape k s d noiseCount →
    Option (MachineAddressEdge.Tape (4 * k) (1 + 9 * k))
  | .savedIndex j => some (.inl (.field (CanonicalBodyMachine.fieldIndex j 3)))
  | .field j slot => if slot = 3 then none
      else some (.inl (.field (CanonicalBodyMachine.fieldIndex j slot)))
  | .extra (.inl (.inl .baseValue)) => some (.inl .radix)
  | .extra (.inl (.inl .capacity)) => some (.inr 0)
  | .extra (.inl (.inl .reversed)) => some (.inr 1)
  | .extra (.inr (.inl tape)) => some (.inl tape)
  | _ => none

private theorem edgeDecode_canonicalField (position : Fin k) (slot : Fin 4) :
    edgeDecode k s d noiseCount (canonicalField k s d noiseCount position slot) =
      some (.inl (.field (CanonicalBodyMachine.fieldIndex position slot))) := by
  by_cases h : slot = 3 <;> simp [canonicalField, edgeDecode, h]

private theorem edgeDecode_edgeSlot (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    edgeDecode k s d noiseCount (edgeSlot k s d noiseCount tape) = some tape := by
  rcases tape with tape | i
  · cases tape <;> try rfl
    rename_i index
    rw [edgeSlot, edgeDecode_canonicalField]
    exact congrArg (fun i => some (Sum.inl (MachineTemplateAddress.Tape.field i)))
      ((CanonicalBodyMachine.fieldEquiv k).apply_symm_apply index)
  · fin_cases i <;> rfl

def addressEdgeSlots : MachineAddressEdge.Tape (4 * k) (1 + 9 * k) ↪ Tape k s d noiseCount where
  toFun := edgeSlot k s d noiseCount
  inj' := by
    intro a b h
    have decoded := congrArg (edgeDecode k s d noiseCount) h
    apply Option.some.inj
    simpa only [edgeDecode_edgeSlot] using decoded

@[simp] theorem addressEdgeSlots_fieldIndex (position : Fin k) (slot : Fin 4) :
    addressEdgeSlots k s d noiseCount
      (.inl (.field (CanonicalBodyMachine.fieldIndex position slot))) =
        canonicalField k s d noiseCount position slot := by
  change canonicalField k s d noiseCount
    ((CanonicalBodyMachine.fieldEquiv k).symm
      (CanonicalBodyMachine.fieldEquiv k (position, slot))).1
    ((CanonicalBodyMachine.fieldEquiv k).symm
      (CanonicalBodyMachine.fieldEquiv k (position, slot))).2 = _
  simp only [Equiv.symm_apply_apply]

@[simp] theorem addressSlots_name (position : Fin k) (slot : Fin 3) :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
      (.field (CanonicalBodyMachine.fieldIndex position (MachineSourceTuple.nameSlot slot))) =
        MachineSourceTuple.nameField position slot := by
  exact (addressEdgeSlots_fieldIndex k s d noiseCount position _).trans
    (canonicalField_name k s d noiseCount position slot)

@[simp] theorem addressSlots_occurrence (position : Fin k) :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
      (.field (CanonicalBodyMachine.fieldIndex position 3)) = .savedIndex position := by
  exact (addressEdgeSlots_fieldIndex k s d noiseCount position 3).trans
    (canonicalField_occurrence k s d noiseCount position)

@[simp] theorem addressSlots_radix :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount) .radix =
      headerTape k s d noiseCount .baseValue := rfl
@[simp] theorem addressSlots_capacity :
    MachineAddressEdge.capacityTape (addressEdgeSlots k s d noiseCount) =
      headerTape k s d noiseCount .capacity := rfl
@[simp] theorem addressSlots_output :
    MachineAddressEdge.outputTape (addressEdgeSlots k s d noiseCount) =
      headerTape k s d noiseCount .reversed := rfl

def current (j : Fin k) : Tape k s d noiseCount := .savedIndex j.rev
def remaining (j : Fin k) : Tape k s d noiseCount := .extra (.inr (.inr (.inl j)))
def finalOutput : Tape k s d noiseCount := .extra (.inr (.inr (.inr ())))

@[simp] theorem current_rev (j : Fin k) : current k s d noiseCount j.rev = .savedIndex j := by
  simp [current]

def odometerSlots : MachineOdometerInit.Tape k ↪ Tape k s d noiseCount where
  toFun
    | .radix => headerTape k s d noiseCount .occurrenceCount
    | .scratch => .copyScratch
    | .current j => current k s d noiseCount j
    | .remaining j => remaining k s d noiseCount j
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [headerTape, current, remaining]

@[simp] theorem odometerSlots_radix : odometerSlots k s d noiseCount .radix =
    headerTape k s d noiseCount .occurrenceCount := rfl
@[simp] theorem odometerSlots_scratch : odometerSlots k s d noiseCount .scratch = .copyScratch := rfl
@[simp] theorem odometerSlots_current (j : Fin k) :
    odometerSlots k s d noiseCount (.current j) = .savedIndex j.rev := rfl
@[simp] theorem odometerSlots_remaining (j : Fin k) :
    odometerSlots k s d noiseCount (.remaining j) = remaining k s d noiseCount j := rfl

theorem current_ne_remaining (j l : Fin k) :
    current k s d noiseCount j ≠ remaining k s d noiseCount l := by simp [current, remaining]
theorem current_ne_finalOutput (j : Fin k) :
    current k s d noiseCount j ≠ finalOutput k s d noiseCount := by simp [current, finalOutput]
theorem remaining_ne_finalOutput (j : Fin k) :
    remaining k s d noiseCount j ≠ finalOutput k s d noiseCount := by simp [remaining, finalOutput]

private theorem edgeSlot_ne_of_decode_none
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) (p : Tape k s d noiseCount)
    (h : edgeDecode k s d noiseCount p = none) : edgeSlot k s d noiseCount tape ≠ p := by
  intro same
  have decoded := congrArg (edgeDecode k s d noiseCount) same
  rw [edgeDecode_edgeSlot, h] at decoded
  cases decoded

theorem addressEdgeSlots_ne_rhsField
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) (j : Fin k) :
    addressEdgeSlots k s d noiseCount tape ≠ rhsField k s d noiseCount j :=
  edgeSlot_ne_of_decode_none k s d noiseCount tape _ rfl

theorem addressEdgeSlots_ne_source
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    addressEdgeSlots k s d noiseCount tape ≠ .source :=
  edgeSlot_ne_of_decode_none k s d noiseCount tape _ rfl

theorem addressEdgeSlots_ne_copyScratch
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    addressEdgeSlots k s d noiseCount tape ≠ .copyScratch :=
  edgeSlot_ne_of_decode_none k s d noiseCount tape _ rfl

/-- Only the radix, capacity, and reversed accumulator intentionally overlap
the address emitter's tapes with the arithmetic block. -/
theorem addressEdgeSlots_ne_headerTape
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k))
    (c : MachineAddressHeaders.Arithmetic.Control)
    (hb : c ≠ .baseValue) (hc : c ≠ .capacity) (hr : c ≠ .reversed) :
    addressEdgeSlots k s d noiseCount tape ≠ headerTape k s d noiseCount c := by
  apply edgeSlot_ne_of_decode_none
  cases c <;> simp_all [edgeDecode, headerTape]

theorem addressEdgeSlots_ne_remaining
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) (j : Fin k) :
    addressEdgeSlots k s d noiseCount tape ≠ remaining k s d noiseCount j :=
  edgeSlot_ne_of_decode_none k s d noiseCount tape _ rfl

theorem addressEdgeSlots_ne_finalOutput
    (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    addressEdgeSlots k s d noiseCount tape ≠ finalOutput k s d noiseCount :=
  edgeSlot_ne_of_decode_none k s d noiseCount tape _ rfl

theorem headerTape_ne_finalOutput (c : MachineAddressHeaders.Arithmetic.Control) :
    headerTape k s d noiseCount c ≠ finalOutput k s d noiseCount := by
  simp [headerTape, finalOutput]

theorem headerTape_ne_current (c : MachineAddressHeaders.Arithmetic.Control) (j : Fin k) :
    headerTape k s d noiseCount c ≠ current k s d noiseCount j := by
  simp [headerTape, current]

theorem headerTape_ne_remaining (c : MachineAddressHeaders.Arithmetic.Control) (j : Fin k) :
    headerTape k s d noiseCount c ≠ remaining k s d noiseCount j := by
  simp [headerTape, remaining]

theorem tupleOutput_headerTape (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple base k (headerTape k s d noiseCount c) =
      base (headerTape k s d noiseCount c) :=
  MachineSourceTuple.stageTapes_frame F tuple base k _
    (by simp [headerTape])
    (by simp [headerTape])
    (by intros; simp [headerTape])

theorem tupleOutput_source (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool) :
    MachineSourceTuple.stageTapes F tuple base k .source = base .source :=
  MachineSourceTuple.output_source F tuple base

theorem tupleOutput_rhs (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool)
    (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple base k (rhsField k s d noiseCount j) =
      encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++
        base (rhsField k s d noiseCount j) :=
  MachineSourceTuple.output_rhs F tuple base j

theorem tupleOutput_occurrence (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val) (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple base k
      (MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
        (.field (CanonicalBodyMachine.fieldIndex j 3))) = encodeWord (tuple j).val := by
  rw [addressSlots_occurrence]
  exact MachineSourceTuple.output_savedIndex_unary F tuple base hsaved j

end UniqueGamesTheorem.Reduction.AddressMachineSpace

end

end OAI
