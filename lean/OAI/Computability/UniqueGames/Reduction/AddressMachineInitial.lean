import OAI.Computability.UniqueGames.Reduction.AddressOdometerSchedule
import OAI.Computability.UniqueGames.Reduction.AddressTuplePolynomialLemmas

namespace OAI


namespace UniqueGamesTheorem.Reduction.AddressMachineInitial

open Turing UniqueGamesTheorem.Foundations.Complexity


noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def afterHeaders (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineAddressHeaders.resultTapes (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
    (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F))
    F.variables F.equations.length

def initialized (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineOdometerInit.stageTapes (AddressMachineSpace.odometerSlots k s d T.vectors.length)
    F.equations.length (afterHeaders k T F) k

private theorem input_header (F : SourceEncoding.Input)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
      (AddressMachineSpace.headerTape k s d T.vectors.length c) = [] := by
  apply AddressMachineProgram.inputTapes_other
  simp [AddressMachineSpace.headerTape]

theorem input_headerClean (F : SourceEncoding.Input) :
    MachineAddressHeaders.Clean (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)) := by
  refine {
    accA := input_header k T F .accA
    accB := input_header k T F .accB
    counter := input_header k T F .counter
    scratch := input_header k T F .scratch
    coefficients := ?_
    baseValue := input_header k T F .baseValue
    capacity := input_header k T F .capacity
    temporary := input_header k T F .temporary
    readCopy := ?_
    variableCount := input_header k T F .variableCount
    occurrenceCount := input_header k T F .occurrenceCount }
  · intro i
    change AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
      (.extra (.inl (.inr i))) = []
    exact AddressMachineProgram.inputTapes_other k T _ _ (by simp)
  · exact AddressMachineProgram.inputTapes_other k T _ .work (by simp)

theorem afterHeaders_frame (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hw : p ≠ .work)
    (hn : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .variableCount)
    (hm : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount)
    (hb : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .baseValue)
    (hc : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .capacity)
    (hr : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    afterHeaders k T F p = AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F) p :=
  MachineAddressHeaders.resultTapes_other _ _ _ _ p hw hn hm hb hc hr

theorem afterHeaders_empty (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hs : p ≠ .source) (hw : p ≠ .work)
    (hn : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .variableCount)
    (hm : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount)
    (hb : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .baseValue)
    (hc : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .capacity)
    (hr : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    afterHeaders k T F p = [] :=
  (afterHeaders_frame k T F p hw hn hm hb hc hr).trans
    (AddressMachineProgram.inputTapes_other k T _ p hs)

@[simp] theorem afterHeaders_source (F : SourceEncoding.Input) :
    afterHeaders k T F .source = SourceEncoding.inputBits F := by
  exact (MachineAddressHeaders.resultTapes_source _ _ F.variables F.equations.length).trans
    (AddressMachineProgram.inputTapes_source k T _)

@[simp] theorem afterHeaders_variables (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) =
      encodeWord F.variables := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .variableCount) = _
  rw [MachineAddressHeaders.resultTapes_n]
  change encodeWord F.variables ++ AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
    (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) = _
  rw [input_header, List.append_nil]

@[simp] theorem afterHeaders_occurrences (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) =
      encodeWord F.equations.length := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .occurrenceCount) = _
  rw [MachineAddressHeaders.resultTapes_m]
  change encodeWord F.equations.length ++ AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
    (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) = _
  rw [input_header, List.append_nil]

@[simp] theorem afterHeaders_base (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.variables F.equations.length) :=
  MachineAddressHeaders.resultTapes_base _ _ _ _

@[simp] theorem afterHeaders_capacity (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.variables F.equations.length) :=
  MachineAddressHeaders.resultTapes_capacity _ _ _ _

@[simp] theorem afterHeaders_reversed (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.variables F.equations.length).reverse := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .reversed) = _
  rw [MachineAddressHeaders.resultTapes_reversed]
  change (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
    F.variables F.equations.length).reverse ++ AddressMachineProgram.inputTapes k T
      (SourceEncoding.inputBits F) (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) = _
  rw [input_header, List.append_nil]

@[simp] theorem afterHeaders_work (F : SourceEncoding.Input) : afterHeaders k T F .work = [] :=
  MachineAddressHeaders.resultTapes_readCopy _ _ _ _

@[simp] theorem afterHeaders_current (F : SourceEncoding.Input) (j : Fin k) :
    afterHeaders k T F (AddressMachineSpace.current k s d T.vectors.length j) = [] := by
  apply afterHeaders_empty <;> simp [AddressMachineSpace.current, AddressMachineSpace.headerTape]

@[simp] theorem afterHeaders_remaining (F : SourceEncoding.Input) (j : Fin k) :
    afterHeaders k T F (AddressMachineSpace.remaining k s d T.vectors.length j) = [] := by
  apply afterHeaders_empty <;> simp [AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

@[simp] theorem afterHeaders_copyScratch (F : SourceEncoding.Input) :
    afterHeaders k T F .copyScratch = [] := by
  apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]

theorem initialized_frame (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hc : ∀ j, p ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀ j, p ≠ AddressMachineSpace.remaining k s d T.vectors.length j) :
    initialized k T F p = afterHeaders k T F p :=
  MachineOdometerInit.stageTapes_frame _ _ _ _ p hc hr

@[simp] theorem initialized_header (F : SourceEncoding.Input)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) =
      afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) :=
  initialized_frame k T F _
    (AddressMachineSpace.headerTape_ne_current k s d T.vectors.length c)
    (AddressMachineSpace.headerTape_ne_remaining k s d T.vectors.length c)

@[simp] theorem initialized_source (F : SourceEncoding.Input) :
    initialized k T F .source = SourceEncoding.inputBits F := by
  rw [initialized_frame k T F .source
    (by intro j; simp [AddressMachineSpace.current])
    (by intro j; simp [AddressMachineSpace.remaining])]
  exact afterHeaders_source k T F

@[simp] theorem initialized_variables (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) =
      encodeWord F.variables := by rw [initialized_header, afterHeaders_variables]
@[simp] theorem initialized_occurrences (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) =
      encodeWord F.equations.length := by rw [initialized_header, afterHeaders_occurrences]
@[simp] theorem initialized_base (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.variables F.equations.length) := by
  rw [initialized_header, afterHeaders_base]
@[simp] theorem initialized_capacity (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.variables F.equations.length) := by
  rw [initialized_header, afterHeaders_capacity]
@[simp] theorem initialized_reversed (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.variables F.equations.length).reverse := by
  rw [initialized_header, afterHeaders_reversed]

@[simp] theorem initialized_current (F : SourceEncoding.Input) (j : Fin k) :
    initialized k T F (AddressMachineSpace.current k s d T.vectors.length j) = encodeWord 0 :=
  MachineOdometerInit.output_current _ (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    F.equations.length (afterHeaders k T F) j

@[simp] theorem initialized_remaining (F : SourceEncoding.Input) (j : Fin k) :
    initialized k T F (AddressMachineSpace.remaining k s d T.vectors.length j) =
      encodeWord (F.equations.length - 1) :=
  MachineOdometerInit.output_remaining _ (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    F.equations.length (afterHeaders k T F) j

@[simp] theorem initialized_savedIndex (F : SourceEncoding.Input) (j : Fin k) :
    initialized k T F (.savedIndex j) = encodeWord 0 := by
  simpa only [AddressMachineSpace.current_rev] using initialized_current k T F j.rev

theorem initialized_empty (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hbefore : afterHeaders k T F p = [])
    (hc : ∀ j, p ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀ j, p ≠ AddressMachineSpace.remaining k s d T.vectors.length j) :
    initialized k T F p = [] := (initialized_frame k T F p hc hr).trans hbefore

@[simp] theorem initialized_work (F : SourceEncoding.Input) : initialized k T F .work = [] := by
  apply initialized_empty k T F _ (afterHeaders_work k T F) <;>
    intro j <;> simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_index (F : SourceEncoding.Input) : initialized k T F .index = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]
  all_goals
    intro j
    simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_scratch (F : SourceEncoding.Input) : initialized k T F .scratch = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]
  all_goals
    intro j
    simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_copyScratch (F : SourceEncoding.Input) :
    initialized k T F .copyScratch = [] := by
  apply initialized_empty k T F _ (afterHeaders_copyScratch k T F) <;>
    intro j <;> simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_field (F : SourceEncoding.Input) (j : Fin k) (slot : Fin 4) :
    initialized k T F (.field j slot) = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]
  all_goals
    intro i
    simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_finalOutput (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.finalOutput k s d T.vectors.length) = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;>
      simp [AddressMachineSpace.finalOutput, AddressMachineSpace.headerTape]
  all_goals
    intro i
    simp [AddressMachineSpace.finalOutput, AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_privateAddress (F : SourceEncoding.Input)
    (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    initialized k T F (AddressMachineSpace.privateAddress k s d T.vectors.length tape) = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;>
      simp [AddressMachineSpace.privateAddress, AddressMachineSpace.headerTape]
  all_goals
    intro i
    simp [AddressMachineSpace.privateAddress, AddressMachineSpace.current, AddressMachineSpace.remaining]

theorem initialized_edgeClean (F : SourceEncoding.Input) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (initialized k T F) := by
  constructor
  · constructor
    · exact initialized_privateAddress k T F .reversed
    · exact initialized_privateAddress k T F .forward
    · exact initialized_privateAddress k T F .copyScratch
    · exact initialized_privateAddress k T F .accA
    · exact initialized_privateAddress k T F .accB
    · exact initialized_privateAddress k T F .counter
    · exact initialized_privateAddress k T F .hornerScratch
    · intro j; exact initialized_privateAddress k T F (.digit j)
  · exact initialized_privateAddress k T F .output

/-- An exact equality with the checked schedule's initial digit configuration. -/
theorem initialized_eq_setDigits_zero (F : SourceEncoding.Input) :
    initialized k T F = AddressOdometerSchedule.setDigits F.equations.length
      (fun _ : Fin k => 0) (afterHeaders k T F) := by
  funext p
  by_cases hc : ∃ j, p = AddressMachineSpace.current k s d T.vectors.length j
  · obtain ⟨j, rfl⟩ := hc
    rw [initialized_current]
    symm
    exact (AddressOdometerSchedule.setDigits_current F.equations.length
      (fun _ : Fin k => 0) (afterHeaders k T F) j).trans (dite_eq_left j.isLt)
  · by_cases hr : ∃ j, p = AddressMachineSpace.remaining k s d T.vectors.length j
    · obtain ⟨j, rfl⟩ := hr
      rw [initialized_remaining]
      symm
      simpa only [Nat.sub_zero, AddressOdometerSchedule.remaining] using
        (AddressOdometerSchedule.setDigits_remaining F.equations.length
          (fun _ : Fin k => 0) (afterHeaders k T F) j).trans (dite_eq_left j.isLt)
    · have hc' : ∀ j, p ≠ AddressMachineSpace.current k s d T.vectors.length j :=
        fun j h => hc ⟨j, h⟩
      have hr' : ∀ j, p ≠ AddressMachineSpace.remaining k s d T.vectors.length j :=
        fun j h => hr ⟨j, h⟩
      exact (initialized_frame k T F p hc' hr').trans
        (AddressOdometerSchedule.setDigits_other F.equations.length
          (fun _ : Fin k => 0) (afterHeaders k T F) p hc' hr').symm

/-- Actual two-phase initialization from the concrete machine input. -/
def inTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits F))
      (some ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k,
        initialized k T F⟩)
      ((MachineAddressHeaders.timePolynomial k s d T.vectors.length).eval
        (SourceEncoding.inputBits F).length + k * (2 * (SourceEncoding.inputBits F).length + 6) + 1) := by
  have header := MachineAddressHeaders.inPolynomialTime
    (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
    (AddressMachineProgram.headerLabels k T) (some (AddressMachineProgram.initializeStart k T))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atHeader k T)
    (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)) F
    (AddressMachineProgram.inputTapes_source k T _) (input_headerClean k T F)
    (AddressMachineSpace.initialState k).1.1 none
  have digits := MachineOdometerInit.initializeInTime
    (AddressMachineSpace.odometerSlots k s d T.vectors.length)
    (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    (AddressMachineProgram.initializeLabels k T) (some (AddressMachineProgram.bodyStart k T))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atInitialize k T)
    F.equations.length (List.length_pos_iff.mpr F.nonempty) (afterHeaders k T F)
    (afterHeaders_occurrences k T F) (afterHeaders_current k T F)
    (afterHeaders_remaining k T F) (afterHeaders_copyScratch k T F)
    (AddressMachineSpace.initialState k).1
  have run := StateTransition.EvalsToInTime.trans (AddressMachineProgram.machine k T).step
    _ _ _ _ _ header digits
  refine { steps := run.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · rw [AddressMachineProgram.initList_eq]
    exact run.evals_in_steps
  · apply Nat.le_trans run.steps_le_m
    have hm := SourceEncoding.inputBits_length_ge_equations F
    have hmul := Nat.mul_le_mul_left k (show 2 * F.equations.length + 6 ≤
      2 * (SourceEncoding.inputBits F).length + 6 by omega)
    omega

def timePolynomial : Polynomial Nat :=
  MachineAddressHeaders.timePolynomial k s d T.vectors.length +
    Polynomial.C k * (Polynomial.C 2 * Polynomial.X + Polynomial.C 6) + Polynomial.C 1

theorem timePolynomial_eval (N : Nat) :
    (timePolynomial k T).eval N =
      (MachineAddressHeaders.timePolynomial k s d T.vectors.length).eval N +
        k * (2 * N + 6) + 1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

def inPolynomialTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits F))
      (some ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k,
        initialized k T F⟩)
      ((timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  rw [timePolynomial_eval]
  exact inTime k T F

end
end UniqueGamesTheorem.Reduction.AddressMachineInitial

end OAI
