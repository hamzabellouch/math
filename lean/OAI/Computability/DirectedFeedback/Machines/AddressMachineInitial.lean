import Mathlib
import OAI.Computability.DirectedFeedback.Games.AddressTupleBody

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

namespace DFVSGames.Reduction.AddressMachineInitial

open Turing DFVSGames.Foundations.Complexity

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def afterHeaders (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineAddressHeaders.resultTapes (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
    (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F))
    F.«variables» F.equations.length

def initialized (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineOdometerInit.stageTapes (AddressMachineSpace.odometerSlots k s d T.vectors.length)
    F.equations.length (afterHeaders k T F) k

private theorem input_header_inline_AddressMachineInitial (F : SourceEncoding.Input)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
      (AddressMachineSpace.headerTape k s d T.vectors.length c) = [] := by
  apply AddressMachineProgram.inputTapes_other
  simp [AddressMachineSpace.headerTape]

theorem input_headerClean (F : SourceEncoding.Input) :
    MachineAddressHeaders.Clean (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)) := by
  refine {
    accA := input_header_inline_AddressMachineInitial k T F .accA
    accB := input_header_inline_AddressMachineInitial k T F .accB
    counter := input_header_inline_AddressMachineInitial k T F .counter
    scratch := input_header_inline_AddressMachineInitial k T F .scratch
    coefficients := ?_
    baseValue := input_header_inline_AddressMachineInitial k T F .baseValue
    capacity := input_header_inline_AddressMachineInitial k T F .capacity
    temporary := input_header_inline_AddressMachineInitial k T F .temporary
    readCopy := ?_
    variableCount := input_header_inline_AddressMachineInitial k T F .variableCount
    occurrenceCount := input_header_inline_AddressMachineInitial k T F .occurrenceCount }
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
  exact (MachineAddressHeaders.resultTapes_source _ _ F.«variables» F.equations.length).trans
    (AddressMachineProgram.inputTapes_source k T _)

@[simp] theorem afterHeaders_variables (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) =
      encodeWord F.«variables» := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .variableCount) = _
  rw [MachineAddressHeaders.resultTapes_n]
  change encodeWord F.«variables» ++ AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
    (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) = _
  rw [input_header_inline_AddressMachineInitial, List.append_nil]

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
  rw [input_header_inline_AddressMachineInitial, List.append_nil]

@[simp] theorem afterHeaders_base (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.«variables» F.equations.length) :=
  MachineAddressHeaders.resultTapes_base _ _ _ _

@[simp] theorem afterHeaders_capacity (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.«variables» F.equations.length) :=
  MachineAddressHeaders.resultTapes_capacity _ _ _ _

@[simp] theorem afterHeaders_reversed (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.«variables» F.equations.length).reverse := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .reversed) = _
  rw [MachineAddressHeaders.resultTapes_reversed]
  change (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
    F.«variables» F.equations.length).reverse ++ AddressMachineProgram.inputTapes k T
      (SourceEncoding.inputBits F) (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) = _
  rw [input_header_inline_AddressMachineInitial, List.append_nil]

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
      encodeWord F.«variables» := by rw [initialized_header, afterHeaders_variables]
@[simp] theorem initialized_occurrences (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) =
      encodeWord F.equations.length := by rw [initialized_header, afterHeaders_occurrences]
@[simp] theorem initialized_base (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.«variables» F.equations.length) := by
  rw [initialized_header, afterHeaders_base]
@[simp] theorem initialized_capacity (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.«variables» F.equations.length) := by
  rw [initialized_header, afterHeaders_capacity]
@[simp] theorem initialized_reversed (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.«variables» F.equations.length).reverse := by
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
end DFVSGames.Reduction.AddressMachineInitial
end

section

namespace DFVSGames.Reduction.OccurrenceTupleOrder

open Turing
open DFVSGames.Foundations.Complexity
open MachineTupleOdometer

variable {α : Type*}

def readCoordinates {m k : Nat} (digits : Fin k → Fin m) : Fin k → Fin m :=
  digits ∘ Fin.rev

@[simp] theorem readCoordinates_apply {m k : Nat} (digits : Fin k → Fin m) (j : Fin k) :
    readCoordinates digits j = digits j.rev := rfl

@[simp] theorem readCoordinates_involutive {m k : Nat} (digits : Fin k → Fin m) :
    readCoordinates (readCoordinates digits) = digits := by
  funext j
  simp only [readCoordinates_apply, Fin.rev_rev]

def coordinateEquiv (m k : Nat) : (Fin k → Fin m) ≃ (Fin k → Fin m) where
  toFun := readCoordinates
  invFun := readCoordinates
  left_inv := readCoordinates_involutive
  right_inv := readCoordinates_involutive

theorem readCoordinates_snoc {m k : Nat} (tail : Fin k → Fin m) (d : Fin m) :
    readCoordinates (Fin.snoc tail d) = Fin.cons d (readCoordinates tail) :=
  Fin.snoc_comp_rev d tail

theorem tupleOrder_readCoordinates (m k : Nat) :
    (MachineTupleOdometer.tupleOrder m k).map readCoordinates =
      ActualEnumeration.functions (List.finRange m) k := by
  induction k with
  | zero =>
    rw [MachineTupleOdometer.tupleOrder_dimension_zero]
    change [readCoordinates (fun i : Fin 0 => Fin.elim0 i)] = [Fin.elim0]
    congr 1
  | succ k ih =>
    have each (d : Fin m) :
        ((MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d)).map
          readCoordinates =
        (ActualEnumeration.functions (List.finRange m) k).map (Fin.cons d) := by
      calc
        _ = ((MachineTupleOdometer.tupleOrder m k).map readCoordinates).map (Fin.cons d) := by
          simp only [List.map_map, Function.comp_def, readCoordinates_snoc]
        _ = _ := by rw [ih]
    rw [MachineTupleOdometer.tupleOrder_snoc]
    change ((List.finRange m).flatMap (fun d =>
      (MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d))).map
      readCoordinates = _
    simp only [List.map_flatMap, each]
    simp only [ActualEnumeration.functions, Explicit.pairs, List.map_flatMap,
      List.map_map, Function.comp_def]

theorem functions_readCoordinates (m k : Nat) :
    (ActualEnumeration.functions (List.finRange m) k).map readCoordinates =
      MachineTupleOdometer.tupleOrder m k := by
  have h := congrArg (List.map readCoordinates) (tupleOrder_readCoordinates m k)
  simpa only [List.map_map, Function.comp_def, readCoordinates_involutive,
    List.map_id_fun', id_eq] using h.symm

theorem functions_flatMap (m k : Nat) (emit : (Fin k → Fin m) → List α) :
    (ActualEnumeration.functions (List.finRange m) k).flatMap emit =
      (MachineTupleOdometer.tupleOrder m k).flatMap
        (fun digits => emit (readCoordinates digits)) := by
  rw [← tupleOrder_readCoordinates]
  exact List.flatMap_map readCoordinates emit _

section ActualSchedule

variable {K Λ σ : Type} [DecidableEq K]
  {m k : Nat} {current remaining : Nat → K} {bodyLabel : Λ}
  {checkLabel resetLabel : Nat → Λ}
  {program : Λ → TM2.Stmt (MachineTupleOdometer.Alphabet (K := K)) Λ (σ × Option Bool)}
  {exitLabel : Λ} {start finish : MachineTupleOdometer.Configuration K Λ σ}

theorem actualSchedule_order
    (tree : MachineTupleOdometer.NestedCycle m current remaining bodyLabel
      checkLabel resetLabel program k exitLabel start finish) :
    tree.order.map readCoordinates = ActualEnumeration.functions (List.finRange m) k := by
  rw [MachineTupleOdometer.NestedCycle.order_eq_tupleOrder, tupleOrder_readCoordinates]

theorem actualSchedule_flatMap
    (tree : MachineTupleOdometer.NestedCycle m current remaining bodyLabel
      checkLabel resetLabel program k exitLabel start finish)
    (emit : (Fin k → Fin m) → List α) :
    (ActualEnumeration.functions (List.finRange m) k).flatMap emit =
      tree.order.flatMap (fun digits => emit (readCoordinates digits)) := by
  rw [MachineTupleOdometer.NestedCycle.order_eq_tupleOrder]
  exact functions_flatMap m k emit

end ActualSchedule

end DFVSGames.Reduction.OccurrenceTupleOrder
end

section

namespace DFVSGames.Integration.AddressTupleBudget

open Reduction Foundations.Complexity
open AddressTupleBody

variable {k s d noiseCount : Nat}

def radixBound (s d L : Nat) : Nat := L + (2^s + 2^d + 4)

def magnitude (k s d L : Nat) : Nat :=
  (L+1) + radixBound s d L + (radixBound s d L)^(1+9*k) +
    (1+9*k)*(radixBound s d L+1) + 1

noncomputable def magnitudePolynomial (k s d : Nat) : Polynomial Nat :=
  (Polynomial.X+1) + (Polynomial.X+Polynomial.C (2^s+2^d+4)) +
    (Polynomial.X+Polynomial.C (2^s+2^d+4))^(1+9*k) +
    Polynomial.C (1+9*k)*(Polynomial.X+Polynomial.C (2^s+2^d+4)+1) + 1

@[simp] theorem magnitudePolynomial_eval (k s d L : Nat) :
    (magnitudePolynomial k s d).eval L = magnitude k s d L := by
  simp only [magnitudePolynomial, magnitude, radixBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]

theorem source_counts_le (F : SourceEncoding.Input) :
    F.«variables»+F.equations.length ≤ (SourceEncoding.inputBits F).length := by
  rw [SourceEncoding.inputBits_length]
  omega

theorem radix_le (F : SourceEncoding.Input) (s d : Nat) :
    CanonicalAddress.base F.«variables» F.equations.length s d ≤
      radixBound s d (SourceEncoding.inputBits F).length := by
  have h := source_counts_le F
  simp only [CanonicalAddress.base_eq, radixBound]
  omega

theorem radix_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    CanonicalAddress.base F.«variables» F.equations.length s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := radix_le F s d
  unfold magnitude
  omega

theorem capacity_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    AddressGame.bodyCapacity (source F) k s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := Nat.pow_le_pow_left (radix_le F s d) (1+9*k)
  change (CanonicalAddress.base F.«variables» F.equations.length s d)^(1+9*k) ≤ _
  unfold magnitude
  omega

theorem field_length_le_magnitude (k s d L : Nat) : L+1 ≤ magnitude k s d L := by
  unfold magnitude
  omega

theorem canonicalValues_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    AddressTupleLoaded.canonicalValues F tuple j slot ≤
      (SourceEncoding.inputBits F).length := by
  rw [canonicalValues_eq_actual]
  unfold CanonicalBodyTemplate.sourceFields CanonicalBodyTemplate.recordFields
  split_ifs with h
  · have hname := (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).isLt
    have hvars := SourceEncoding.inputBits_length_ge_variables F
    change _ < F.«variables» at hname
    change (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).val ≤
      (SourceEncoding.inputBits F).length
    exact (Nat.le_of_lt hname).trans hvars
  · have hocc := (tuple j).isLt
    have hcount := SourceEncoding.inputBits_length_ge_equations F
    omega

theorem loaded_fields_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (i : Fin (4*k)) :
    ((loaded F tuple base) (MachineAddressEdge.addressSlots
      (Slots k s d noiseCount) (.field i))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have fields := AddressTupleLoaded.loaded_savedFields F tuple base ready.saved ready.fields
  have atField := congrFun fields i
  change loaded F tuple base (MachineAddressEdge.addressSlots
    (Slots k s d noiseCount) (.field i)) = _ at atField
  rw [atField]
  simp only [CanonicalBodyMachine.savedFields, encodeWord_length]
  exact (Nat.add_le_add_right (canonicalValues_le F tuple _ _) 1).trans
    (field_length_le_magnitude k s d _)

theorem queryWords_lt_radix (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (w : Nat) (hw : w ∈ AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) :
    w < CanonicalAddress.base F.«variables» F.equations.length s d := by
  rw [canonicalValues_eq_actual, rhs_eq_actual] at hw
  change w ∈ AddressByteSemantics.queryWords
    (CanonicalBodyTemplate.sourceFields (m := (source F).occurrences) tuple
      (ActualGame.names (source F))) X (fun j => ActualGame.rhs (source F) (tuple j)) at hw
  rw [AddressByteSemantics.queryWords_actual (source F) (tuple,X)] at hw
  exact CanonicalAddress.bodyWords_lt_base _ w hw

theorem queryWords_encoded_length_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d) :
    (encodeWords (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hwords := encodeWords_length_le
    (AddressByteSemantics.queryWords (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))
    (radixBound s d (SourceEncoding.inputBits F).length)
    (fun w hw => (Nat.le_of_lt (queryWords_lt_radix F tuple X w hw)).trans (radix_le F s d))
  rw [AddressByteSemantics.queryWords_length] at hwords
  unfold magnitude
  omega

theorem queryWords_digits_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (i : Nat) (hi : i < 1+9*k) :
    MachineTemplateAddress.digits (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) i ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hi' : i < (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))).length := by
    simpa only [AddressByteSemantics.queryWords_length] using hi
  simp only [MachineTemplateAddress.digits, List.getElem?_eq_getElem hi', Option.getD_some]
  exact (Nat.le_of_lt (queryWords_lt_radix F tuple X _ (List.getElem_mem hi'))).trans
    (radix_le_magnitude F k s d)

theorem selected_values_bound (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d) :
    ∀ row ∈ MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple),
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) := by
  rw [AddressOutcomeSpecs.selected_rows]
  intro row member
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
  simp only [AddressOutcomeSpecs.values_row_left, AddressOutcomeSpecs.values_row_right]
  exact ⟨queryWords_encoded_length_le_magnitude F tuple p.1,
    queryWords_encoded_length_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p),
    queryWords_digits_le_magnitude F tuple p.1,
    queryWords_digits_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p)⟩

noncomputable def rowPolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  Polynomial.C (2^((2*k+1)*(s+d+1))*T.vectors.length) *
    MachineAddressEdge.timePolynomial (1+9*k) (1+9*k) (1+9*k) + 1

private theorem eval_sum_constant_inline_AddressTupleBudget {α : Type} (items : List α) (p : Polynomial Nat) (M : Nat) :
    ((items.map (fun _ => p)).sum).eval M = items.length*p.eval M := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [List.map_cons, List.sum_cons, Polynomial.eval_add, List.length_cons,
      Nat.add_mul, Nat.one_mul, ih]
    omega

theorem selected_polynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (b : Fin k → Bool) (M : Nat) :
    (MachineOutcomeRows.timePolynomial
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) b)).eval M =
        (rowPolynomial k T).eval M := by
  simp only [MachineOutcomeRows.timePolynomial, AddressOutcomeSpecs.selected_rows,
    List.map_map, Function.comp_def, AddressOutcomeSpecs.row_left_length,
    AddressOutcomeSpecs.row_right_length, Polynomial.eval_add, Polynomial.eval_one,
    eval_sum_constant_inline_AddressTupleBudget, FixedOutcomes.tableParams_length, rowPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem rows_budget_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    (MachineOutcomeRows.rowCosts (Slots k s d noiseCount)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
      (loaded F tuple base)).sum+1 ≤
        (rowPolynomial k T).eval (magnitude k s d (SourceEncoding.inputBits F).length) := by
  have h := MachineOutcomeRows.phaseCost_le_timePolynomial (Slots k s d noiseCount)
    (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
    (loaded F tuple base) _ _
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
    (magnitude k s d (SourceEncoding.inputBits F).length)
    (AddressTupleLoaded.loaded_clean F tuple base clean)
    (loaded_fields_le_magnitude F tuple base ready)
    (radix_le_magnitude F k s d) (capacity_le_magnitude F k s d)
    (selected_values_bound F tuple T)
  simpa only [selected_polynomial_eval] using h

theorem physicalField_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) ≤
      (SourceEncoding.inputBits F).length := by
  have hv := SourceEncoding.inputBits_length_ge_variables F
  have hl := SourceEncoding.inputBits_length F
  have h₁ := F.equations[(tuple j).val].first.isLt
  have h₂ := F.equations[(tuple j).val].second.isLt
  have h₃ := F.equations[(tuple j).val].third.isLt
  fin_cases slot <;>
    simp only [SourceEncoding.equationWords, List.getElem_cons_zero,
      List.getElem_cons_succ] <;> (try split_ifs) <;> omega

private theorem lengthSum_le_of_mem_inline_AddressTupleBudget {K : Type} [DecidableEq K]
    (chosen : List K) (base : K → List Bool) (M : Nat)
    (bounded : ∀ tape ∈ chosen, (base tape).length ≤ M) :
    MachineDrainMany.lengthSum chosen base ≤ chosen.length*M := by
  induction chosen with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons tape chosen ih =>
    have first := bounded tape (by simp)
    have rest := ih (fun t ht => bounded t (List.mem_cons_of_mem tape ht))
    simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
      List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

theorem cleanup_budget_le (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base) :
    AddressTupleCleanup.budget k s d noiseCount (emitted rows B C values F tuple base) ≤
      4*k*((SourceEncoding.inputBits F).length+2) := by
  have h := lengthSum_le_of_mem_inline_AddressTupleBudget (AddressTupleCleanup.loadedFields k s d noiseCount)
    (emitted rows B C values F tuple base) ((SourceEncoding.inputBits F).length+1) (by
      intro tape member
      obtain ⟨j, slot, rfl⟩ :=
        (AddressTupleCleanup.mem_loadedFields k s d noiseCount tape).mp member
      rw [emitted, MachineAddressEdge.appended_other]
      · rw [loaded, AddressTupleLoaded.loaded_field F tuple base ready.fields, encodeWord_length]
        exact Nat.add_le_add_right (physicalField_le F tuple j slot) 1
      · rw [AddressMachineSpace.addressSlots_output]
        simp [AddressMachineSpace.headerTape])
  rw [AddressTupleCleanup.loadedFields_length] at h
  change MachineDrainMany.lengthSum _ _ + 4*k ≤ _
  calc
    _ ≤ 4*k*((SourceEncoding.inputBits F).length+1)+4*k := Nat.add_le_add_right h _
    _ = 4*k*((SourceEncoding.inputBits F).length+2) := by ring

noncomputable def timePolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  (Polynomial.C k*(Polynomial.C 10*Polynomial.X+Polynomial.C 20)+1)+1+
    (rowPolynomial k T).comp (magnitudePolynomial k s d)+
    Polynomial.C (4*k)*(Polynomial.X+Polynomial.C 2)+1

theorem timePolynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) (L : Nat) :
    (timePolynomial k T).eval L =
      (k*(10*L+20)+1)+1+(rowPolynomial k T).eval (magnitude k s d L)+4*k*(L+2)+1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, magnitudePolynomial_eval]

theorem budget_le_timePolynomial (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    AddressTupleBody.budget (AddressOutcomeSpecs.rows k T)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ≤
        (timePolynomial k T).eval (SourceEncoding.inputBits F).length := by
  have rowsBound := rows_budget_le F tuple T base ready clean
  have cleanupBound := cleanup_budget_le (AddressOutcomeSpecs.rows k T)
    (CanonicalAddress.base F.«variables» F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d)
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ready
  rw [AddressTupleBody.budget, timePolynomial_eval]
  omega

end DFVSGames.Integration.AddressTupleBudget
end

section

namespace DFVSGames.Integration.AddressTuplePolynomial

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
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d))
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
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d))
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

end DFVSGames.Integration.AddressTuplePolynomial
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
