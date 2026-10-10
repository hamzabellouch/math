import OAI.Computability.UniqueGames.Reduction.AddressMachineInitial
import OAI.Computability.UniqueGames.Reduction.AddressOutputSize
import OAI.Computability.UniqueGames.Reduction.AddressTuplePolynomialLemmas
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas

namespace OAI


namespace UniqueGamesTheorem.Reduction.AddressMachineLoop

open Turing Foundations.Complexity Integration


noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

def bits (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) : List Bool :=
  AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T
    (OccurrenceTupleOrder.readCoordinates digits)

def stateTapes (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    AddressMachineProgram.Tape k T → List Bool :=
  AddressOdometerSchedule.setDigits F.equations.length (fun j => (digits j).val)
    (AddressOdometerSchedule.setAcc (AddressMachineInitial.initialized k T F) output)

theorem stateTapes_frame (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (tape : AddressMachineProgram.Tape k T)
    (hc : ∀j, tape ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀j, tape ≠ AddressMachineSpace.remaining k s d T.vectors.length j)
    (ha : tape ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    stateTapes k T F digits output tape = AddressMachineInitial.initialized k T F tape := by
  rw [stateTapes, AddressOdometerSchedule.setDigits_other _ _ _ tape hc hr]
  exact AddressOdometerSchedule.setAcc_other _ _ tape ha

@[simp] theorem stateTapes_savedIndex (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) (j : Fin k) :
    stateTapes k T F digits output (.savedIndex j) = encodeWord (digits j.rev).val := by
  exact AddressOdometerSchedule.setDigits_savedIndex _ _ _ j

@[simp] theorem stateTapes_private (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (tape : MachineTemplateAddress.Tape (4*k) (1+9*k)) :
    stateTapes k T F digits output (AddressMachineSpace.privateAddress k s d T.vectors.length tape) = [] := by
  rw [stateTapes_frame]
  · exact AddressMachineInitial.initialized_privateAddress k T F tape
  all_goals simp [AddressMachineSpace.privateAddress, AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

@[simp] theorem stateTapes_header (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (c : MachineAddressHeaders.Arithmetic.Control) (hc : c ≠ .reversed) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length c) =
      AddressMachineInitial.initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) := by
  apply stateTapes_frame
  · exact AddressMachineSpace.headerTape_ne_current k s d T.vectors.length c
  · exact AddressMachineSpace.headerTape_ne_remaining k s d T.vectors.length c
  · intro h
    exact hc ((AddressMachineSpace.headerTape_eq_iff k s d T.vectors.length c .reversed).mp h)

theorem stateTapes_ready (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    AddressTupleBody.Ready F (OccurrenceTupleOrder.readCoordinates digits)
      (stateTapes k T F digits output) := by
  constructor
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_source k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j
    exact stateTapes_savedIndex k T F digits output j
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_index k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_work k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_scratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_copyScratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j slot
    rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_field k T F j slot
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

theorem stateTapes_clean (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) := by
  constructor
  · constructor
    · exact stateTapes_private k T F digits output .reversed
    · exact stateTapes_private k T F digits output .forward
    · exact stateTapes_private k T F digits output .copyScratch
    · exact stateTapes_private k T F digits output .accA
    · exact stateTapes_private k T F digits output .accB
    · exact stateTapes_private k T F digits output .counter
    · exact stateTapes_private k T F digits output .hornerScratch
    · intro j; exact stateTapes_private k T F digits output (.digit j)
  · exact stateTapes_private k T F digits output .output

theorem stateTapes_base (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (CanonicalAddress.base F.variables F.equations.length s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_base]
  congr 1
  simp [MachineAddressHeaders.radix, MachineAddressHeaders.baseConstant,
    CanonicalAddress.base_eq, Nat.add_assoc]

theorem stateTapes_capacity (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (AddressGame.bodyCapacity (AddressTupleBody.source F) k s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_capacity]
  congr 1
  change MachineAddressHeaders.capacity k s d F.variables F.equations.length =
    CanonicalAddress.capacity F.variables F.equations.length k s d
  simp [MachineAddressHeaders.capacity, MachineAddressHeaders.radix,
    MachineAddressHeaders.baseConstant, CanonicalAddress.capacity,
    CanonicalAddress.base_eq, Nat.add_assoc]

/-- Appending actual tuple bytes is exactly the schedule's accumulator update. -/
theorem appended_stateTapes (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output payload : List Bool) :
    MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) payload =
      stateTapes k T F digits (payload.reverse ++ output) := by
  change AddressOdometerSchedule.setAcc (stateTapes k T F digits output)
    (payload.reverse ++ stateTapes k T F digits output
      (AddressOdometerSchedule.accumulator k s d T.vectors.length)) = _
  simp only [stateTapes, AddressOdometerSchedule.setDigits_accumulator, AddressOdometerSchedule.setAcc_apply]
  rw [AddressOdometerSchedule.setDigits_setAcc, AddressOdometerSchedule.setAcc_setAcc,
    ← AddressOdometerSchedule.setDigits_setAcc]

/-- The local-body premise of the odometer theorem is derived from the actual
placed tuple-body implementation and its actual uniform budget theorem. -/
theorem bodyTrace (F : SourceEncoding.Input) :
    AddressOdometerSchedule.BodyTrace (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F)
      (bits k T F) ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  intro digits output
  let base := stateTapes k T F digits output
  have ready := stateTapes_ready k T F digits output
  have clean := stateTapes_clean k T F digits output
  have actual := AddressTuplePolynomial.run_actual T (AddressMachineProgram.bodyLabels k T) (some (AddressMachineProgram.next k T 0))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atBody k T) F
    (OccurrenceTupleOrder.readCoordinates digits) base ready clean (fun _ => false)
    (stateTapes_base k T F digits output) (stateTapes_capacity k T F digits output)
  refine ⟨actual.steps, actual.steps_le_m, ?_⟩
  have hemit : MachineAddressEdge.appended (AddressTupleBody.Slots k s d T.vectors.length)
      base (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T
        (OccurrenceTupleOrder.readCoordinates digits)) =
      stateTapes k T F digits ((bits k T F digits).reverse ++ output) :=
    appended_stateTapes k T F digits output _
  exact actual.evals_in_steps.trans (congrArg
    (fun tapes => some (AddressOdometerSchedule.configuration
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 tapes)) hemit)

/-- The all-zero assignment is already physically present after initialization. -/
theorem setDigits_initialized_zero (F : SourceEncoding.Input) :
    AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
      (AddressMachineInitial.initialized k T F) = AddressMachineInitial.initialized k T F := by
  funext tape
  cases tape with
  | savedIndex j =>
    rw [AddressOdometerSchedule.setDigits_savedIndex, AddressMachineInitial.initialized_savedIndex]
  | extra e =>
    rcases e with e | e
    · rfl
    · rcases e with e | e
      · rfl
      · rcases e with j | e
        · change AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
            (AddressMachineInitial.initialized k T F) (AddressOdometerSchedule.remaining k s d T.vectors.length j) = _
          simp only [AddressOdometerSchedule.setDigits_remaining, Fin.isLt, dite_eq_left, Nat.sub_zero]
          exact (AddressMachineInitial.initialized_remaining k T F j).symm
        · rfl
  | _ => rfl

def finalTapes (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  (AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
    (AddressMachineInitial.initialized k T F) (bits k T F)).stk

/-- Actual complete tuple traversal, before the final output reversal. -/
def traversal (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      (((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length + 2*k) *
        F.equations.length^k) := by
  have actual := AddressOdometerSchedule.traversalInTime (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
    (AddressMachineProgram.next k T) (AddressMachineProgram.resetAt k T) (AddressMachineSpace.initialState k).1
    (List.length_pos_iff.mpr F.nonempty)
    ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length)
    (AddressMachineInitial.initialized k T F) (bits k T F)
    (by
      intro i hi
      simp only [AddressMachineProgram.next_lt k T i hi, AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atCheck k T ⟨i,hi⟩)
    (by
      intro i hi
      simp only [AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atReset k T ⟨i,hi⟩)
    (bodyTrace k T F)
  have run := Classical.choice actual
  have hstart : AddressOdometerSchedule.initialConfiguration (m := F.equations.length) k
      (AddressMachineProgram.bodyStart k T) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F) =
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩ := by
    simp only [AddressOdometerSchedule.initialConfiguration, AddressOdometerSchedule.configuration,
      setDigits_initialized_zero, AddressMachineSpace.initialState]
  have hfinish : AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
      (AddressMachineInitial.initialized k T F) (bits k T F) =
      ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩ := by
    simp only [AddressOdometerSchedule.finalConfiguration, AddressOdometerSchedule.configuration, finalTapes,
      AddressMachineProgram.next_ge k T k (Nat.le_refl _), AddressMachineSpace.initialState]
  rw [hstart, hfinish] at run
  exact run

/-- Exact output order, including repeated constraints and the original header. -/
theorem allBits_eq (F : SourceEncoding.Input) :
    AddressOdometerSchedule.allBits (bits k T F) =
      (FixedOutcomes.occurrenceTuples F.equations.length k).flatMap
        (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T) := by
  exact (OccurrenceTupleOrder.functions_flatMap F.equations.length k _).symm

@[simp] theorem final_reversed (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      ((FixedOutcomes.occurrenceTuples F.equations.length k).flatMap
        (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T)).reverse ++
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.variables F.equations.length).reverse := by
  change (AddressOdometerSchedule.finalConfiguration _ _ _ _).stk (AddressOdometerSchedule.accumulator _ _ _ _) = _
  rw [AddressOdometerSchedule.final_accumulator]
  change (AddressOdometerSchedule.allBits (bits k T F)).reverse ++ _ = _
  rw [allBits_eq]
  congr 1
  exact AddressMachineInitial.initialized_reversed k T F

/-- The actual header machine emits exactly the target instance's three headers. -/
theorem headerBits_eq (F : SourceEncoding.Input) :
    MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
      F.variables F.equations.length =
      encodeWords [(AddressGame.tableOutput (AddressTupleBody.source F) k T).vertices, 2^s,
        (AddressGame.tableOutput (AddressTupleBody.source F) k T).constraints.length] := by
  have hcap : MachineAddressHeaders.capacity k s d F.variables F.equations.length =
      AddressGame.bodyCapacity (AddressTupleBody.source F) k s d := by
    change MachineAddressHeaders.capacity k s d F.variables F.equations.length =
      CanonicalAddress.capacity F.variables F.equations.length k s d
    simp [MachineAddressHeaders.capacity, MachineAddressHeaders.radix,
      MachineAddressHeaders.baseConstant, CanonicalAddress.capacity,
      CanonicalAddress.base_eq, Nat.add_assoc]
  have hedge : MachineAddressHeaders.edgeCount k s d T.vectors.length F.equations.length =
      (AddressGame.tableOutput (AddressTupleBody.source F) k T).constraints.length := by
    rw [AddressOutputSize.table_constraints_eq]
    change MachineAddressHeaders.edgeCount k s d T.vectors.length F.equations.length =
      Explicit.edgeCount F.equations.length k (s+d) T.vectors.length
    unfold MachineAddressHeaders.edgeCount MachineAddressHeaders.edgeFactor Explicit.edgeCount
    ring
  rw [MachineAddressHeaders.Arithmetic.headerBits, hcap, hedge]
  rfl

/-- The final reversed tape is exactly the complete encoded actual instance. -/
theorem final_accumulator (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineProgram.accumulator k T) =
      (gameBits (AddressGame.tableOutput (AddressTupleBody.source F) k T)).reverse := by
  rw [AddressOutcomeSpecs.gameBits_factor, ← headerBits_eq k T F, List.reverse_append]
  exact final_reversed k T F

theorem final_other (F : SourceEncoding.Input) (tape : AddressMachineProgram.Tape k T)
    (hc : ∀j, tape ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀j, tape ≠ AddressMachineSpace.remaining k s d T.vectors.length j)
    (ha : tape ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    finalTapes k T F tape = AddressMachineInitial.initialized k T F tape :=
  AddressOdometerSchedule.final_other _ _ _ _ tape hc hr ha

@[simp] theorem final_outputEmpty (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineProgram.output k T) = [] := by
  rw [final_other]
  · exact AddressMachineInitial.initialized_finalOutput k T F
  · intro j
    exact Ne.symm (AddressMachineSpace.current_ne_finalOutput k s d T.vectors.length j)
  · intro j
    exact Ne.symm (AddressMachineSpace.remaining_ne_finalOutput k s d T.vectors.length j)
  · exact Ne.symm (AddressMachineSpace.headerTape_ne_finalOutput k s d T.vectors.length .reversed)

@[simp] theorem final_current (F : SourceEncoding.Input) (j : Fin k) :
    finalTapes k T F (AddressMachineSpace.current k s d T.vectors.length j) = encodeWord 0 :=
  AddressOdometerSchedule.final_current _ _ _ _ j

@[simp] theorem final_remaining (F : SourceEncoding.Input) (j : Fin k) :
    finalTapes k T F (AddressMachineSpace.remaining k s d T.vectors.length j) =
      encodeWord (F.equations.length-1) :=
  AddressOdometerSchedule.final_remaining _ _ _ _ j

/-- The exponent and coefficients depend only on fixed reduction parameters. -/
def timePolynomial : Polynomial Nat :=
  (AddressTupleBudget.timePolynomial k T + Polynomial.C (2*k)) * Polynomial.X^k

@[simp] theorem timePolynomial_eval (N : Nat) :
    (timePolynomial k T).eval N = ((AddressTupleBudget.timePolynomial k T).eval N + 2*k)*N^k := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

def inPolynomialTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      ((timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have run := traversal k T F
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  rw [timePolynomial_eval]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (SourceEncoding.inputBits_length_ge_equations F) k)

end
end UniqueGamesTheorem.Reduction.AddressMachineLoop



/-!
# The complete addressed outer-reduction machine

The fixed finite machine reads an encoded nonempty E3LIN occurrence list and
writes the exact encoded addressed Unique Games instance. Its execution covers
all headers, all occurrence tuples, every fixed noise/coefficient outcome,
every permutation image, reversal, and complete tape cleanup.
-/

namespace UniqueGamesTheorem.Reduction.MachineAddressGame

open Turing Foundations.Complexity


noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def output (input : SourceEncoding.Input) : Foundations.Target.Instance (2 ^ s) :=
  AddressGame.tableOutput
    (ActualSource.Source.ofList input.equations input.nonempty) k T

def prefixPolynomial : Polynomial Nat :=
  AddressMachineInitial.timePolynomial k T + AddressMachineLoop.timePolynomial k T

def timePolynomial : Polynomial Nat :=
  AddressMachineFinish.timePolynomial k T (prefixPolynomial k T)

/-- The complete actual prefix, with both initialization and every tuple body
supplied by their constructed finite programs. -/
def prefixInTime (input : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input))
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k,
        AddressMachineLoop.finalTapes k T input⟩)
      ((prefixPolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let initial := AddressMachineInitial.inPolynomialTime k T input
  let loop := AddressMachineLoop.inPolynomialTime k T input
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initial loop
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm] using run.steps_le_m

/-- Literal `initList` to literal `haltList`, including all private tape and
finite-state cleanup. This theorem has no runtime premise. -/
def fullRunInTime (input : SourceEncoding.Input) :
    TM2OutputsInTime (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input)
      (some (gameBits (output k T input)))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let run := AddressMachineFinish.completePrefix k T (SourceEncoding.inputBits input)
    (prefixPolynomial k T) (AddressMachineLoop.finalTapes k T input)
    (prefixInTime k T input) (AddressMachineLoop.final_outputEmpty k T input)
  simpa only [AddressMachineLoop.final_accumulator, List.reverse_reverse, output,
    Integration.AddressTupleBody.source, timePolynomial] using run

def computableInPolyTime :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) where
  tm := AddressMachineProgram.machine k T
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial k T
  outputsFun input := by
    change TM2OutputsInTime (AddressMachineProgram.machine k T)
      ((SourceEncoding.inputBits input).map id)
      (some ((gameBits (output k T input)).map id))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length)
    have input_eq : @List.map
        ((AddressMachineProgram.machine k T).Γ (AddressMachineProgram.machine k T).k₀)
        ((AddressMachineProgram.machine k T).Γ (AddressMachineProgram.machine k T).k₀)
        id (SourceEncoding.inputBits input) = SourceEncoding.inputBits input := List.map_id _
    have output_eq : @List.map
        ((AddressMachineProgram.machine k T).Γ (AddressMachineProgram.machine k T).k₁)
        ((AddressMachineProgram.machine k T).Γ (AddressMachineProgram.machine k T).k₁)
        id (gameBits (output k T input)) = gameBits (output k T input) := List.map_id _
    erw [input_eq, output_eq]
    exact fullRunInTime k T input

/-- Every working tape of the actual certificate uses the finite Bool alphabet. -/
theorem workAlphabetFinite (tape : (computableInPolyTime k T).tm.K) :
    Finite ((computableInPolyTime k T).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end
end UniqueGamesTheorem.Reduction.MachineAddressGame

end OAI
