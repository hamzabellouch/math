import OAI.Computability.PerfectCompleteness.Machines.CircuitLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.CircuitEmission

open Turing
open UniqueGamesTheorem.Reduction
open CircuitProducerModel

theorem contextSource_ne_scratch (context : Context) :
    contextSource context ≠ Tape.scratch := by
  cases context with
  | header slot => simp only [contextSource]; split <;> simp
  | gate tag position => simp [contextSource]
  | output position => simp [contextSource]

theorem contextSource_ne_reversed (context : Context) :
    contextSource context ≠ Tape.reversed := by
  cases context with
  | header slot => simp only [contextSource]; split <;> simp
  | gate tag position => simp [contextSource]
  | output position => simp [contextSource]

def contextOutput (context : Context) (base : Tape → List Bool) : List Bool :=
  MachineTransducer.output (fun control _ => control) emission
    context (base (contextSource context))

def contextSteps (context : Context) (base : Tape → List Bool) : Nat :=
  3 * (base (contextSource context)).length + 3

def contextTapes (context : Context) (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .reversed ((contextOutput context base).reverse ++ base .reversed)

@[simp] theorem contextTapes_other (context : Context) (base : Tape → List Bool)
    (tape : Tape) (different : tape ≠ .reversed) :
    contextTapes context base tape = base tape := by
  simp [contextTapes, different]

@[simp] theorem contextTapes_source (context other : Context) (base : Tape → List Bool) :
    contextTapes context base (contextSource other) = base (contextSource other) :=
  contextTapes_other context base _ (contextSource_ne_reversed other)

@[simp] theorem contextTapes_scratch (context : Context) (base : Tape → List Bool) :
    contextTapes context base .scratch = base .scratch :=
  contextTapes_other context base _ (by decide)

@[simp] theorem contextOutput_update (context : Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextOutput context (Function.update base .reversed out) = contextOutput context base := by
  simp [contextOutput, contextSource_ne_reversed]

@[simp] theorem contextSteps_update (context : Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextSteps context (Function.update base .reversed out) = contextSteps context base := by
  simp [contextSteps, contextSource_ne_reversed]

theorem setupStep (context : Context) (base : Tape → List Bool) (state : State) :
    TM2.step program ⟨some (.setup context), state, base⟩ =
      some ⟨some (.scan context), (((), context), none), base⟩ := rfl

theorem contextTrace (context : Context) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[contextSteps context base]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState, contextTapes context base⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (contextSource context) Tape.scratch Tape.reversed
    (contextSource_ne_scratch context) (contextSource_ne_reversed context) (by decide)
    defaultControl (fun control _ => control) emission
    (.scan context) (.restore context) (fun control symbol => .emit context control symbol)
    (contextNext context) program rfl (by intros; rfl) rfl base scratchEmpty () context none
  rw [contextSteps, show 3 * (base (contextSource context)).length + 3 =
      (3 * (base (contextSource context)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[
    3 * (base (contextSource context)).length + 2]
    (TM2.step program ⟨some (.setup context), state, base⟩) = _
  rw [setupStep]
  exact copied

def contextInTime (context : Context) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup context), state, base⟩
      (some ⟨contextNext context, initialState, contextTapes context base⟩)
      (contextSteps context base) where
  steps := contextSteps context base
  evals_in_steps := contextTrace context base scratchEmpty state
  steps_le_m := Nat.le_refl _

theorem output_eq_flatMap (context : Context) (input : List Bool) :
    MachineTransducer.output (fun control _ => control) emission context input =
      input.flatMap (emission context) := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

theorem literalEmit_word (positive : Bool) (value : Nat) :
    (encodeWord value).flatMap (literalEmit positive) =
      encodeWords [value, if positive then 1 else 0] := by
  induction value with
  | zero => simp [encodeWord, encodeWords, literalEmit]
  | succ value ih =>
    simpa [encodeWord, encodeWords, List.replicate_succ, literalEmit] using
      congrArg (List.cons true) ih

theorem affineEmit_word (scale offset value : Nat) :
    (encodeWord value).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * value) := by
  have hrep : (List.replicate value true).flatMap (affineEmit scale offset) =
      List.replicate (scale * value) true := by
    rw [List.flatMap_replicate]
    change (List.replicate value (List.replicate scale true)).flatten = _
    rw [List.flatten_replicate_replicate, Nat.mul_comm value scale]
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, hrep, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * value) offset]

def contextWords (context : Context) (value : Nat) : List Nat :=
  match context with
  | .header j => if j.val = 0 then [value] else [3 * value + 1]
  | .gate tag j => [value, if (gateTemplate tag j).2 then 1 else 0]
  | .output _ => [value, 1]

theorem output_word (context : Context) (value : Nat) :
    MachineTransducer.output (fun control _ => control) emission context (encodeWord value) =
      encodeWords (contextWords context value) := by
  rw [output_eq_flatMap]
  cases context with
  | header j =>
    by_cases hj : j.val = 0 <;>
      simp [emission, contextWords, hj, affineEmit_word, encodeWords, Nat.add_comm]
  | gate tag j => exact literalEmit_word (gateTemplate tag j).2 value
  | output j => simpa [emission, contextWords] using literalEmit_word true value

theorem contextTrace_word (context : Context) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State) (value : Nat)
    (cached : base (contextSource context) = encodeWord value) :
    (MachineComposition.advance (TM2.step program))^[3 * (value + 1) + 3]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState,
        Function.update base .reversed
          ((encodeWords (contextWords context value)).reverse ++ base .reversed)⟩ := by
  simpa only [contextSteps, contextTapes, contextOutput, cached, encodeWord_length, output_word]
    using contextTrace context base scratchEmpty state

def contextListOutput (contexts : List Context) (base : Tape → List Bool) : List Bool :=
  contexts.flatMap (fun context => contextOutput context base)

def contextListSteps (contexts : List Context) (base : Tape → List Bool) : Nat :=
  (contexts.map (fun context => contextSteps context base)).sum

def contextListStart (contexts : List Context) (exit : Option Label) : Option Label :=
  match contexts with
  | [] => exit
  | context :: _ => some (.setup context)

def ContextListLinked : List Context → Option Label → Prop
  | [], _ => True
  | context :: rest, exit =>
    contextNext context = contextListStart rest exit ∧ ContextListLinked rest exit

@[simp] theorem contextListOutput_update (contexts : List Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextListOutput contexts (Function.update base .reversed out) = contextListOutput contexts base := by
  simp [contextListOutput]

@[simp] theorem contextListSteps_update (contexts : List Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextListSteps contexts (Function.update base .reversed out) = contextListSteps contexts base := by
  simp [contextListSteps]

private theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

theorem contextListTrace (contexts : List Context) (exit : Option Label)
    (linked : ContextListLinked contexts exit) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (emptyInitial : contexts = [] → state = initialState) :
    (MachineComposition.advance (TM2.step program))^[contextListSteps contexts base]
      (some ⟨contextListStart contexts exit, state, base⟩) =
      some ⟨exit, initialState, Function.update base .reversed
        ((contextListOutput contexts base).reverse ++ base .reversed)⟩ := by
  induction contexts generalizing base state with
  | nil =>
    rw [emptyInitial rfl]
    simp [contextListSteps, contextListOutput, contextListStart]
  | cons context rest ih =>
    let after := contextTapes context base
    have first := contextTrace context base scratchEmpty state
    have second := ih linked.2 after (by simpa [after] using scratchEmpty)
      initialState (by intro _; rfl)
    rw [linked.1] at first
    have combined := chain first second
    simp only [after, contextTapes, contextListSteps_update, contextListOutput_update,
      Function.update_self, Function.update_idem] at combined
    rw [show contextListSteps (context :: rest) base =
        contextListSteps rest base + contextSteps context base by
      simp [contextListSteps, Nat.add_comm]]
    simpa only [contextListStart, contextListOutput, List.flatMap_cons,
      List.reverse_append, List.append_assoc] using combined

def gateContexts (tag : Fin 5) : List Context :=
  (List.finRange 9).map (Context.gate tag)

def outputContexts : List Context := [.output 0, .output 1, .output 2]

theorem gateContexts_linked (tag : Fin 5) :
    ContextListLinked (gateContexts tag) (some (.cleanup 0)) := by
  simp [gateContexts, List.finRange, List.ofFn_succ, ContextListLinked,
    contextListStart, contextNext]

theorem outputContexts_linked :
    ContextListLinked outputContexts (some .finalCounter) := by
  simp [outputContexts, ContextListLinked, contextListStart, contextNext]

theorem contextOutput_gate_word (record : Record) (position : Fin 9)
    (base : Tape → List Bool)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    contextOutput (.gate record.tag position) base = encodeWords
      [record.slot (gateTemplate record.tag position).1,
        if (gateTemplate record.tag position).2 then 1 else 0] := by
  have fields (slot : Fin 3) :
      base (.field ⟨slot.val + 1, by omega⟩) = encodeWord (record.slot slot) := by
    have slotCases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
    rcases slotCases with h | h | h
    · simpa [Record.slot, h] using h1
    · simpa [Record.slot, h] using h2
    · simpa [Record.slot, h] using h3
  unfold contextOutput
  rw [show base (contextSource (.gate record.tag position)) =
      encodeWord (record.slot (gateTemplate record.tag position).1) from fields _]
  exact output_word (.gate record.tag position) _

theorem encodeWords_flatMap {A : Type*} (items : List A) (words : A → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem gateOutput_words (record : Record) (base : Tape → List Bool)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    contextListOutput (gateContexts record.tag) base = record.outputBits := by
  simp only [contextListOutput, gateContexts, List.flatMap_map,
    Record.outputBits, Record.outputWords, templateWords, encodeWords_flatMap]
  congr 1
  funext position
  exact contextOutput_gate_word record position base h1 h2 h3

def gateSteps (record : Record) : Nat :=
  ((List.finRange 9).map fun position =>
    3 * (record.slot (gateTemplate record.tag position).1 + 1) + 3).sum

theorem gateSteps_eq (record : Record) (base : Tape → List Bool)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    contextListSteps (gateContexts record.tag) base = gateSteps record := by
  have fields (slot : Fin 3) :
      base (.field ⟨slot.val + 1, by omega⟩) = encodeWord (record.slot slot) := by
    have slotCases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
    rcases slotCases with h | h | h
    · simpa [Record.slot, h] using h1
    · simpa [Record.slot, h] using h2
    · simpa [Record.slot, h] using h3
  simp only [contextListSteps, gateContexts, List.map_map, gateSteps]
  congr 2
  funext position
  simp only [Function.comp_apply, contextSteps, contextSource, fields, encodeWord_length]

theorem slot_le_sum (record : Record) (slot : Fin 3) :
    record.slot slot ≤ record.output + record.first + record.second := by
  unfold Record.slot
  split <;> omega

private theorem sum_map_le_length_mul {A : Type*} (items : List A)
    (value : A → Nat) (bound : Nat) (bounded : ∀ item ∈ items, value item ≤ bound) :
    (items.map value).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have head := bounded item (by simp)
    have tail := ih (fun a ha => bounded a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem gateSteps_le (record : Record) :
    gateSteps record ≤ 27 * (record.output + record.first + record.second) + 54 := by
  have bound := sum_map_le_length_mul (List.finRange 9)
    (fun position => 3 * (record.slot (gateTemplate record.tag position).1 + 1) + 3)
    (3 * (record.output + record.first + record.second) + 6) (by
      intro position _
      have := slot_le_sum record (gateTemplate record.tag position).1
      omega)
  simp only [List.length_finRange] at bound
  unfold gateSteps
  omega

private theorem length_flatMap_le_length_mul {A : Type*} (items : List A)
    (word : A → List Bool) (bound : Nat) (bounded : ∀ item ∈ items, (word item).length ≤ bound) :
    (items.flatMap word).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have head := bounded item (by simp)
    have tail := ih (fun a ha => bounded a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

theorem outputBits_length_le (record : Record) :
    record.outputBits.length ≤ 9 * (record.output + record.first + record.second) + 27 := by
  have bound := length_flatMap_le_length_mul (List.finRange 9)
    (fun position => encodeWords
      [record.slot (gateTemplate record.tag position).1,
        if (gateTemplate record.tag position).2 then 1 else 0])
    (record.output + record.first + record.second + 3) (by
      intro position _
      have index := slot_le_sum record (gateTemplate record.tag position).1
      have sign : (if (gateTemplate record.tag position).2 then 1 else 0 : Nat) ≤ 1 := by
        split <;> omega
      simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
      omega)
  simp only [List.length_finRange] at bound
  unfold Record.outputBits Record.outputWords templateWords
  rw [encodeWords_flatMap]
  omega

theorem recordBits_length (record : Record) :
    record.bits.length = record.tag.val + record.output + record.first + record.second + 4 := by
  simp [Record.bits, Record.words, encodeWords_length]
  omega

theorem gateSteps_le_inputSize (record : Record) :
    gateSteps record ≤ 27 * record.bits.length := by
  have bound := gateSteps_le record
  rw [recordBits_length]
  omega

theorem outputBits_length_le_inputSize (record : Record) :
    record.outputBits.length ≤ 9 * record.bits.length := by
  have bound := outputBits_length_le record
  rw [recordBits_length]
  omega

theorem gateTrace (record : Record) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    (MachineComposition.advance (TM2.step program))^[gateSteps record]
      (some ⟨some (.setup (.gate record.tag 0)), state, base⟩) =
      some ⟨some (.cleanup 0), initialState, Function.update base .reversed
        (record.outputBits.reverse ++ base .reversed)⟩ := by
  have trace := contextListTrace (gateContexts record.tag) (some (.cleanup 0))
    (gateContexts_linked record.tag) base scratchEmpty state
    (by intro h; have := congrArg List.length h; simp [gateContexts] at this)
  rw [gateSteps_eq record base h1 h2 h3, gateOutput_words record base h1 h2 h3] at trace
  simpa [contextListStart, gateContexts, List.finRange] using trace

def gateInTime (record : Record) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup (.gate record.tag 0)), state, base⟩
      (some ⟨some (.cleanup 0), initialState, Function.update base .reversed
        (record.outputBits.reverse ++ base .reversed)⟩)
      (gateSteps record) where
  steps := gateSteps record
  evals_in_steps := gateTrace record base scratchEmpty state h1 h2 h3
  steps_le_m := Nat.le_refl _

theorem outputTrace (selected : Nat) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (cached : base .selected = encodeWord selected) :
    (MachineComposition.advance (TM2.step program))^[9 * (selected + 1) + 9]
      (some ⟨some (.setup (.output 0)), state, base⟩) =
      some ⟨some .finalCounter, initialState, Function.update base .reversed
        ((encodeWords (outputWords selected)).reverse ++ base .reversed)⟩ := by
  have trace := contextListTrace outputContexts (some .finalCounter)
    outputContexts_linked base scratchEmpty state (by simp [outputContexts])
  have steps : contextListSteps outputContexts base = 9 * (selected + 1) + 9 := by
    simp [contextListSteps, outputContexts, contextSteps, contextSource, cached]
    omega
  have out : contextListOutput outputContexts base = encodeWords (outputWords selected) := by
    simp [contextListOutput, outputContexts, contextOutput, contextSource, cached,
      output_word, contextWords, outputWords, encodeWords, List.append_assoc]
  rw [steps, out] at trace
  exact trace

def outputInTime (selected : Nat) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (cached : base .selected = encodeWord selected) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup (.output 0)), state, base⟩
      (some ⟨some .finalCounter, initialState, Function.update base .reversed
        ((encodeWords (outputWords selected)).reverse ++ base .reversed)⟩)
      (9 * (selected + 1) + 9) where
  steps := 9 * (selected + 1) + 9
  evals_in_steps := outputTrace selected base scratchEmpty state cached
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.CircuitEmission

end

end OAI
