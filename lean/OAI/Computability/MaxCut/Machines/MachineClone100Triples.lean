import Mathlib
import OAI.Computability.MaxCut.PCP.PreprocessingStageMaps
import OAI.Computability.MaxCut.Machines.MachineClone100Table

namespace OAI

namespace MaxCutGames.Explicit.MachineClone100Triples

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MachineClone100Model MachineClone100Context MachineClone100Affine

def rowOutput (t : Nat × Nat × Nat) (base : Tape → List Bool) : List Bool :=
  (base (.field 0)).flatMap (affineEmit 100 t.1) ++
    (base (.field 1)).flatMap (affineEmit 100 t.2.1) ++
    (base (.field 2)).flatMap (affineEmit 100 t.2.2) ++
    (base (.field 3)).flatMap (affineEmit 1 0)

def rowSteps (base : Tape → List Bool) : Nat :=
  3 * ((base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length) + 12

def startAt (D i : Nat) : Option (Label D) :=
  if h : i < D then some (.setup (.inr (⟨i, h⟩, 0))) else some (.cleanup 0)

@[simp] theorem contextTapes_field (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (base : Tape → List Bool) (j : Fin 4) :
    contextTapes triples c base (.field j) = base (.field j) :=
  contextTapes_other triples c base _ (by intro h; cases h)

@[simp] theorem rowOutput_update (t : Nat × Nat × Nat) (base : Tape → List Bool)
    (out : List Bool) :
    rowOutput t (Function.update base .reversed out) = rowOutput t base := by
  simp [rowOutput]

@[simp] theorem rowSteps_update (base : Tape → List Bool) (out : List Bool) :
    rowSteps (Function.update base .reversed out) = rowSteps base := by
  simp [rowSteps]

private theorem chain_inline_MachineClone100Triples {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

theorem fourContexts_tapes (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (base : Tape → List Bool) :
    contextTapes triples (.inr (i, 3))
      (contextTapes triples (.inr (i, 2))
        (contextTapes triples (.inr (i, 1))
          (contextTapes triples (.inr (i, 0)) base))) =
      Function.update base .reversed ((rowOutput (triples.get i) base).reverse ++
        base .reversed) := by
  simp [contextTapes, output_eq_flatMap, emission, contextSource, contextScale,
    contextOffset, tripleField, rowOutput, List.reverse_append, List.append_assoc]

/-- Execute each of the four actual contexts in slot order. -/
theorem rowTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (i : Fin triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[rowSteps base]
      (some ⟨some (.setup (.inr (i, 0))), state, base⟩) =
      some ⟨startAt triples.length (i.val + 1), initialState _,
        Function.update base .reversed ((rowOutput (triples.get i) base).reverse ++
          base .reversed)⟩ := by
  let b1 := contextTapes triples (.inr (i, 0)) base
  let b2 := contextTapes triples (.inr (i, 1)) b1
  let b3 := contextTapes triples (.inr (i, 2)) b2
  have h0 := contextTrace triples nonempty (.inr (i, 0)) base scratchEmpty state
  have h1 := contextTrace triples nonempty (.inr (i, 1)) b1
    (by simpa [b1] using scratchEmpty) (initialState _)
  have h2 := contextTrace triples nonempty (.inr (i, 2)) b2
    (by simpa [b2, b1] using scratchEmpty) (initialState _)
  have h3 := contextTrace triples nonempty (.inr (i, 3)) b3
    (by simpa [b3, b2, b1] using scratchEmpty) (initialState _)
  have next0 : contextNext (.inr (i, (0 : Fin 4))) = some (.setup (.inr (i, 1))) := rfl
  have next1 : contextNext (.inr (i, (1 : Fin 4))) = some (.setup (.inr (i, 2))) := rfl
  have next2 : contextNext (.inr (i, (2 : Fin 4))) = some (.setup (.inr (i, 3))) := rfl
  have next3 : contextNext (.inr (i, (3 : Fin 4))) =
      startAt triples.length (i.val + 1) := by simp [contextNext, startAt]
  rw [next0] at h0
  rw [next1] at h1
  rw [next2] at h2
  rw [next3] at h3
  have combined := chain_inline_MachineClone100Triples (chain_inline_MachineClone100Triples (chain_inline_MachineClone100Triples h0 h1) h2) h3
  simp only [contextSource, b3, b2, b1, contextTapes_field] at combined
  rw [fourContexts_tapes] at combined
  convert combined using 1
  unfold rowSteps
  congr 1
  omega

private theorem tailTrace_inline_MachineClone100Triples (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (remaining : Nat) :
    ∀ (i : Nat), i + remaining = triples.length →
      ∀ (base : Tape → List Bool) (_scratchEmpty : base .scratch = [])
        (state : State triples.length),
        (remaining = 0 → state = initialState _) →
        (MachineComposition.advance (TM2.step (program triples nonempty)))^[remaining * rowSteps base]
          (some ⟨startAt triples.length i, state, base⟩) =
          some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
            (((triples.drop i).flatMap (fun t => rowOutput t base)).reverse ++ base .reversed)⟩ := by
  induction remaining with
  | zero =>
      intro i hi base scratchEmpty state finalState
      have heq : i = triples.length := by omega
      subst i
      rw [finalState rfl]
      simp [startAt]
  | succ remaining ih =>
      intro i hi base scratchEmpty state finalState
      have hiLt : i < triples.length := by omega
      let index : Fin triples.length := ⟨i, hiLt⟩
      let after := Function.update base .reversed
        ((rowOutput (triples.get index) base).reverse ++ base .reversed)
      have row := rowTrace triples nonempty index base scratchEmpty state
      have rest := ih (i + 1) (by omega) after
        (by simpa [after] using scratchEmpty) (initialState _) (by intro _; rfl)
      have combined := chain_inline_MachineClone100Triples row rest
      have dropHead : triples.drop i = triples.get index :: triples.drop (i + 1) :=
        List.drop_eq_getElem_cons hiLt
      have hstart : startAt triples.length i = some (.setup (.inr (index, 0))) := by
        simp [startAt, hiLt, index]
      rw [hstart]
      simp only [after, rowSteps_update, rowOutput_update] at combined
      simp only [Function.update_self, Function.update_idem] at combined
      rw [dropHead]
      simp only [List.flatMap_cons, List.reverse_append, List.append_assoc]
      convert combined using 1
      congr 1
      simp [Nat.add_mul]

theorem tableTrace_raw (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (scratchEmpty : base .scratch = [])
    (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[triples.length * rowSteps base]
      (some ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), state, base⟩) =
      some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
        ((triples.flatMap (fun t => rowOutput t base)).reverse ++ base .reversed)⟩ := by
  have h := tailTrace_inline_MachineClone100Triples triples nonempty triples.length 0 (by omega) base scratchEmpty state
    (by intro hz; exact False.elim (by have := List.length_pos_iff.mpr nonempty; omega))
  simpa [startAt, List.length_pos_iff.mpr nonempty] using h

def affineRecord (a b c rhs : Nat) (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * a, t.2.1 + 100 * b, t.2.2 + 100 * c, rhs]

theorem rowOutput_words (t : Nat × Nat × Nat) (base : Tape → List Bool)
    (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    rowOutput t base = encodeWords (affineRecord a b c rhs t) := by
  simp [rowOutput, h0, h1, h2, h3, affineEmit_word, affineRecord, encodeWords,
    List.append_assoc]

theorem tableOutput_words (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    triples.flatMap (fun t => rowOutput t base) =
      encodeWords (triples.flatMap (affineRecord a b c rhs)) := by
  induction triples with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.flatMap_cons, encodeWords_append, ih,
        rowOutput_words t base a b c rhs h0 h1 h2 h3]

/-- The actual inner loop outputs the concrete cloned equation words. -/
theorem tableTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (scratchEmpty : base .scratch = [])
    (state : State triples.length) (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
      triples.length * (3 * ((a + 1) + (b + 1) + (c + 1) + (rhs + 1)) + 12)]
      (some ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), state, base⟩) =
      some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
        ((encodeWords (triples.flatMap (affineRecord a b c rhs))).reverse ++ base .reversed)⟩ := by
  have h := tableTrace_raw triples nonempty base scratchEmpty state
  rw [tableOutput_words triples base a b c rhs h0 h1 h2 h3] at h
  simpa only [rowSteps, h0, h1, h2, h3, encodeWord_length] using h

theorem tableTapes_other (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (tape : Tape) (different : tape ≠ .reversed) :
    Function.update base .reversed
      ((triples.flatMap (fun t => rowOutput t base)).reverse ++ base .reversed) tape =
      base tape := by simp [different]

end MaxCutGames.Explicit.MachineClone100Triples

namespace MaxCutGames.Explicit.MachineClone100Loop

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineClone100Model

structure Record where
  a : Nat
  b : Nat
  c : Nat
  rhs : Nat

def recordWords (r : Record) : List Nat := [r.a, r.b, r.c, r.rhs]
def recordBits (r : Record) : List Bool := encodeWords (recordWords r)
def recordsBits (rs : List Record) : List Bool := rs.flatMap recordBits

def clonedRecordBits (triples : List (Nat × Nat × Nat)) (r : Record) : List Bool :=
  encodeWords (triples.flatMap (MachineClone100Triples.affineRecord r.a r.b r.c r.rhs))

def clonedRecordsBits (triples : List (Nat × Nat × Nat)) (rs : List Record) : List Bool :=
  rs.flatMap (clonedRecordBits triples)

def recordFields (r : Record) (j : Fin 4) : List Bool :=
  encodeWord (match j.val with | 0 => r.a | 1 => r.b | 2 => r.c | _ => r.rhs)

/-- The frame records all tapes, including untouched header and output tapes.
At every loop guard the four fields are empty and scratch is empty. -/
def tapes (base : Tape → List Bool) (input counter accumulator : List Bool)
    (fields : Fin 4 → List Bool) : Tape → List Bool
  | .input => input
  | .header => base .header
  | .counter => counter
  | .field j => fields j
  | .scratch => []
  | .reversed => accumulator
  | .output => base .output

theorem update_reversed (base : Tape → List Bool) (input counter acc out : List Bool)
    (fields : Fin 4 → List Bool) :
    Function.update (tapes base input counter acc fields) .reversed out =
      tapes base input counter out fields := by
  funext tape
  cases tape <;> simp [tapes]

theorem counterTapes_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes .counter
      (tapes base input counter acc fields) n [] =
      tapes base input (encodeWord n) acc fields := by
  funext tape
  cases tape <;> simp [MachineUnaryCounter.counterTapes, tapes]

theorem fourTapes_eq (base : Tape → List Bool) (input counter acc suffix : List Bool)
    (r : Record) :
    SourceMachine.fourTapes .input Tape.field
      (tapes base input counter acc (fun _ => [])) r.a r.b r.c r.rhs suffix =
      tapes base suffix counter acc (recordFields r) := by
  funext tape
  cases tape with
  | field j =>
    fin_cases j <;>
      simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
        tapes, recordFields]
  | _ =>
    simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
      tapes]

theorem clearFields_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) :
    MachineClone100Cleanup.clearFields (tapes base input counter acc fields) =
      tapes base input counter acc (fun _ => []) := by
  funext tape
  cases tape <;> simp [tapes]

theorem cleanupSteps_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (r : Record) :
    MachineClone100Cleanup.cleanupSteps (tapes base input counter acc (recordFields r)) =
      r.a + r.b + r.c + r.rhs + 8 := by
  simp [MachineClone100Cleanup.cleanupSteps, tapes, recordFields]
  omega

theorem recordBits_length (r : Record) :
    (recordBits r).length = r.a + r.b + r.c + r.rhs + 4 := by
  simp [recordBits, recordWords, encodeWords]
  omega

def bodyCost (D : Nat) (r : Record) : Nat :=
  (2 + 3 * D) * (recordBits r).length + (8 + 12 * D)

private theorem bodyCost_eq_inline_MachineClone100Loop (D : Nat) (r : Record) :
    ((r.a + r.b + r.c + r.rhs + 8) +
      D * (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)) +
      (r.a + r.b + r.c + r.rhs + 8) = bodyCost D r := by
  rw [bodyCost, recordBits_length]
  ring

def bodyInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (r : Record) (suffix counter acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.fieldStart 0), initialState _,
        tapes base (recordBits r ++ suffix) counter acc (fun _ => [])⟩
      (some ⟨some .guard, initialState _,
        tapes base suffix counter ((clonedRecordBits triples r).reverse ++ acc)
          (fun _ => [])⟩)
      (bodyCost triples.length r) := by
  let before := tapes base (recordBits r ++ suffix) counter acc (fun _ => [])
  let parsed := tapes base suffix counter acc (recordFields r)
  let out := (clonedRecordBits triples r).reverse ++ acc
  let emitted := tapes base suffix counter out (recordFields r)
  let parse := SourceMachine.fourFieldsInTime .input Tape.field
    (by intro j h; cases h) Label.fieldStart Label.fieldLoop
    (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))))
    (program triples nonempty) (by intro j; rfl) (by intro j; rfl)
    before r.a r.b r.c r.rhs suffix rfl ((), defaultControl _) none
  have parsed_eq : SourceMachine.fourTapes .input Tape.field before
      r.a r.b r.c r.rhs suffix = parsed := fourTapes_eq _ _ _ _ _ _
  rw [parsed_eq] at parse
  let table : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), initialState _, parsed⟩
      (some ⟨some (.cleanup 0), initialState _, emitted⟩)
      (triples.length * (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)) := {
    steps := triples.length *
      (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)
    evals_in_steps := by
      change (MachineComposition.advance (TM2.step (program triples nonempty)))^[_] _ = _
      have h := MachineClone100Triples.tableTrace triples nonempty parsed rfl
        (initialState _) r.a r.b r.c r.rhs rfl rfl rfl rfl
      simpa only [parsed, tapes, update_reversed, clonedRecordBits, emitted, out] using h
    steps_le_m := Nat.le_refl _ }
  let cleanup := MachineClone100Cleanup.cleanupFourInTime triples nonempty emitted
    ((), defaultControl _) none
  have cleared : MachineClone100Cleanup.clearFields emitted =
      tapes base suffix counter out (fun _ => []) := clearFields_eq _ _ _ _ _
  rw [cleared] at cleanup
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parse table
  let combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first cleanup
  exact {
    toEvalsTo := combined.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans combined.steps_le_m
      have hc : MachineClone100Cleanup.cleanupSteps emitted =
          r.a + r.b + r.c + r.rhs + 8 := cleanupSteps_eq _ _ _ _ _
      have hb := bodyCost_eq_inline_MachineClone100Loop triples.length r
      omega }

def loopCost (D : Nat) : List Record → Nat
  | [] => 1
  | r :: rs => (1 + bodyCost D r) + loopCost D rs

theorem loopCost_eq (D : Nat) (rs : List Record) :
    loopCost D rs = (2 + 3 * D) * (recordsBits rs).length +
      (9 + 12 * D) * rs.length + 1 := by
  induction rs with
  | nil => simp [loopCost, recordsBits]
  | cons r rs ih =>
    simp only [loopCost, ih, recordsBits, List.flatMap_cons, List.length_append,
      List.length_cons, bodyCost]
    ring

/-- The complete record loop consumes exactly the specified occurrence list.
The final zero guard retains the counter delimiter for the final cleanup stage.
Arbitrary suffixes and already emitted prefixes are preserved explicitly. -/
def loopInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (suffix : List Bool) (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _,
        tapes base (recordsBits rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _,
        tapes base suffix (encodeWord 0) ((clonedRecordsBits triples rs).reverse ++ acc)
          (fun _ => [])⟩)
      (loopCost triples.length rs) := by
  induction rs generalizing acc with
  | nil =>
    let guard := MachineUnaryCounter.guardInTime_zero .counter Label.guard
      (.fieldStart 0) .finalCounter (program triples nonempty) rfl
      (tapes base suffix (encodeWord 0) acc (fun _ => [])) []
      ((), defaultControl _) none
    simpa only [counterTapes_eq, loopCost, recordsBits, clonedRecordsBits,
      List.flatMap_nil, List.reverse_nil, List.nil_append, List.length_nil,
      initialState] using guard
  | cons r rs ih =>
    let before := tapes base (recordBits r ++ (recordsBits rs ++ suffix))
      (encodeWord (rs.length + 1)) acc (fun _ => [])
    let guard := MachineUnaryCounter.guardInTime_succ .counter Label.guard
      (.fieldStart 0) .finalCounter (program triples nonempty) rfl before rs.length []
      ((), defaultControl _) none
    simp only [before, counterTapes_eq] at guard
    let body := bodyInTime triples nonempty base r (recordsBits rs ++ suffix)
      (encodeWord rs.length) acc
    let rest := ih ((clonedRecordBits triples r).reverse ++ acc)
    let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    let combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [loopCost, recordsBits, clonedRecordsBits, List.flatMap_cons,
      List.length_cons, List.reverse_append, List.append_assoc, initialState,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

/-- A linear bound derived from the actual composed execution. -/
def loopInTime_linear (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (suffix : List Bool) (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _,
        tapes base (recordsBits rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _,
        tapes base suffix (encodeWord 0) ((clonedRecordsBits triples rs).reverse ++ acc)
          (fun _ => [])⟩)
      ((2 + 3 * triples.length) * (recordsBits rs).length +
        (9 + 12 * triples.length) * rs.length + 1) := by
  simpa only [loopCost_eq] using loopInTime triples nonempty base suffix rs acc

def recordOfEquation {n : Nat} (e : CloneGap.Equation (Fin n)) : Record :=
  ⟨e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0⟩

theorem recordsBits_equations {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    recordsBits (es.map recordOfEquation) =
      encodeWords (es.flatMap SourceEncoding.equationWords) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, recordsBits, List.flatMap_cons, encodeWords_append] at *
    rw [ih]
    rfl

theorem clonedRecordsBits_equations_table (triples : List (Nat × Nat × Nat))
    {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    clonedRecordsBits triples (es.map recordOfEquation) =
      encodeWords (es.flatMap fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, clonedRecordsBits, List.flatMap_cons, encodeWords_append] at *
    rw [ih]
    rfl

def sourceLoopInTime_table (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (base : Tape → List Bool) (suffix acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _, tapes base
        (encodeWords (es.flatMap SourceEncoding.equationWords) ++ suffix)
        (encodeWord es.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _, tapes base suffix (encodeWord 0)
        ((encodeWords (es.flatMap fun e => triples.flatMap
          (MachineClone100Table.cloneEquationWords e))).reverse ++ acc) (fun _ => [])⟩)
      ((2 + 3 * triples.length) *
        (encodeWords (es.flatMap SourceEncoding.equationWords)).length +
        (9 + 12 * triples.length) * es.length + 1) := by
  simpa only [recordsBits_equations, clonedRecordsBits_equations_table, List.length_map] using
    loopInTime_linear triples nonempty base suffix (es.map recordOfEquation) acc

end MaxCutGames.Explicit.MachineClone100Loop

namespace MaxCutGames.Explicit.MachineClone100Finish

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MachineClone100Model

def finishTapes (base : Tape → List Bool) : Tape → List Bool :=
  MachineTransfer.tapesAt .reversed .output (Function.update base .counter []) []
    ((base .reversed).reverse ++ base .output)

@[simp] theorem finishTapes_counter (base : Tape → List Bool) :
    finishTapes base .counter = [] := by simp [finishTapes, MachineTransfer.tapesAt]

@[simp] theorem finishTapes_reversed (base : Tape → List Bool) :
    finishTapes base .reversed = [] := by simp [finishTapes, MachineTransfer.tapesAt]

@[simp] theorem finishTapes_output (base : Tape → List Bool) :
    finishTapes base .output = (base .reversed).reverse ++ base .output := by
  simp [finishTapes, MachineTransfer.tapesAt]

theorem finishTapes_other (base : Tape → List Bool) (tape : Tape)
    (hc : tape ≠ .counter) (hr : tape ≠ .reversed) (ho : tape ≠ .output) :
    finishTapes base tape = base tape := by
  simp [finishTapes, MachineTransfer.tapesAt, hc, hr, ho]

theorem counterStep (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    TM2.step (program triples hne)
      ⟨some .finalCounter, initialState _, base⟩ =
        some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩ := by
  simp [TM2.step, TM2.stepAux, program, initialState, hcounter]

theorem finishTrace (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 2]
      (some ⟨some .finalCounter, initialState _, base⟩) =
        some ⟨none, initialState _, finishTapes base⟩ := by
  have first := counterStep triples hne base hcounter
  have rest := MachineTransfer.transferAt_fromTapes Tape.reversed Tape.output
    (by decide) id false (Label.finalReverse : Label triples.length) none
    (program triples hne) rfl (Function.update base Tape.counter [])
    ((), defaultControl triples.length) none
  change (MachineComposition.advance (TM2.step (program triples hne)))^[
      ((Function.update base Tape.counter []) Tape.reversed).length + 1]
    (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) = _ at rest
  have rest' :
      (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 1]
        (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) =
          some ⟨none, initialState _, finishTapes base⟩ := by
    simpa only [finishTapes, initialState,
      Function.update_of_ne (by decide : Tape.reversed ≠ Tape.counter),
      Function.update_of_ne (by decide : Tape.output ≠ Tape.counter), List.map_id] using rest
  rw [show (base .reversed).length + 2 = ((base .reversed).length + 1) + 1 by omega,
    Function.iterate_succ_apply, MachineComposition.advance_some, first]
  exact rest'

def finishInTime (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    StateTransition.EvalsToInTime (TM2.step (program triples hne))
      ⟨some .finalCounter, initialState _, base⟩
      (some ⟨none, initialState _, finishTapes base⟩) ((base .reversed).length + 2) where
  steps := (base .reversed).length + 2
  evals_in_steps := finishTrace triples hne base hcounter
  steps_le_m := Nat.le_refl _

theorem finish_eq_haltList (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool)
    (emptyOther : ∀ tape, tape ≠ .counter → tape ≠ .reversed → base tape = []) :
    (⟨none, initialState _, finishTapes base⟩ : (machine triples hne).Cfg) =
      haltList (machine triples hne) ((base .reversed).reverse) := by
  have hout := emptyOther .output (by decide) (by decide)
  have ht : finishTapes base =
      (haltList (machine triples hne) ((base .reversed).reverse)).stk := by
    funext tape
    cases tape <;> simp [finishTapes, MachineTransfer.tapesAt, haltList, machine, hout,
      emptyOther]
    rfl
  exact congrArg
    (fun tapes => (⟨none, initialState triples.length, tapes⟩ : (machine triples hne).Cfg)) ht

end MaxCutGames.Explicit.MachineClone100Finish

namespace MaxCutGames.Explicit.MachineClone100Run

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MachineClone100Model

def tm (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 :=
  machine triples nonempty

def emptyTapes : Tape → List Bool := fun _ => []

def sourceBody (input : SourceEncoding.Input) : List Bool :=
  encodeWords (input.equations.flatMap SourceEncoding.equationWords)

def outputHeaders (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  encodeWords [100 * input.«variables», triples.length * input.equations.length]

def outputBody (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  encodeWords (input.equations.flatMap fun equation =>
    triples.flatMap (MachineClone100Table.cloneEquationWords equation))

def outputBits (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  outputHeaders triples input ++ outputBody triples input

def inputTapes (input : SourceEncoding.Input) : Tape → List Bool :=
  fun tape => if tape = .input then SourceEncoding.inputBits input else []

def guardTapes (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    Tape → List Bool :=
  MachineClone100Loop.tapes emptyTapes (sourceBody input) (encodeWord input.equations.length)
    (outputHeaders triples input).reverse (fun _ => [])

def afterLoopTapes (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    Tape → List Bool :=
  MachineClone100Loop.tapes emptyTapes [] (encodeWord 0)
    ((outputBody triples input).reverse ++ (outputHeaders triples input).reverse) (fun _ => [])

theorem inputBits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.«variables», input.equations.length] ++ sourceBody input := by
  simp only [SourceEncoding.inputBits, SourceEncoding.inputWords, encodeWords_append, sourceBody]

theorem initList_eq (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    initList (tm triples nonempty) (SourceEncoding.inputBits input) =
      ⟨some (.headerStart 0), initialState triples.length, inputTapes input⟩ := by
  change (⟨some (.headerStart 0), initialState triples.length,
    (initList (tm triples nonempty) (SourceEncoding.inputBits input)).stk⟩ :
    (tm triples nonempty).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨some (.headerStart 0), initialState triples.length, tapes⟩ : (tm triples nonempty).Cfg))
  funext tape
  cases tape <;> simp [initList, tm, machine, inputTapes]
  rfl

theorem headers_result_eq (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    MachineClone100Headers.resultTapes triples (inputTapes input)
      input.«variables» input.equations.length (sourceBody input) = guardTapes triples input := by
  funext tape
  cases tape <;> simp [MachineClone100Headers.resultTapes, inputTapes, guardTapes,
    MachineClone100Loop.tapes, emptyTapes, outputHeaders]

theorem afterLoop_reversed (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    (afterLoopTapes triples input .reversed).reverse = outputBits triples input := by
  simp only [afterLoopTapes, MachineClone100Loop.tapes, List.reverse_append,
    List.reverse_reverse, outputBits]

theorem afterLoop_length (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    (afterLoopTapes triples input .reversed).length = (outputBits triples input).length := by
  calc
    _ = ((afterLoopTapes triples input .reversed).reverse).length := List.length_reverse.symm
    _ = _ := congrArg List.length (afterLoop_reversed triples input)

theorem finish_eq (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    (⟨none, initialState triples.length,
      MachineClone100Finish.finishTapes (afterLoopTapes triples input)⟩ :
      (tm triples nonempty).Cfg) =
        haltList (tm triples nonempty) (outputBits triples input) := by
  have finished := MachineClone100Finish.finish_eq_haltList triples nonempty
    (afterLoopTapes triples input) (by
      intro tape counter reversed
      cases tape <;> simp_all [afterLoopTapes, MachineClone100Loop.tapes, emptyTapes])
  simpa only [afterLoop_reversed, tm] using finished

/-- Actual execution from the existing input codec to the complete literal
halt configuration, with the sum of the three proved phase budgets. -/
def runInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    TM2OutputsInTime (tm triples nonempty) (SourceEncoding.inputBits input)
      (some (outputBits triples input))
      (((outputBits triples input).length + 2) +
        (((2 + 3 * triples.length) * (sourceBody input).length +
            (9 + 12 * triples.length) * input.equations.length + 1) +
          (5 * input.«variables» + 4 * input.equations.length + 18))) := by
  let first := MachineClone100Headers.headersInTime triples nonempty
    (inputTapes input) input.«variables» input.equations.length (sourceBody input)
    (by simpa only [inputTapes, ite_true] using inputBits_eq input) rfl rfl rfl rfl
  have first' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      (initList (tm triples nonempty) (SourceEncoding.inputBits input))
      (some ⟨some .guard, initialState _, guardTapes triples input⟩)
      (5 * input.«variables» + 4 * input.equations.length + 18) := by
    rw [initList_eq, ← headers_result_eq]
    exact first
  let middle := MachineClone100Loop.sourceLoopInTime_table triples nonempty
    (n := input.«variables») input.equations emptyTapes [] (outputHeaders triples input).reverse
  have middle' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _, guardTapes triples input⟩
      (some ⟨some .finalCounter, initialState _, afterLoopTapes triples input⟩)
      ((2 + 3 * triples.length) * (sourceBody input).length +
        (9 + 12 * triples.length) * input.equations.length + 1) := by
    simpa only [List.append_nil, guardTapes, afterLoopTapes, sourceBody, outputBody] using middle
  let last := MachineClone100Finish.finishInTime triples nonempty (afterLoopTapes triples input) rfl
  have last' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .finalCounter, initialState _, afterLoopTapes triples input⟩
      (some (haltList (tm triples nonempty) (outputBits triples input)))
      ((outputBits triples input).length + 2) := by
    rw [← afterLoop_length, ← finish_eq]
    exact last
  let firstTwo := StateTransition.EvalsToInTime.trans
    (TM2.step (program triples nonempty)) _ _ _ _ _ first' middle'
  let allThree := StateTransition.EvalsToInTime.trans
    (TM2.step (program triples nonempty)) _ _ _ _ _ firstTwo last'
  exact { toEvalsTo := allThree.toEvalsTo, steps_le_m := allThree.steps_le_m }

end MaxCutGames.Explicit.MachineClone100Run

namespace MaxCutGames.Explicit.MachineClone100Certified

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity

noncomputable def timePolynomial (copies : Nat) : Polynomial Nat :=
  Polynomial.C (300 * copies) * Polynomial.X * Polynomial.X +
    Polynomial.C (120 + 18 * copies) * Polynomial.X + Polynomial.C 23

theorem timePolynomial_eval (copies length : Nat) :
    (timePolynomial copies).eval length =
      (300 * copies) * length * length + (120 + 18 * copies) * length + 23 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

private theorem numericalBudget_inline_MachineClone100Certified (D N n m B out : Nat)
    (hn : n ≤ N) (hm : m ≤ N) (hB : B ≤ N)
    (ho : out ≤ (300 * D) * N * N + (100 + 3 * D) * N + 2) :
    (out + 2) + (((2 + 3 * D) * B + (9 + 12 * D) * m + 1) +
      (5 * n + 4 * m + 18)) ≤ (300 * D) * N * N + (120 + 18 * D) * N + 23 := by
  have hn' := Nat.mul_le_mul_left 5 hn
  have hm' := Nat.mul_le_mul_left (13 + 12 * D) hm
  have hb' := Nat.mul_le_mul_left (2 + 3 * D) hB
  calc
    _ = 5 * n + (13 + 12 * D) * m + (2 + 3 * D) * B + out + 21 := by ring
    _ ≤ 5 * N + (13 + 12 * D) * N + (2 + 3 * D) * N +
        ((300 * D) * N * N + (100 + 3 * D) * N + 2) + 21 := by omega
    _ = _ := by ring

noncomputable def certifiedFunction (triples : List (CloneGap.Index × CloneGap.Index × CloneGap.Index))
    (nonempty : triples ≠ []) (f : SourceEncoding.Input → SourceEncoding.Input)
    (output_eq : ∀ input, SourceEncoding.inputBits (f input) =
      MachineClone100Run.outputBits triples input)
    (size_bound : ∀ input,
      (SourceEncoding.inputBits (f input)).length ≤
        (300 * triples.length) * (SourceEncoding.inputBits input).length *
            (SourceEncoding.inputBits input).length +
          (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2) :
    TM2ComputableInPolyTime SourceEncoding.inputBits SourceEncoding.inputBits f where
  tm := MachineClone100Run.tm triples nonempty
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial triples.length
  outputsFun input := by
    change TM2OutputsInTime (MachineClone100Run.tm triples nonempty)
      ((SourceEncoding.inputBits input).map id)
      (some ((SourceEncoding.inputBits (f input)).map id))
      ((timePolynomial triples.length).eval (SourceEncoding.inputBits input).length)
    rw [@List.map_id ((MachineClone100Run.tm triples nonempty).Γ
      (MachineClone100Run.tm triples nonempty).k₀) (SourceEncoding.inputBits input),
      @List.map_id ((MachineClone100Run.tm triples nonempty).Γ
        (MachineClone100Run.tm triples nonempty).k₁) (SourceEncoding.inputBits (f input)),
      output_eq input, timePolynomial_eval]
    let actual := MachineClone100Run.runInTime triples nonempty input
    refine { toEvalsTo := actual.toEvalsTo, steps_le_m := actual.steps_le_m.trans ?_ }
    apply numericalBudget_inline_MachineClone100Certified
    · exact SourceEncoding.inputBits_length_ge_variables input
    · exact SourceEncoding.inputBits_length_ge_equations input
    · have h := SourceEncoding.inputBits_length input
      change (SourceEncoding.inputBits input).length =
        input.«variables» + input.equations.length + 2 +
          (MachineClone100Run.sourceBody input).length at h
      omega
    · rw [← output_eq input]
      exact size_bound input

end MaxCutGames.Explicit.MachineClone100Certified

end OAI
