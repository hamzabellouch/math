import OAI.Computability.UniqueGames.Machines.MachineClone100TableLemmas
import OAI.Computability.UniqueGames.Machines.MachineClone100Triples

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Loop

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
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

private theorem bodyCost_eq (D : Nat) (r : Record) :
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
      have hb := bodyCost_eq triples.length r
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

end UniqueGamesTheorem.Explicit.MachineClone100Loop

end

end OAI
