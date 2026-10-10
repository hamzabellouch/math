import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineSubdivisionRows

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionInit

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

theorem source_ne_scratch (i : Fin 9) : (initOp i).source ≠ Tape.affineScratch := by
  fin_cases i <;> simp [initOp]

theorem source_ne_destination (i : Fin 9) : (initOp i).source ≠ (initOp i).destination := by
  fin_cases i <;> simp [initOp]

theorem scratch_ne_destination (i : Fin 9) : Tape.affineScratch ≠ (initOp i).destination := by
  fin_cases i <;> simp [initOp]

def priorWord (seed : Option Nat) (b : Nat) : List Bool :=
  match seed with
  | none => encodeWord b
  | some _ => []

theorem operationTrace (q : Nat) (i : Fin 9) (base : Tape → List Bool) (a b : Nat)
    (sourceWord : base (initOp i).source = encodeWord a)
    (scratchEmpty : base .affineScratch = [])
    (destinationWord : base (initOp i).destination = priorWord (initOp i).seed b) :
    (MachineComposition.advance (machine q).step)^[2 * (a + 1) + 1]
      (some ⟨some (.initialize i 0), initialState, base⟩) =
      some ⟨some (initNext i), initialState,
        Function.update base (initOp i).destination
          (encodeWord ((initOp i).coefficient * a + (initOp i).seed.getD b))⟩ := by
  cases seedValue : (initOp i).seed with
  | some offset =>
    have run := MachineUnaryAffineAt.seededAffineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient offset
      (.initialize i 0 : Label q) (.initialize i 1) (.initialize i 2)
      (some (initNext i)) (program q)
      (by simp [program, seedValue]) rfl rfl base a []
      (by simpa using sourceWord) scratchEmpty ((), ()) none
    have hd : base (initOp i).destination = [] := by
      simpa [priorWord, seedValue] using destinationWord
    simp only [initialState, hd, List.append_nil, Option.getD_some] at run ⊢
    exact run
  | none =>
    have hd : base (initOp i).destination = encodeWord b := by
      simpa [priorWord, seedValue] using destinationWord
    have frame (word : List Bool) :
        MachineUnaryAffineAt.tapes (initOp i).source Tape.affineScratch
          (initOp i).destination base (encodeWord a ++ []) [] word =
        Function.update base (initOp i).destination word := by
      simp only [List.append_nil]
      rw [← sourceWord, ← scratchEmpty]
      simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes,
        Function.update_eq_self]
    have run := MachineUnaryAffineAt.affineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient (.initialize i 1 : Label q) (.initialize i 2)
      (some (initNext i)) (program q) rfl rfl base a b [] [] ((), ()) none
    rw [frame, frame] at run
    simp only [List.append_nil, ← hd, Function.update_eq_self] at run
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine q).step)^[2 * (a + 1)]
      (some (TM2.stepAux (program q (.initialize i 0)) initialState base)) = _
    simp only [program, seedValue, TM2.stepAux]
    simp only [initialState, Option.getD_none] at run ⊢
    exact run

def sourceValue (n Q : Nat) : Fin 9 → Nat
  | 0 => n
  | 1 => Q
  | 2 => Q
  | 3 => n
  | 4 => n
  | 5 => Q
  | 6 => n
  | 7 => Q
  | 8 => Q

def beforeValue (n : Nat) : Fin 9 → Nat
  | 0 => 0
  | 1 => n
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => n
  | 6 => 0
  | 7 => n + 1
  | 8 => 0

def afterValue (n Q : Nat) (i : Fin 9) : Nat :=
  (initOp i).coefficient * sourceValue n Q i + (initOp i).seed.getD (beforeValue n i)

def frame (n q Q : Nat) (body : List Bool) : Nat → Tape → List Bool
  | 0 => MachineSubdivisionHeaders.resultTapes n q Q body
  | r + 1 => if h : r < 9 then
      Function.update (frame n q Q body r) (initOp ⟨r, h⟩).destination
        (encodeWord (afterValue n Q ⟨r, h⟩))
    else frame n q Q body r

theorem frame_source (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).source = encodeWord (sourceValue n Q i) := by
  fin_cases i <;>
    simp [frame, sourceValue, initOp, MachineSubdivisionHeaders.resultTapes]

theorem frame_scratch (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val .affineScratch = [] := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes]

theorem frame_destination (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).destination =
      priorWord (initOp i).seed (beforeValue n i) := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes,
    afterValue, sourceValue, beforeValue, priorWord]

def atStage (q r : Nat) : Label q :=
  if h : r < 9 then .initialize ⟨r, h⟩ 0
  else .emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)

theorem initNext_eq_atStage (q : Nat) (i : Fin 9) :
    (initNext i : Label q) = atStage q (i.val + 1) := by
  simp [initNext, atStage]

def stageCost (n Q : Nat) : Nat := 2 * (n + Q + 1) + 1

theorem sourceValue_le (n Q : Nat) (i : Fin 9) : sourceValue n Q i ≤ n + Q := by
  fin_cases i <;> simp [sourceValue]

def prefixInTime (q n Q : Nat) (body : List Bool) (r : Nat) (hr : r ≤ 9) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (atStage q r), initialState, frame n q Q body r⟩)
      (r * stageCost n Q) := by
  induction r with
  | zero =>
    refine { steps := 0, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp [atStage, frame]
    · simp
  | succ r ih =>
    have hlt : r < 9 := by omega
    let i : Fin 9 := ⟨r, hlt⟩
    have before := ih (by omega)
    have opTrace := operationTrace q i (frame n q Q body r)
      (sourceValue n Q i) (beforeValue n i)
      (frame_source n q Q body i) (frame_scratch n q Q body i)
      (frame_destination n q Q body i)
    have op : StateTransition.EvalsToInTime (machine q).step
        ⟨some (atStage q r), initialState, frame n q Q body r⟩
        (some ⟨some (atStage q (r + 1)), initialState, frame n q Q body (r + 1)⟩)
        (stageCost n Q) := {
      steps := 2 * (sourceValue n Q i + 1) + 1
      evals_in_steps := by
        change (MachineComposition.advance (TM2.step (program q)))^[_] _ = _
        simp only [atStage, hlt, ↓reduceDIte, i, initNext_eq_atStage, frame, afterValue]
          at opTrace ⊢
        exact opTrace
      steps_le_m := by
        have bound := sourceValue_le n Q i
        dsimp [stageCost]
        omega }
    have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ before op
    exact {
      toEvalsTo := joined.toEvalsTo
      steps_le_m := by
        calc
          joined.steps ≤ stageCost n Q + r * stageCost n Q := joined.steps_le_m
          _ = (r + 1) * stageCost n Q := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
    }

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => body
  | .vertices => encodeWord n
  | .alphabetHeader => encodeWord q
  | .occurrences => encodeWord Q
  | .remaining => encodeWord Q
  | .newVertices => encodeWord (n + 3 * Q)
  | .newEdges => encodeWord (4 * Q)
  | .middle => encodeWord n
  | .first => encodeWord (n + Q)
  | .last => encodeWord (n + Q + 1)
  | _ => []

theorem final_frame (n q Q : Nat) (body : List Bool) :
    frame n q Q body 9 = resultTapes n q Q body := by
  funext tape
  cases tape <;>
    simp [frame, resultTapes, initOp, MachineSubdivisionHeaders.resultTapes,
      afterValue, sourceValue, beforeValue, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]

def initializeInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, resultTapes n q Q body⟩)
      (9 * stageCost n Q) := by
  simpa only [atStage, show ¬ (9 < 9) by omega, ↓reduceDIte, final_frame]
    using prefixInTime q n Q body 9 (by omega)

end DFVSGames.Explicit.MachineSubdivisionInit


namespace DFVSGames.Explicit.MachineSubdivisionEmission

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

def headerBits (n q Q : Nat) : List Bool := encodeWords [n + 3 * Q, q, 4 * Q]

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineSubdivisionInit.resultTapes n q Q body)
    .accumulator (headerBits n q Q).reverse

theorem header_template (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      headerBits n q Q := by
  simp [MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput,
    headerTokens, newHeaderField, MachineSubdivisionInit.resultTapes,
    headerBits, encodeWords]

theorem header_copiedLength (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      n + 7 * Q + 2 := by
  simp [MachineFieldTemplate.copiedLength, headerTokens, newHeaderField,
    MachineSubdivisionInit.resultTapes]
  omega

theorem header_result (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.outputTapes (MachineSubdivisionInit.resultTapes n q Q body)
      .accumulator (headerBits n q Q) = resultTapes n q Q body := by
  simp only [MachineFieldTemplate.outputTapes, MachineSubdivisionInit.resultTapes,
    List.append_nil, resultTapes]

def headerInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, MachineSubdivisionInit.resultTapes n q Q body⟩
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (3 * (n + 7 * Q + 2) + 10) := by
  have run := MachineFieldTemplate.phaseInTime (headerTokens q) newHeaderField
    Tape.copyScratch Tape.accumulator
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide) (by decide)
    (Label.emitHeader : MachineFieldTemplate.Label (headerTokens q).length → Label q)
    (some .guard) (program q) (fun _ => rfl)
    (MachineSubdivisionInit.resultTapes n q Q body) rfl initialState
  rw [header_template, header_copiedLength, header_result] at run
  simp only [MachineFieldTemplate.reset, initialState,
    headerTokens, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
    at run ⊢
  exact run

def prepareInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6 + 9 * MachineSubdivisionInit.stageCost n Q +
        (3 * (n + 7 * Q + 2) + 10)) := by
  have h := MachineSubdivisionHeaders.headersInTime q n Q body
  have i := MachineSubdivisionInit.initializeInTime q n Q body
  have e := headerInTime q n Q body
  have hi := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h i
  have hie := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hi e
  exact {
    toEvalsTo := hie.toEvalsTo
    steps_le_m := by
      have bound := hie.steps_le_m
      omega }

end DFVSGames.Explicit.MachineSubdivisionEmission


namespace DFVSGames.Reduction.GameEncodingSize

open Foundations.Target Foundations.Complexity

theorem tableBits_length_le {q : Nat} (table : PermutationTable q) :
    (encodeWords (tableWords table)).length ≤ q * (q + 1) := by
  have h := encodeWords_length_le (tableWords table) q (by
    intro value hvalue
    obtain ⟨label, _, hlabel⟩ := List.mem_map.mp hvalue
    rw [← hlabel]
    exact Nat.le_of_lt label.isLt)
  simpa only [tableWords_length] using h

theorem constraintBits_length_le {n q : Nat} (constraint : Constraint n q) :
    (encodeWords (constraintWords constraint)).length ≤ 2 * n + q * (q + 1) := by
  have hs := constraint.source.isLt
  have ht := constraint.target.isLt
  have hp := tableBits_length_le constraint.permutation
  simp only [constraintWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem constraintsBits_length_le {n q : Nat} (constraints : List (Constraint n q)) :
    (encodeWords (constraints.flatMap constraintWords)).length ≤
      constraints.length * (2 * n + q * (q + 1)) := by
  induction constraints with
  | nil => simp [encodeWords]
  | cons constraint constraints ih =>
      have hc := constraintBits_length_le constraint
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem gameBits_length_le {q : Nat} (g : Instance q) :
    (gameBits g).length ≤
      g.vertices + q + g.constraints.length + 3 +
        g.constraints.length * (2 * g.vertices + q * (q + 1)) := by
  have h := constraintsBits_length_le g.constraints
  simp only [gameBits, gameWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end DFVSGames.Reduction.GameEncodingSize


namespace DFVSGames.Explicit.MachineSubdivisionTableRead

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

def tapes (base : Tape → List Bool) (input reversed : List Bool) : Tape → List Bool :=
  Function.update (Function.update base Tape.input input) Tape.permutationReverse reversed

@[simp] theorem tapes_input (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .input = input := by simp [tapes]

@[simp] theorem tapes_reverse (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .permutationReverse = reversed := by simp [tapes]

private theorem update_input_inline_MachineSubdivisionTableRead (base : Tape → List Bool) (input reversed replacement : List Bool) :
    Function.update (tapes base input reversed) .input replacement =
      tapes base replacement reversed := by
  funext k
  cases k <;> simp [tapes]

private theorem update_reverse_inline_MachineSubdivisionTableRead (base : Tape → List Bool) (input reversed replacement : List Bool) :
    Function.update (tapes base input reversed) .permutationReverse replacement =
      tapes base input replacement := by
  funext k
  cases k <;> simp [tapes]

theorem step_true (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (true :: input) reversed⟩ =
      some ⟨some (.readTable completed), (ambient, some true),
        tapes base input (true :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input_inline_MachineSubdivisionTableRead, update_reverse_inline_MachineSubdivisionTableRead]

theorem step_false (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (false :: input) reversed⟩ =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input (false :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input_inline_MachineSubdivisionTableRead, update_reverse_inline_MachineSubdivisionTableRead]

theorem readWordTrace (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (value : Nat) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[value + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWord value ++ input) reversed⟩) =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input ((encodeWord value).reverse ++ reversed)⟩ := by
  induction value generalizing reversed register with
  | zero =>
    simpa [encodeWord, MachineComposition.advance] using
      step_false q completed valid base input reversed ambient register
  | succ value ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append,
      MachineComposition.advance_some]
    rw [step_true q completed valid]
    have h := ih (true :: reversed) (some true)
    simpa only [encodeWord, List.reverse_cons, List.reverse_append,
      List.append_assoc, List.singleton_append] using h

theorem readWordsTrace (q : Nat) (words : List Nat) (completed : Fin (q + 1))
    (complete : completed.val + words.length = q) (base : Tape → List Bool)
    (suffix reversed : List Bool) (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWords words ++ suffix) reversed⟩) =
      some ⟨some .reverseTable, (ambient, none),
        tapes base suffix ((encodeWords words).reverse ++ reversed)⟩ := by
  induction words generalizing completed reversed register with
  | nil =>
    have hc : ¬ completed.val < q := by simpa using complete.ge
    simp [encodeWords, MachineComposition.advance, TM2.step, program, hc, TM2.stepAux]
  | cons value words ih =>
    have valid : completed.val < q := by simp only [List.length_cons] at complete; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at complete
      dsimp [next]
      omega
    have first := readWordTrace q completed valid base value (encodeWords words ++ suffix)
      reversed ambient register
    have second := ih next hn ((encodeWord value).reverse ++ reversed) none
    rw [encodeWords, List.length_append, encodeWord_length,
      show value + 1 + (encodeWords words).length + 1 =
        ((encodeWords words).length + 1) + (value + 1) by omega,
      Function.iterate_add_apply]
    simp only [List.append_assoc]
    rw [first]
    simpa only [next, List.reverse_append, List.append_assoc] using second

def finalTapes (base : Tape → List Bool) (suffix bits : List Bool) : Tape → List Bool :=
  Function.update (tapes base suffix []) .permutation (bits ++ base .permutation)

theorem finalTapes_other (base : Tape → List Bool) (suffix bits : List Bool)
    (k : Tape) (hi : k ≠ .input) (hr : k ≠ .permutationReverse) (hp : k ≠ .permutation) :
    finalTapes base suffix bits k = base k := by
  simp [finalTapes, tapes, hi, hr, hp]

@[simp] theorem finalTapes_input (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .input = suffix := by simp [finalTapes]

@[simp] theorem finalTapes_reverse (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .permutationReverse = [] := by simp [finalTapes]

@[simp] theorem finalTapes_permutation (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .permutation = bits ++ base .permutation := by simp [finalTapes]

theorem tableTrace (q : Nat) (words : List Nat) (length : words.length = q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[2 * (encodeWords words).length + 2]
      (some ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords words ++ suffix) []⟩) =
      some ⟨some (rowEntry q), (ambient, none), finalTapes base suffix (encodeWords words)⟩ := by
  have read := readWordsTrace q words 0 (by simpa using length) base suffix [] ambient register
  simp only [List.append_nil] at read
  have reverse := MachineTransfer.transferAt_fromTapes
    Tape.permutationReverse Tape.permutation (by decide) id false
    Label.reverseTable (some (rowEntry q)) (program q) rfl
    (tapes base suffix (encodeWords words).reverse) ambient none
  have finish : MachineTransfer.tapesAt Tape.permutationReverse Tape.permutation
      (tapes base suffix (encodeWords words).reverse) []
      (((tapes base suffix (encodeWords words).reverse) .permutationReverse).reverse.map id ++
        (tapes base suffix (encodeWords words).reverse) .permutation) =
      finalTapes base suffix (encodeWords words) := by
    funext k
    cases k <;> simp [MachineTransfer.tapesAt, tapes, finalTapes]
  rw [finish] at reverse
  simp only [tapes_reverse, List.length_reverse] at reverse
  rw [show 2 * (encodeWords words).length + 2 =
      ((encodeWords words).length + 1) + ((encodeWords words).length + 1) by omega,
    Function.iterate_add_apply, read]
  exact reverse

def tableInTime {q : Nat} (table : Target.PermutationTable q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords (tableWords table) ++ suffix) []⟩
      (some ⟨some (rowEntry q), (ambient, none),
        finalTapes base suffix (encodeWords (tableWords table))⟩)
      (2 * (q * (q + 1)) + 2) where
  steps := 2 * (encodeWords (tableWords table)).length + 2
  evals_in_steps := tableTrace q (tableWords table) (tableWords_length table)
    base suffix ambient register
  steps_le_m := by
    have h := GameEncodingSize.tableBits_length_le table
    omega

end DFVSGames.Explicit.MachineSubdivisionTableRead


namespace DFVSGames.Explicit.MachineSubdivisionBody

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction
open MachineSubdivisionProgram

def tableBits {q : Nat} (table : Target.PermutationTable q) : List Bool :=
  encodeWords (tableWords table)

structure Ready {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Prop where
  input : base .input = encodeWord u ++ encodeWord v ++ tableBits table ++ suffix
  uEmpty : base .u = []
  vEmpty : base .v = []
  permutationEmpty : base .permutation = []
  reverseEmpty : base .permutationReverse = []
  scratchEmpty : base .copyScratch = []

def afterU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .u base u (encodeWord v ++ tableBits table ++ suffix)

def afterV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .v (afterU base u v table suffix) v (tableBits table ++ suffix)

def afterTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineSubdivisionTableRead.finalTapes (afterV base u v table suffix) suffix (tableBits table)

def rowPayload {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : List Bool :=
  MachineFieldTemplate.templateOutput (rowTokens q)
    (fun j => afterTable base u v table suffix (rowField j))

def afterRows {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterTable base u v table suffix) .accumulator
    (rowPayload base u v table suffix)

def afterDrainU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterRows base u v table suffix) .u []

def afterDrainV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainU base u v table suffix) .v []

def afterDrainTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainV base u v table suffix) .permutation []

def incrementTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update base .middle (true :: base .middle))
      .first (true :: true :: base .first))
    .last (true :: true :: base .last)

def bodyResult {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  incrementTapes (afterDrainTable base u v table suffix)

def bodyBudget {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Nat :=
  (u + 2) + (v + 2) + (2 * (q * (q + 1)) + 2) +
    (3 * MachineFieldTemplate.copiedLength (rowTokens q)
      (fun j => afterTable base u v table suffix (rowField j)) + 37) +
    ((afterRows base u v table suffix .u).length + 1) +
    ((afterDrainU base u v table suffix .v).length + 1) +
    ((afterDrainV base u v table suffix .permutation).length + 1) + 1

private theorem rowField_ne_scratch_inline_MachineSubdivisionBody (j : Fin 6) : rowField j ≠ Tape.copyScratch := by
  fin_cases j <;> decide

private theorem rowField_ne_accumulator_inline_MachineSubdivisionBody (j : Fin 6) : rowField j ≠ Tape.accumulator := by
  fin_cases j <;> decide

def incrementInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .increment, initialState, base⟩
      (some ⟨some .guard, initialState, incrementTapes base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .increment) initialState base) = _
    simp [program, TM2.stepAux, incrementTapes, initialState]
  steps_le_m := Nat.le_refl _

def bodyInTime {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .startU, initialState, base⟩
      (some ⟨some .guard, initialState, bodyResult base u v table suffix⟩)
      (bodyBudget base u v table suffix) := by
  have hu : base .input = encodeWord u ++ (encodeWord v ++ tableBits table ++ suffix) := by
    simpa only [List.append_assoc] using ready.input
  let p₀ := SourceMachine.fieldInTime Tape.input Tape.u (by decide)
    Label.startU Label.readU (some .startV) (program q) rfl rfl base u
    (encodeWord v ++ tableBits table ++ suffix) hu ((), ()) none
  have hv : afterU base u v table suffix .input =
      encodeWord v ++ (tableBits table ++ suffix) := by
    simp [afterU, SourceMachine.afterField, SourceMachine.fieldTapes, List.append_assoc]
  let p₁ := SourceMachine.fieldInTime Tape.input Tape.v (by decide)
    Label.startV Label.readV (some (.readTable 0)) (program q) rfl rfl
    (afterU base u v table suffix) v (tableBits table ++ suffix) hv ((), ()) none
  have tableStart : MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
      (tableBits table ++ suffix) [] = afterV base u v table suffix := by
    funext k
    cases k <;> simp [MachineSubdivisionTableRead.tapes, afterV, afterU,
      SourceMachine.afterField, SourceMachine.fieldTapes, ready.reverseEmpty]
  have p₂ : StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), initialState, afterV base u v table suffix⟩
      (some ⟨some (rowEntry q), initialState, afterTable base u v table suffix⟩)
      (2 * (q * (q + 1)) + 2) := by
    have h := MachineSubdivisionTableRead.tableInTime table
      (afterV base u v table suffix) suffix ((), ()) none
    change StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨_, _, MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
        (tableBits table ++ suffix) []⟩ _ _ at h
    rw [tableStart] at h
    exact h
  have scratch : afterTable base u v table suffix .copyScratch = [] := by
    simp [afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
      afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, ready.scratchEmpty]
  let p₃ := MachineFieldTemplate.phaseInTime (rowTokens q) rowField
    Tape.copyScratch Tape.accumulator rowField_ne_scratch_inline_MachineSubdivisionBody rowField_ne_accumulator_inline_MachineSubdivisionBody (by decide)
    Label.emitRows (some .drainU) (program q) (fun _ => rfl)
    (afterTable base u v table suffix) scratch initialState
  let p₄ := MachineDrain.drainInTime Tape.u Label.drainU (some .drainV)
    (program q) rfl (afterRows base u v table suffix) ((), ()) none
  let p₅ := MachineDrain.drainInTime Tape.v Label.drainV (some .drainPermutation)
    (program q) rfl (afterDrainU base u v table suffix) ((), ()) none
  let p₆ := MachineDrain.drainInTime Tape.permutation Label.drainPermutation (some .increment)
    (program q) rfl (afterDrainV base u v table suffix) ((), ()) none
  let p₇ := incrementInTime q (afterDrainTable base u v table suffix)
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅
  let p₀₁₂₃₄₅₆ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆
  let full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅₆ p₇
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      have h := full.steps_le_m
      have tokens_length : (rowTokens q).length = 12 := rfl
      unfold bodyBudget
      omega
  }

end DFVSGames.Explicit.MachineSubdivisionBody


namespace DFVSGames.Explicit.MachineSubdivisionLoopFrame

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

def bodyBits {n q : Nat} (edges : List (Constraint n q)) : List Bool :=
  encodeWords (edges.flatMap constraintWords)

@[simp] theorem bodyBits_nil {n q : Nat} : bodyBits ([] : List (Constraint n q)) = [] := rfl

theorem bodyBits_cons {n q : Nat} (edge : Constraint n q) (edges : List (Constraint n q)) :
    bodyBits (edge :: edges) =
      encodeWord edge.source.val ++ encodeWord edge.target.val ++
        MachineSubdivisionBody.tableBits edge.permutation ++ bodyBits edges := by
  simp [bodyBits, constraintWords, encodeWords, MachineSubdivisionBody.tableBits,
    List.append_assoc]

def identityBits (q : Nat) : List Bool :=
  encodeWords (tableWords (MachineSubdivisionRows.identityTable q))

def rowBits {n q : Nat} (Q e : Nat) (edge : Constraint n q) : List Bool :=
  encodeWords [edge.source.val, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e + 1] ++ identityBits q ++
  encodeWords [edge.target.val, n + Q + 2 * e + 1] ++
    MachineSubdivisionBody.tableBits edge.permutation

def outputRows {n q : Nat} (Q : Nat) : Nat → List (Constraint n q) → List Bool
  | _, [] => []
  | e, edge :: edges => rowBits Q e edge ++ outputRows Q (e + 1) edges

def frame {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => bodyBits edges
  | .remaining => encodeWord edges.length
  | .middle => encodeWord (n + e)
  | .first => encodeWord (n + Q + 2 * e)
  | .last => encodeWord (n + Q + 2 * e + 1)
  | .accumulator => emitted.reverse
  | _ => MachineSubdivisionInit.resultTapes n q Q [] tape

def afterGuard {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) : Tape → List Bool :=
  Function.update (frame Q e (edge :: edges) emitted) .remaining (encodeWord edges.length)

theorem frame_prepared {n q : Nat} (edges : List (Constraint n q)) :
    frame edges.length 0 edges (MachineSubdivisionEmission.headerBits n q edges.length) =
      MachineSubdivisionEmission.resultTapes n q edges.length (bodyBits edges) := by
  funext tape
  cases tape <;> simp [frame, MachineSubdivisionEmission.resultTapes,
    MachineSubdivisionInit.resultTapes]

theorem guard_cons {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    (machine q).step ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ =
      some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩ := by
  have before : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) (edges.length + 1) [] =
      frame Q e (edge :: edges) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e (edge :: edges) emitted) Tape.remaining
      ((frame Q e (edge :: edges) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have after : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) edges.length [] =
      afterGuard Q e edge edges emitted := by
    simp [MachineUnaryCounter.counterTapes, afterGuard]
  have run := MachineUnaryCounter.guardStep_succ Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e (edge :: edges) emitted) edges.length [] ((), ()) none
  rw [before, after] at run
  exact run

theorem guard_nil (n q Q e : Nat) (emitted : List Bool) :
    (machine q).step
      ⟨some .guard, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ =
      some ⟨some .finishStart, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ := by
  have framed : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e ([] : List (Constraint n q)) emitted) 0 [] =
      frame Q e ([] : List (Constraint n q)) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e ([] : List (Constraint n q)) emitted) Tape.remaining
      ((frame Q e ([] : List (Constraint n q)) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have run := MachineUnaryCounter.guardStep_zero Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e ([] : List (Constraint n q)) emitted) [] ((), ()) none
  rw [framed] at run
  exact run

theorem ready {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.Ready (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) := by
  constructor
  · simpa only [afterGuard, Function.update_of_ne (by decide : Tape.input ≠ .remaining),
      frame] using bodyBits_cons edge edges
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]

end DFVSGames.Explicit.MachineSubdivisionLoopFrame


namespace DFVSGames.Explicit.MachineSubdivisionBodySpec

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction
open MachineSubdivisionProgram MachineSubdivisionBody

def resultTapes {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .u | .v | .permutation | .permutationReverse => []
  | .middle => true :: base .middle
  | .first => true :: true :: base .first
  | .last => true :: true :: base .last
  | .accumulator => (rowPayload base u v table suffix).reverse ++ base .accumulator
  | k => base k

theorem bodyResult_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (_ready : Ready base u v table suffix) :
    bodyResult base u v table suffix = resultTapes base u v table suffix := by
  funext k
  cases k <;> simp [bodyResult, incrementTapes, afterDrainTable, afterDrainV,
    afterDrainU, afterRows, MachineFieldTemplate.outputTapes, afterTable,
    MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, resultTapes]

theorem result_input {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .input = suffix := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem result_locals {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .u = [] ∧
    bodyResult base u v table suffix .v = [] ∧
    bodyResult base u v table suffix .permutation = [] ∧
    bodyResult base u v table suffix .permutationReverse = [] ∧
    bodyResult base u v table suffix .copyScratch = [] := by
  rw [bodyResult_eq base u v table suffix ready]
  simp [resultTapes, ready.scratchEmpty]

theorem result_accumulator {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .accumulator =
      (rowPayload base u v table suffix).reverse ++ base .accumulator := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem encodeWord_succ (n : Nat) : encodeWord (n + 1) = true :: encodeWord n := by
  simp [encodeWord, List.replicate_succ]

theorem result_indices {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyResult base u v table suffix .middle = encodeWord (n + (e + 1)) ∧
    bodyResult base u v table suffix .first = encodeWord (n + Q + 2 * (e + 1)) ∧
    bodyResult base u v table suffix .last = encodeWord (n + Q + 2 * (e + 1) + 1) := by
  rw [bodyResult_eq base u v table suffix ready]
  have hm : n + (e + 1) = (n + e) + 1 := by omega
  have hf : n + Q + 2 * (e + 1) = (n + Q + 2 * e) + 1 + 1 := by omega
  have hl : n + Q + 2 * (e + 1) + 1 = (n + Q + 2 * e + 1) + 1 + 1 := by omega
  simp [resultTapes, middle, first, last, hm, hf, encodeWord_succ]

def rowBits {q : Nat} (u middle first last v : Nat) (table : Target.PermutationTable q) :
    List Bool :=
  encodeWords
    ([u, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, last] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [v, last] ++ tableWords table)

theorem rowPayload_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (middle first last : Nat)
    (hm : base .middle = encodeWord middle) (hf : base .first = encodeWord first)
    (hl : base .last = encodeWord last) :
    rowPayload base u v table suffix = rowBits u middle first last v table := by
  simp [rowPayload, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput, rowField,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, hm, hf, hl,
    rowBits, tableBits, encodeWords, List.append_assoc]

theorem rowBits_eq_dynamic {N q : Nat} (vertices : Fin 5 → Fin N)
    (table : Target.PermutationTable q) :
    rowBits (vertices 0).val (vertices 2).val (vertices 1).val (vertices 3).val
      (vertices 4).val table = MachineSubdivisionDynamicRows.rowBits vertices table := by
  simp [rowBits, MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionDynamicRows.rows,
    constraintWords, List.append_assoc]

theorem bodyBudget_le {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (hu : u < n) (hv : v < n) (he : e ≤ Q)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyBudget base u v table suffix ≤ 100 * (n + 3 * Q + q * (q + 1) + 1) := by
  have ht : (tableBits table).length ≤ q * (q + 1) :=
    GameEncodingSize.tableBits_length_le table
  simp [bodyBudget, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.copiedLength, rowField,
    afterDrainV, afterDrainU, afterRows, MachineFieldTemplate.outputTapes,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, middle, first, last] at *
  omega

end DFVSGames.Explicit.MachineSubdivisionBodySpec

end OAI
