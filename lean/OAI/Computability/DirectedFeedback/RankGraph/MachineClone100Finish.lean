import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.MachineClone100Cleanup

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

namespace DFVSGames.Explicit.MachineClone100Finish

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
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

end DFVSGames.Explicit.MachineClone100Finish
end

section

namespace DFVSGames.Explicit.MachineClone100Run

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
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

end DFVSGames.Explicit.MachineClone100Run
end

section

namespace DFVSGames.Explicit.MachineClone100Certified

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity

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

end DFVSGames.Explicit.MachineClone100Certified
end

section

namespace DFVSGames.Explicit.MachineClone100

open Turing DFVSGames.Reduction
open DFVSGames.Foundations.Complexity

noncomputable section

def indices (t : Outer.Clone100Triples.GoodTriple) : Nat × Nat × Nat :=
  (t.val.1.val, t.val.2.1.val, t.val.2.2.val)

def triples : List (Nat × Nat × Nat) := Outer.Clone100.triples.map indices

theorem triples_length : triples.length = 970200 := by
  simp [triples, Outer.Clone100.triples_length]

theorem triples_nonempty : triples ≠ [] := by
  apply List.length_pos_iff.mp
  rw [triples_length]
  decide

theorem equation_words {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Outer.Clone100Triples.GoodTriple) :
    SourceEncoding.equationWords (Outer.Clone100.equation e t) =
      MachineClone100Table.cloneEquationWords e (indices t) := by
  simp [SourceEncoding.equationWords, Outer.Clone100.equation,
    Outer.Clone100.nameEquiv, finProdFinEquiv,
    MachineClone100Table.cloneEquationWords, indices, Nat.mul_comm]

theorem body_words {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    (Outer.Clone100.equations es).flatMap SourceEncoding.equationWords =
      es.flatMap (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [Outer.Clone100.equations, List.flatMap_assoc, List.flatMap_map,
    equation_words, triples]

theorem input_words_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputWords (Outer.Clone100.clonedInput input) =
      [100 * input.«variables», triples.length * input.equations.length] ++
        input.equations.flatMap
          (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [SourceEncoding.inputWords, Outer.Clone100.clonedInput,
    Outer.Clone100.equations_length, body_words, triples_length]
  simp [Nat.mul_comm]

theorem input_bits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits (Outer.Clone100.clonedInput input) =
      MachineClone100Run.outputBits triples input := by
  rw [SourceEncoding.inputBits, input_words_eq, encodeWords_append]
  rfl

private theorem serialized_polynomial_inline_MachineClone100 (D N n m : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    n * 100 + m * D + 2 + m * D * (300 * n + 2) ≤
      (300 * D) * N * N + (100 + 3 * D) * N + 2 := by
  have hproduct := Nat.mul_le_mul_left (300 * D) (Nat.mul_le_mul hm hn)
  have hvariables := Nat.mul_le_mul_left 100 hn
  have hoccurrences := Nat.mul_le_mul_left (3 * D) hm
  calc
    _ = (300 * D) * (m * n) + 100 * n + (3 * D) * m + 2 := by ring
    _ ≤ (300 * D) * (N * N) + 100 * N + (3 * D) * N + 2 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hproduct hvariables) hoccurrences)
        (Nat.le_refl 2)
    _ = _ := by ring

theorem size_bound (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (Outer.Clone100.clonedInput input)).length ≤
      (300 * triples.length) * (SourceEncoding.inputBits input).length *
        (SourceEncoding.inputBits input).length +
      (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2 := by
  rw [triples_length]
  exact (Outer.Clone100.clonedInput_bits_length_le input).trans
    (serialized_polynomial_inline_MachineClone100 970200 (SourceEncoding.inputBits input).length
      input.«variables» input.equations.length
      (SourceEncoding.inputBits_length_ge_variables input)
      (SourceEncoding.inputBits_length_ge_equations input))

def computation : TM2ComputableInPolyTime SourceEncoding.inputBits
    SourceEncoding.inputBits Outer.Clone100.clonedInput :=
  MachineClone100Certified.certifiedFunction triples triples_nonempty
    Outer.Clone100.clonedInput input_bits_eq size_bound

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

def fullRunInTime (input : SourceEncoding.Input) := computation.outputsFun input

end

end DFVSGames.Explicit.MachineClone100
end

section

namespace DFVSGames.BinaryValidatorMachine

open BinaryEncoding BinaryFormula

inductive Mode
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3) (last : Bool)
  | digit (slot : Fin 3)
  | done
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Mode :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

def nextMode : Mode → Bool → Mode
  | .clause, true => .sign 0
  | .clause, false => .done
  | .sign slot, _ => .name slot true
  | .name slot _, true => .digit slot
  | .name slot last, false => if last then afterName slot else .reject
  | .digit slot, bit => .name slot bit
  | .done, _ => .reject
  | .reject, _ => .reject

def run : Mode → List Bool → Mode
  | mode, [] => mode
  | mode, bit :: rest => run (nextMode mode bit) rest

@[simp] theorem run_reject (input : List Bool) : run .reject input = .reject := by
  induction input with
  | nil => rfl
  | cons bit input ih => simpa only [run, nextMode] using ih

theorem run_done_iff (input : List Bool) : run .done input = .done ↔ input = [] := by
  cases input with
  | nil => simp [run]
  | cons bit rest => simp [run, nextMode]

private theorem finalDigit_true_iff_inline_MachineBinaryValidatorMachine (bits : List Bool) :
    BinaryNameMachine.finalDigit bits (some true) = some true ↔
      BinaryNameMachine.canonical bits = true := by
  cases bits with
  | nil => simp [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
  | cons bit bits =>
      simp only [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
      have hsome : ∀ (ds : List Bool) (b : Bool),
          ∃ last, BinaryNameMachine.finalDigit ds (some b) = some last := by
        intro ds
        induction ds with
        | nil => intro b; exact ⟨b, rfl⟩
        | cons d ds ih => intro b; exact ih d
      obtain ⟨last, hlast⟩ := hsome bits bit
      rw [hlast]
      simp

theorem run_frame (slot : Fin 3) (bits rest : List Bool) (last : Bool)
    (valid : BinaryNameMachine.finalDigit bits (some last) = some true) :
    run (.name slot last) (frame bits ++ rest) = run (afterName slot) rest := by
  induction bits generalizing last with
  | nil =>
      have hlast : last = true := by simpa [BinaryNameMachine.finalDigit] using valid
      subst last
      simp [frame, run, nextMode]
  | cons bit bits ih =>
      have hvalid : BinaryNameMachine.finalDigit bits (some bit) = some true := valid
      simpa only [frame, List.cons_append, run, nextMode] using ih bit hvalid

theorem run_name (slot : Fin 3) (name : Nat) (rest : List Bool) :
    run (.name slot true) (nameBits name ++ rest) = run (afterName slot) rest := by
  apply run_frame
  exact (finalDigit_true_iff_inline_MachineBinaryValidatorMachine name.bits).mpr (BinaryParsing.canonical_nat_bits name)

theorem run_literal (slot : Fin 3) (literal : Literal) (rest : List Bool) :
    run (.sign slot) (literalBits literal ++ rest) = run (afterName slot) rest := by
  simpa only [literalBits, List.cons_append, run, nextMode] using
    run_name slot literal.name rest

theorem run_clause (clause : Clause) (rest : List Bool) :
    run (.sign 0) (clauseBits clause ++ rest) = run .clause rest := by
  simp [clauseBits, List.append_assoc, run_literal, afterName]

theorem run_clauses (clauses : List Clause) : run .clause (clausesBits clauses) = .done := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      change run (.sign 0) (clauseBits clause ++ clausesBits clauses) = .done
      rw [run_clause, ih]

theorem run_formula (formula : Formula) : run .clause (formulaBits formula) = .done :=
  run_clauses formula.clauses

theorem frame_inverse (slot : Fin 3) (last : Bool) (input : List Bool)
    (accepted : run (.name slot last) input = .done) :
    ∃ bits rest, input = frame bits ++ rest ∧
      BinaryNameMachine.finalDigit bits (some last) = some true ∧
      run (afterName slot) rest = .done := by
  induction input using List.twoStepInduction generalizing last with
  | nil => simp [run] at accepted
  | singleton flag =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], [], rfl, rfl, by simpa [run, nextMode] using accepted⟩
      | true => simp [run, nextMode] at accepted
  | cons_cons flag bit input ih _ =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], bit :: input, rfl, rfl,
                by simpa [run, nextMode] using accepted⟩
      | true =>
          have haccepted : run (.name slot bit) input = .done := by
            simpa only [run, nextMode] using accepted
          obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := ih bit haccepted
          refine ⟨bit :: bits, rest, ?_, hvalid, hrest⟩
          simp [frame, hinput]

theorem name_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.name slot true) input = .done) :
    ∃ name rest, input = nameBits name ++ rest ∧ run (afterName slot) rest = .done := by
  obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := frame_inverse slot true input accepted
  have hcanonical := (finalDigit_true_iff_inline_MachineBinaryValidatorMachine bits).mp hvalid
  have hbits := (BinaryParsing.canonical_iff bits).mp hcanonical
  refine ⟨bitsValue bits, rest, ?_, hrest⟩
  simpa only [nameBits, hbits] using hinput

theorem literal_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.sign slot) input = .done) :
    ∃ literal rest, input = literalBits literal ++ rest ∧ run (afterName slot) rest = .done := by
  cases input with
  | nil => simp [run] at accepted
  | cons sign input =>
      have haccepted : run (.name slot true) input = .done := accepted
      obtain ⟨name, rest, hinput, hrest⟩ := name_inverse slot input haccepted
      refine ⟨⟨name, sign⟩, rest, ?_, hrest⟩
      simp [literalBits, hinput]

theorem clause_inverse (input : List Bool) (accepted : run (.sign 0) input = .done) :
    ∃ clause rest, input = clauseBits clause ++ rest ∧ run .clause rest = .done := by
  obtain ⟨a, afterA, hA, acceptedA⟩ := literal_inverse 0 input accepted
  have hacceptedA : run (.sign 1) afterA = .done := by
    simpa [afterName] using acceptedA
  obtain ⟨b, afterB, hB, acceptedB⟩ := literal_inverse 1 afterA hacceptedA
  have hacceptedB : run (.sign 2) afterB = .done := by
    simpa [afterName] using acceptedB
  obtain ⟨c, rest, hC, acceptedC⟩ := literal_inverse 2 afterB hacceptedB
  have hrest : run .clause rest = .done := by simpa [afterName] using acceptedC
  refine ⟨#v[a, b, c], rest, ?_, hrest⟩
  simp [clauseBits, hA, hB, hC, List.append_assoc]

private theorem clauses_inverse_aux_inline_MachineBinaryValidatorMachine (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .clause input = .done) :
    ∃ clauses, input = clausesBits clauses := by
  induction fuel generalizing input with
  | zero => omega
  | succ fuel ih =>
      cases input with
      | nil => simp [run] at accepted
      | cons flag input =>
          cases flag with
          | false =>
              have hdone : run .done input = .done := accepted
              have hempty := (run_done_iff input).mp hdone
              subst input
              exact ⟨[], rfl⟩
          | true =>
              have haccepted : run (.sign 0) input = .done := accepted
              obtain ⟨clause, rest, hinput, hrest⟩ := clause_inverse input haccepted
              have hlength := congrArg List.length hinput
              simp only [List.length_append] at hlength
              have henough : rest.length < fuel := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨clauses, hclauses⟩ := ih rest henough hrest
              refine ⟨clause :: clauses, ?_⟩
              simp [clausesBits, hinput, hclauses]

theorem run_clause_iff (input : List Bool) :
    run .clause input = .done ↔ ∃ formula, input = formulaBits formula := by
  constructor
  · intro accepted
    obtain ⟨clauses, hclauses⟩ :=
      clauses_inverse_aux_inline_MachineBinaryValidatorMachine (input.length + 1) input (by omega) accepted
    exact ⟨⟨clauses⟩, hclauses⟩
  · rintro ⟨formula, rfl⟩
    exact run_formula formula

def accepts (input : List Bool) : Bool := decide (run .clause input = .done)

theorem accepts_eq_decode (input : List Bool) :
    accepts input = (decodeFormula input).isSome := by
  cases parsed : decodeFormula input with
  | none =>
      have rejected : run .clause input ≠ .done := by
        intro accepted
        obtain ⟨formula, encoded⟩ := (run_clause_iff input).mp accepted
        have roundtrip := decodeFormula_encoded formula
        rw [← encoded, parsed] at roundtrip
        cases roundtrip
      simp [accepts, rejected]
  | some formula =>
      have encoded := BinaryParsing.decodeFormula_sound input formula parsed
      have accepted := (run_clause_iff input).mpr ⟨formula, encoded⟩
      simp [accepts, accepted]

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

abbrev Alphabet (_ : Bool) := Bool
abbrev State := Mode × Option Bool

def instruction : TM2.Stmt Alphabet Unit State :=
  .pop false (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => (nextMode state.1 (state.2.getD false), none))
        (.goto fun _ => ()))
      (.push true (fun state => decide (state.1 = .done))
        (.load (fun _ => (.clause, none)) .halt)))

abbrev machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Alphabet
  Λ := Unit
  main := ()
  σ := State
  initialState := (.clause, none)
  m _ := instruction

def tapes (input output : List Bool) : Bool → List Bool
  | false => input
  | true => output

def cfg (label : Option Unit) (input output : List Bool) (mode : Mode)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input output⟩

@[simp] theorem tapes_input (input output : List Bool) :
    tapes input output false = input := rfl

@[simp] theorem tapes_output (input output : List Bool) :
    tapes input output true = output := rfl

private theorem update_input_inline_MachineBinaryValidatorMachine (input output replacement : List Bool) :
    Function.update (tapes input output) false replacement = tapes replacement output := by
  funext k
  cases k <;> rfl

private theorem update_output_inline_MachineBinaryValidatorMachine (input output replacement : List Bool) :
    Function.update (tapes input output) true replacement = tapes input replacement := by
  funext k
  cases k <;> rfl

theorem step_empty (mode : Mode) (output : List Bool) (register : Option Bool) :
    machine.step (cfg (some ()) [] output mode register) =
      some (cfg none [] (decide (mode = .done) :: output) .clause) := by
  change some (TM2.stepAux instruction _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryValidatorMachine, update_output_inline_MachineBinaryValidatorMachine]
  rfl

theorem step_cons (mode : Mode) (bit : Bool) (input output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some ()) (bit :: input) output mode register) =
      some (cfg (some ()) input output (nextMode mode bit)) := by
  change some (TM2.stepAux instruction _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryValidatorMachine]
  rfl

theorem runTrace (input output : List Bool) (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some ()) input output mode register)) =
      some (cfg none [] (decide (run mode input = .done) :: output) .clause) := by
  induction input generalizing mode register with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run]
      exact step_empty mode output register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_cons]
      exact ih (nextMode mode bit) none

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some ()) input [] .clause := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] output .clause := by
  unfold haltList cfg
  congr 1
  funext k
  cases k <;> rfl

theorem validatorTrace (input : List Bool) :
    (advance machine.step)^[input.length + 1]
      (some (initList machine input)) =
      some (haltList machine [(BinaryEncoding.decodeFormula input).isSome]) := by
  rw [initList_eq, haltList_eq]
  have h := runTrace input [] .clause none
  change (advance machine.step)^[input.length + 1]
    (some (cfg (some ()) input [] .clause)) =
    some (cfg none [] [accepts input] .clause) at h
  rw [accepts_eq_decode] at h
  exact h

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input (some [(BinaryEncoding.decodeFormula input).isSome])
      (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := validatorTrace input
  steps_le_m := Nat.le_refl _

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun input => [(BinaryEncoding.decodeFormula input).isSome]) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id)
      (some ([(BinaryEncoding.decodeFormula input).isSome].map id))
      ((Polynomial.X + 1 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one] using outputsInTime input

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end DFVSGames.BinaryValidatorMachine

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
