import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineBinaryLiteralMachine
import OAI.Computability.DirectedFeedback.Machines.MachineBinaryTokenMachine

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

namespace DFVSGames.BinaryRenameMachine

open Turing DFVSGames.Foundations
open Complexity Complexity.MachineComposition
open DFVSGames.Reduction.MachineTransfer

abbrev Tape := Fin 12
abbrev Alphabet (_ : Tape) := Bool
abbrev State := BinaryRenameLoop.State Unit

inductive Label
  | copyOut | copyBack
  | loop (label : BinaryRenameLoop.Label)
  | restore | clauseStart | clauseLoop | variableStart | variableLoop
  | cleanup | reject
  deriving DecidableEq, Fintype

def loopTapes : Fin 11 → Tape := Fin.castSucc

theorem loopTapes_injective : Function.Injective loopTapes := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Tape => k.val) h

def program : Label → TM2.Stmt Alphabet Label State
  | .copyOut => loopAt 1 6 id false .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop 6 1 0 false .copyBack (some (.loop .entry))
  | .loop label => BinaryRenameLoop.instruction loopTapes Label.loop
      (some .restore) (some .reject) label
  | .restore => loopAt 8 11 id false .restore (some .clauseStart)
  | .clauseStart => BinaryHeaderMachine.delimiter 11 .clauseLoop
  | .clauseLoop => loopAt 10 11 id false .clauseLoop (some .variableStart)
  | .variableStart => BinaryHeaderMachine.delimiter 11 .variableLoop
  | .variableLoop => loopAt 9 11 id false .variableLoop (some .cleanup)
  | .cleanup => MachineDrain.drain 1 .cleanup none
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 1
  k₁ := 11
  Γ := Alphabet
  Λ := Label
  main := .copyOut
  σ := State
  initialState := BinaryRenameLoop.clean () 0
  m := program

def tapes (permanent cursor reversed variableCounter clauseCounter output : List Bool) :
    Tape → List Bool := fun k =>
  if k = 0 then cursor
  else if k = 1 then permanent
  else if k = 8 then reversed
  else if k = 9 then variableCounter
  else if k = 10 then clauseCounter
  else if k = 11 then output
  else []

def cfg (label : Option Label)
    (permanent cursor reversed variableCounter clauseCounter output : List Bool) : machine.Cfg :=
  ⟨label, BinaryRenameLoop.clean () 0,
    tapes permanent cursor reversed variableCounter clauseCounter output⟩

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .copyOut) input [] [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] [] [] [] [] output := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem copyTrace (input : List Bool) :
    (advance machine.step)^[2 * (input.length + 1)]
      (some (cfg (some .copyOut) input [] [] [] [] [])) =
      some (cfg (some (.loop .entry)) input input [] [] [] []) := by
  have updated : Function.update (tapes input [] [] [] [] []) 0 input =
      tapes input input [] [] [] [] := by
    funext k
    fin_cases k <;> simp [tapes]
  have h := MachineCopy.copyTrace (1 : Tape) 0 6 (by decide) (by decide) (by decide)
    false .copyOut .copyBack (some (.loop .entry)) program rfl rfl
    (tapes input [] [] [] [] []) (by simp [tapes])
    (BinaryRenameLoop.clean () 0).1 none
  have first : tapes input [] [] [] [] [] 1 = input := rfl
  have second : tapes input [] [] [] [] [] 0 = [] := rfl
  rw [first, second, List.append_nil, updated] at h
  exact h

theorem restoreTrace (input body variableCounter clauseCounter : List Bool) :
    (advance machine.step)^[body.length + 1]
      (some (cfg (some .restore) input [] body.reverse variableCounter clauseCounter [])) =
      some (cfg (some .clauseStart) input [] [] variableCounter clauseCounter body) := by
  change (nextAt (11 : Tape) program)^[body.length + 1]
    (some (cfg (some .restore) input [] body.reverse variableCounter clauseCounter [])) = _
  have updated : tapesAt (8 : Tape) 11
      (tapes input [] body.reverse variableCounter clauseCounter []) [] body =
      tapes input [] [] variableCounter clauseCounter body := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  have h := transferAt_fromTapes (Γ := Alphabet) (8 : Tape) 11 (by decide) id false
    .restore (some .clauseStart) program rfl
    (tapes input [] body.reverse variableCounter clauseCounter [])
    (BinaryRenameLoop.clean () 0).1 none
  have source : tapes input [] body.reverse variableCounter clauseCounter [] 8 = body.reverse := rfl
  have output : tapes input [] body.reverse variableCounter clauseCounter [] 11 = [] := rfl
  rw [source, output, List.length_reverse, List.reverse_reverse, List.map_id_fun,
    List.append_nil, id_eq, updated] at h
  exact h

theorem headerTrace (input body : List Bool) (n m : Nat) :
    (advance machine.step)^[n + m + 4]
      (some (cfg (some .clauseStart) input [] []
        (List.replicate n true) (List.replicate m true) body)) =
      some (cfg (some .cleanup) input [] [] [] []
        (encodeWord n ++ encodeWord m ++ body)) := by
  change (advance (TM2.step program))^[n + m + 4]
    (some ⟨some .clauseStart, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] (List.replicate n true) (List.replicate m true) body⟩) =
    some ⟨some .cleanup, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] [] [] (encodeWord n ++ encodeWord m ++ body)⟩
  have updated (variableWord clauses output : List Bool) :
      BinaryHeaderMachine.tapes (9 : Tape) 10 11 (tapes input [] [] [] [] [])
        variableWord clauses output = tapes input [] [] variableWord clauses output := by
    funext k
    fin_cases k <;> simp [BinaryHeaderMachine.tapes, tapes]
  have h := BinaryHeaderMachine.headerTrace (9 : Tape) 10 11
    (by decide) (by decide) (by decide)
    .clauseStart .clauseLoop .variableStart .variableLoop (some .cleanup) program
    rfl rfl rfl rfl (tapes input [] [] [] [] [])
    (BinaryRenameLoop.clean () 0).1 n m body none
  simp only [updated] at h
  exact h

theorem cleanupTrace (input output : List Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .cleanup) input [] [] [] [] output)) =
      some (cfg none [] [] [] [] [] output) := by
  change (advance (TM2.step program))^[input.length + 1]
    (some ⟨some .cleanup, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] [] [] output⟩) =
    some ⟨none, ((BinaryRenameLoop.clean () 0).1, none), tapes [] [] [] [] [] output⟩
  have updated (word : List Bool) :
      Function.update (tapes [] [] [] [] [] output) 1 word =
        tapes word [] [] [] [] output := by
    funext k
    fin_cases k <;> simp [tapes]
  have h := MachineDrain.drainTrace (1 : Tape) .cleanup none program rfl
    (tapes [] [] [] [] [] output) input (BinaryRenameLoop.clean () 0).1 none
  simp only [updated] at h
  exact h

theorem outputBody_eq (formula : BinaryFormula.Formula) :
    BinaryRenameLoop.outputBody (BinaryRenameWords.tokens formula.clauses)
      (BinaryRenameWords.tokens formula.clauses) = BinaryRenameWords.body formula := by
  change ((BinaryRenameWords.literals formula.clauses).map BinaryRenameWords.token).flatMap
    (fun t => BinaryLiteralMachine.outputWord (BinaryRenameWords.tokens formula.clauses)
      t.2 t.1) = (BinaryRenameWords.literals formula.clauses).flatMap
        (BinaryRenameWords.outputLiteral (BinaryFormula.sourceNames formula))
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro literal _
  simp only [BinaryRenameWords.token, BinaryLiteralMachine.outputWord,
    BinaryLiteralMachine.index, BinaryLiteralMachine.signWord,
    BinaryRenameWords.payload_index, BinaryRenameWords.outputLiteral]
  rfl

theorem loopTrace (formula : BinaryFormula.Formula) :
    (advance machine.step)^[BinaryRenameLoop.steps (BinaryRenameWords.tokens formula.clauses)
        (BinaryRenameWords.tokens formula.clauses)]
      (some (cfg (some (.loop .entry)) (BinaryTokenMachine.tokens formula.clauses)
        (BinaryTokenMachine.tokens formula.clauses) [] [] [] [])) =
      some (cfg (some .restore) (BinaryTokenMachine.tokens formula.clauses) []
        (BinaryRenameWords.body formula).reverse (List.replicate (3 * formula.clauses.length) true)
        (List.replicate formula.clauses.length true) []) := by
  change (advance (TM2.step program))^[BinaryRenameLoop.steps
      (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)]
    (some ⟨some (.loop .entry), BinaryRenameLoop.clean () 0,
      tapes (BinaryTokenMachine.tokens formula.clauses) (BinaryTokenMachine.tokens formula.clauses)
        [] [] [] []⟩) =
    some ⟨some .restore, BinaryRenameLoop.clean () 0,
      tapes (BinaryTokenMachine.tokens formula.clauses) [] (BinaryRenameWords.body formula).reverse
        (List.replicate (3 * formula.clauses.length) true)
        (List.replicate formula.clauses.length true) []⟩
  let input := BinaryTokenMachine.tokens formula.clauses
  have updated (cursor output variableWord clauseWord : List Bool) :
      BinaryRenameLoop.loopTapes loopTapes (tapes input [] [] [] [] [])
        cursor output variableWord clauseWord =
      tapes input cursor output variableWord clauseWord [] := by
    funext k
    fin_cases k <;> simp [BinaryRenameLoop.loopTapes, loopTapes, tapes]
  have scratch (i : Fin 11) (lo : 2 ≤ i.val) (hi : i.val ≤ 7) :
      tapes input [] [] [] [] [] (loopTapes i) = [] := by
    have n0 : loopTapes i ≠ 0 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n1 : loopTapes i ≠ 1 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n8 : loopTapes i ≠ 8 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n9 : loopTapes i ≠ 9 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n10 : loopTapes i ≠ 10 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n11 : loopTapes i ≠ 11 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    simp [tapes, n0, n1, n8, n9, n10, n11]
  have run := BinaryRenameLoop.triplesTrace loopTapes loopTapes_injective Label.loop
    (some .restore) (some .reject) program (fun _ => rfl)
    (tapes input [] [] [] [] []) ()
    (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)
    formula.clauses.length (BinaryRenameWords.tokens_length formula.clauses) [] [] []
    (BinaryRenameWords.tokens_canonical formula.clauses) (fun _ h => h)
    (by change input = _; rw [BinaryRenameWords.tokens_stream]) scratch
  simp only [updated, BinaryRenameWords.tokens_stream, outputBody_eq, List.append_nil, input] at run
  exact run

private theorem joinTrace_inline_MachineBinaryRenameMachine {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def steps (formula : BinaryFormula.Formula) : Nat :=
  2 * ((BinaryTokenMachine.tokens formula.clauses).length + 1) +
    BinaryRenameLoop.steps (BinaryRenameWords.tokens formula.clauses)
      (BinaryRenameWords.tokens formula.clauses) +
    ((BinaryRenameWords.body formula).length + 1) + (4 * formula.clauses.length + 4) +
    ((BinaryTokenMachine.tokens formula.clauses).length + 1)

theorem renameTrace (formula : BinaryFormula.Formula) :
    (advance machine.step)^[steps formula]
      (some (initList machine (BinaryTokenMachine.tokens formula.clauses))) =
      some (haltList machine (formulaBits (BinaryOccurrenceRename.renamed formula))) := by
  have first := copyTrace (BinaryTokenMachine.tokens formula.clauses)
  have second := loopTrace formula
  have third := restoreTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (List.replicate (3 * formula.clauses.length) true)
    (List.replicate formula.clauses.length true)
  have fourth := headerTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (3 * formula.clauses.length) formula.clauses.length
  have fifth := cleanupTrace (BinaryTokenMachine.tokens formula.clauses)
    (encodeWord (3 * formula.clauses.length) ++ encodeWord formula.clauses.length ++
      BinaryRenameWords.body formula)
  have full := joinTrace_inline_MachineBinaryRenameMachine (joinTrace_inline_MachineBinaryRenameMachine (joinTrace_inline_MachineBinaryRenameMachine (joinTrace_inline_MachineBinaryRenameMachine first second) third) fourth) fifth
  have count : 3 * formula.clauses.length + formula.clauses.length + 4 =
      4 * formula.clauses.length + 4 := by omega
  simpa only [steps, initList_eq, haltList_eq, BinaryRenameWords.encoded_renamed, count] using full

theorem clause_count_le_stream (formula : BinaryFormula.Formula) :
    formula.clauses.length ≤ (BinaryTokenMachine.tokens formula.clauses).length := by
  rw [BinaryTokenMachine.tokens_length]
  omega

theorem body_length_le (formula : BinaryFormula.Formula) :
    (BinaryRenameWords.body formula).length ≤
      9 * (BinaryTokenMachine.tokens formula.clauses).length ^ 2 +
        10 * (BinaryTokenMachine.tokens formula.clauses).length + 2 := by
  have initial := BinaryOccurrenceRename.renamed_encoding_bound formula
  rw [BinaryRenameWords.encoded_renamed] at initial
  simp only [List.length_append] at initial
  have count := clause_count_le_stream formula
  have square := Nat.mul_self_le_mul_self count
  nlinarith

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 12 * Polynomial.X ^ 3 + Polynomial.C 35 * Polynomial.X ^ 2 +
    Polynomial.C 28 * Polynomial.X + Polynomial.C 11

theorem steps_le (formula : BinaryFormula.Formula) :
    steps formula ≤ timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length := by
  have loopBound := BinaryRenameLoop.steps_le
    (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)
    (fun _ h => h)
  rw [BinaryRenameWords.tokens_stream, BinaryRenameWords.tokens_length] at loopBound
  have literalCount : 3 * formula.clauses.length ≤
      (BinaryTokenMachine.tokens formula.clauses).length := by
    rw [BinaryTokenMachine.tokens_length]
    omega
  have product := Nat.mul_le_mul_left
    (BinaryRenameLoop.perLiteralBound (BinaryTokenMachine.tokens formula.clauses).length)
    literalCount
  have output := body_length_le formula
  have count := clause_count_le_stream formula
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold steps BinaryRenameLoop.perLiteralBound at *
  nlinarith

def outputsInTime (formula : BinaryFormula.Formula) :
    TM2OutputsInTime machine (BinaryTokenMachine.tokens formula.clauses)
      (some (formulaBits (BinaryOccurrenceRename.renamed formula)))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length) where
  steps := steps formula
  evals_in_steps := renameTrace formula
  steps_le_m := steps_le formula

noncomputable def tokenComputation :
    TM2ComputableInPolyTime (fun formula : BinaryFormula.Formula =>
      BinaryTokenMachine.tokens formula.clauses) formulaBits BinaryOccurrenceRename.renamed where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun formula := by
    change TM2OutputsInTime machine ((BinaryTokenMachine.tokens formula.clauses).map id)
      (some ((formulaBits (BinaryOccurrenceRename.renamed formula)).map id))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length)
    simpa only [List.map_id_fun, id_eq] using outputsInTime formula

noncomputable def preprocessing :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits
      (fun formula : BinaryFormula.Formula => BinaryTokenMachine.tokens formula.clauses)
      (id : BinaryFormula.Formula → BinaryFormula.Formula) where
  tm := BinaryTokenMachine.computableInPolyTime.tm
  inputAlphabet := BinaryTokenMachine.computableInPolyTime.inputAlphabet
  outputAlphabet := BinaryTokenMachine.computableInPolyTime.outputAlphabet
  time := BinaryTokenMachine.computableInPolyTime.time
  outputsFun := BinaryTokenMachine.computableInPolyTime.outputsFun

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits formulaBits
      BinaryOccurrenceRename.renamed :=
  MachineSequential.composeBits preprocessing tokenComputation

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  MachineFiniteAlphabet.composeBits preprocessing tokenComputation
    BinaryTokenMachine.machine_finiteAlphabet machine_finiteAlphabet

end DFVSGames.BinaryRenameMachine

end

section

namespace DFVSGames.Foundations.Complexity.CookLevin

def pairBits (input : List Bool × List Bool) : List Bool :=
  encodeWord input.1.length ++ input.1 ++ input.2

def decodePairAux : Nat → List Bool → Option (List Bool × List Bool)
  | _, [] => none
  | read, true :: rest => decodePairAux (read + 1) rest
  | read, false :: rest =>
      if read ≤ rest.length then some (rest.take read, rest.drop read) else none

def decodePair (bits : List Bool) : Option (List Bool × List Bool) :=
  decodePairAux 0 bits

theorem decodePairAux_frame (read count : Nat) (rest : List Bool) :
    decodePairAux read (List.replicate count true ++ false :: rest) =
      if read + count ≤ rest.length then
        some (rest.take (read + count), rest.drop (read + count)) else none := by
  induction count generalizing read with
  | zero => simp [decodePairAux]
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, decodePairAux, ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 count]

@[simp] theorem decodePair_pairBits (input : List Bool × List Bool) :
    decodePair (pairBits input) = some input := by
  rcases input with ⟨x, witness⟩
  simp [decodePair, pairBits, encodeWord, List.append_assoc,
    decodePairAux_frame]

theorem pairBits_injective : Function.Injective pairBits := by
  intro first second same
  have h := congrArg decodePair same
  simpa only [decodePair_pairBits, Option.some.injEq] using h

@[simp] theorem pairBits_length (input : List Bool × List Bool) :
    (pairBits input).length = 2 * input.1.length + input.2.length + 1 := by
  simp only [pairBits, List.length_append, encodeWord_length]
  omega

def pairEncoding : Computability.Encoding (List Bool × List Bool) Bool where
  encode := pairBits
  decode := decodePair
  decode_encode := decodePair_pairBits

structure NPVerifier where
  witnessBound : Polynomial Nat
  verify : (List Bool × List Bool) → Bool
  computation : Turing.TM2ComputableInPolyTime pairBits (fun bit => [bit]) verify
  finiteAlphabet : (k : computation.tm.K) → Fintype (computation.tm.Γ k)

def NPVerifier.Accepts (verifier : NPVerifier) (input : List Bool) : Prop :=
  ∃ witness : List Bool,
    witness.length ≤ verifier.witnessBound.eval input.length ∧
    verifier.verify (input, witness) = true

def InNP (language : List Bool → Prop) : Prop :=
  ∃ verifier : NPVerifier, ∀ input, language input ↔ verifier.Accepts input

theorem NPVerifier.acceptedLanguage_inNP (verifier : NPVerifier) :
    InNP verifier.Accepts := ⟨verifier, fun _ => Iff.rfl⟩

structure PolynomialThreeSATReduction (language : List Bool → Prop) where
  reduce : List Bool → Target.Formula
  computation : Turing.TM2ComputableInPolyTime id formulaBits reduce
  correct : ∀ input, language input ↔ (reduce input).Satisfiable

noncomputable def NPVerifier.horizon (verifier : NPVerifier) (inputLength : Nat) : Nat :=
  verifier.computation.time.eval
    (2 * inputLength + verifier.witnessBound.eval inputLength + 1)

theorem NPVerifier.input_time_le_horizon (verifier : NPVerifier)
    (input witness : List Bool)
    (bounded : witness.length ≤ verifier.witnessBound.eval input.length) :
    verifier.computation.time.eval (pairBits (input, witness)).length ≤
      verifier.horizon input.length := by
  apply MachineComposition.natPolynomial_eval_mono
  rw [pairBits_length]
  exact Nat.add_le_add_right (Nat.add_le_add_left bounded _) _

def NPVerifier.runWithinHorizon (verifier : NPVerifier)
    (input witness : List Bool)
    (bounded : witness.length ≤ verifier.witnessBound.eval input.length) :
    Turing.TM2OutputsInTime verifier.computation.tm
      ((pairBits (input, witness)).map verifier.computation.inputAlphabet.invFun)
      (some ([verifier.verify (input, witness)].map verifier.computation.outputAlphabet.invFun))
      (verifier.horizon input.length) where
  toEvalsTo := (verifier.computation.outputsFun (input, witness)).toEvalsTo
  steps_le_m := Nat.le_trans
    (verifier.computation.outputsFun (input, witness)).steps_le_m
    (verifier.input_time_le_horizon input witness bounded)

end DFVSGames.Foundations.Complexity.CookLevin
end

section

namespace DFVSGames.BinaryInputReduction

open Turing DFVSGames.Foundations.Complexity

noncomputable def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits BinaryLanguage.totalRename := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => BinaryOccurrenceRename.renamed (BinaryLanguage.totalParsed input))
  exact MachineSequential.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime
    BinaryTotalInputMachine.computation_finiteAlphabet
    BinaryRenameMachine.computation_finiteAlphabet

noncomputable def reduction : CookLevin.PolynomialThreeSATReduction BinaryLanguage.language where
  reduce := BinaryLanguage.totalRename
  computation := computation
  correct input := (BinaryLanguage.totalRename_satisfiable_iff input).symm

theorem reduction_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet reduction.computation.tm :=
  computation_finiteAlphabet

end DFVSGames.BinaryInputReduction

end

section

namespace DFVSGames.Outer.BinaryParityReduction

open DFVSGames.Foundations Target Complexity PCP
open DFVSGames.Reduction ActualSource
open MachineFiniteAlphabet

noncomputable section

def output (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (word : List Bool) : SourceEncoding.Input :=
  SourceIncidence.input H ξ hξ (BinaryLanguage.totalRename word)

def formulaMachine (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits
      (SourceIncidence.input H ξ hξ) :=
  MachineSequential.composeBits
    (f := HastadSource.output H ξ hξ) (g := Clone100.clonedInput)
    (HastadSource.computation H ξ hξ)
    Explicit.MachineClone100.computation

theorem formulaMachine_finite (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (formulaMachine H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits
    (f := HastadSource.output H ξ hξ) (g := Clone100.clonedInput)
    (HastadSource.computation H ξ hξ)
    Explicit.MachineClone100.computation
    (HastadSource.finiteAlphabet H ξ hξ) Explicit.MachineClone100.finiteAlphabet

def computation (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) SourceEncoding.inputBits
      (output H ξ hξ) :=
  MachineSequential.composeBits
    (f := BinaryLanguage.totalRename) (g := SourceIncidence.input H ξ hξ)
    BinaryInputReduction.computation (formulaMachine H ξ hξ)

theorem computation_finite (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (computation H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits
    (f := BinaryLanguage.totalRename) (g := SourceIncidence.input H ξ hξ)
    BinaryInputReduction.computation (formulaMachine H ξ hξ)
    BinaryInputReduction.computation_finiteAlphabet (formulaMachine_finite H ξ hξ)

theorem complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (word : List Bool) (yes : BinaryLanguage.language word) :
    ∃ a, 1 - ξ ≤ Clone100.success (output H ξ hξ word).equations a := by
  obtain ⟨a, ha⟩ := HastadSource.complete H ξ hξ (BinaryLanguage.totalRename word)
    ((BinaryLanguage.totalRename_satisfiable_iff word).mpr yes)
  refine ⟨Clone100.lift a, ?_⟩
  change 1 - ξ ≤ Clone100.success
    (Clone100.clonedInput (HastadSource.output H ξ hξ (BinaryLanguage.totalRename word))).equations
      (Clone100.lift a)
  rw [Clone100.completeness]
  exact ha

theorem sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (small : ξ < 1 / 100)
    (word : List Bool) (no : ¬ BinaryLanguage.language word)
    (a : Fin (output H ξ hξ word).«variables» → Bool) :
    Clone100.success (output H ξ hξ word).equations a ≤ 4 / 5 := by
  have hno : ¬ (BinaryLanguage.totalRename word).Satisfiable :=
    fun h => no ((BinaryLanguage.totalRename_satisfiable_iff word).mp h)
  exact Clone100.soundness_four_fifths
    (HastadSource.output H ξ hξ (BinaryLanguage.totalRename word)) ξ small
    (HastadSource.sound H certificate ξ hξ (BinaryLanguage.totalRename word) hno) a

structure Reduction (ξ : ℚ) where
  reduce : List Bool → SourceEncoding.Input
  distinct : ∀ word, (HastadSource.asSource (reduce word)).DistinctNames
  completeness : ∀ word, BinaryLanguage.language word →
    ∃ a, 1 - ξ ≤ Clone100.success (reduce word).equations a
  soundness : ∀ word, ¬ BinaryLanguage.language word →
    ∀ a, Clone100.success (reduce word).equations a ≤ 4 / 5
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    SourceEncoding.inputBits reduce
  finiteAlphabet : FiniteAlphabet computation.tm

theorem exists_reduction (ξ : ℚ) (positive : 0 < ξ) (small : ξ < 1 / 100) :
    Nonempty (Reduction ξ) := by
  obtain ⟨H, certificate⟩ := ExpanderTables.exists_base_table
  exact ⟨⟨output H ξ positive,
    (fun word => SourceIncidence.source_distinct H ξ positive (BinaryLanguage.totalRename word)),
    complete H ξ positive, sound H certificate ξ positive small,
    computation H ξ positive, computation_finite H ξ positive⟩⟩

theorem failure_completeness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (yes : BinaryLanguage.language word) :
    ∃ a, (HastadSource.asSource (R.reduce word)).failure a ≤ ξ := by
  obtain ⟨a, ha⟩ := R.completeness word yes
  refine ⟨a, ?_⟩
  have hsum := HastadSource.failure_add_success (R.reduce word) a
  change _ + Clone100.success (R.reduce word).equations a = 1 at hsum
  linarith

theorem parity_soundness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (no : ¬ BinaryLanguage.language word) :
    DFVSGames.Clean.IncidenceGap.parityValue
      (SourceIncidence.incidence (HastadSource.asSource (R.reduce word)))
      (DFVSGames.Foundations.Games.FiniteDistribution.uniform
        (Fin (HastadSource.asSource (R.reduce word)).occurrences)) ≤ 4 / 5 := by
  unfold DFVSGames.Clean.IncidenceGap.parityValue
  apply Finset.sup'_le
  intro a _
  have hq := R.soundness word no a
  have hreal : (Clone100.success (R.reduce word).equations a : ℝ) ≤ 4 / 5 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).mpr hq)
  exact (SourceIncidence.paritySuccess_input (R.reduce word) a).trans_le hreal

theorem ordinaryGame_soundness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (no : ¬ BinaryLanguage.language word) :
    (DFVSGames.Clean.IncidenceGap.fourAnswerGame
      (SourceIncidence.incidence (HastadSource.asSource (R.reduce word)))
      (DFVSGames.Foundations.Games.FiniteDistribution.uniform
        (Fin (HastadSource.asSource (R.reduce word)).occurrences))).value ≤ 14 / 15 :=
  DFVSGames.Clean.IncidenceGap.fourAnswerGame_value_le_fourteen_fifteenths _ _
    (SourceIncidence.names_distinct _ (R.distinct word)) (parity_soundness R word no)

end
end DFVSGames.Outer.BinaryParityReduction

end

section

namespace DFVSGames.Explicit.MachineSingleOrbitProgram

open Turing
open DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad
open DFVSGames.Reduction

inductive Tape
  | input | capacity | saved | remaining | accumulator | output
  deriving DecidableEq

instance : Fintype Tape where
  elems := {.input, .capacity, .saved, .remaining, .accumulator, .output}
  complete := by intro tape; cases tape <;> simp

abbrev State := Unit × Option Bool

def initialState : State := ((), none)

def clearKeys : List Tape := [.input, .capacity, .saved, .remaining]

inductive Label (q : Nat)
  | start | halfFirst | halfSecond | alphabet | count | guard
  | source | subtract | restore | target
  | table (completed : Fin (q + 1))
  | finishStart
  | finish (localLabel : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def copyField {q : Nat} (loopLabel exitLabel : Label q) :
    TM2.Stmt (fun _ : Tape => Bool) (Label q) State :=
  .pop .input (fun state head => (state.1, head))
    (.push .accumulator (fun state => state.2.getD false)
      (.branch (fun state => state.2.getD false)
        (.goto fun _ => loopLabel)
        (.load (fun _ => initialState) (.goto fun _ => exitLabel))))

def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .start => .push .capacity (fun _ => false)
      (.push .remaining (fun _ => false) (.goto fun _ => .halfFirst))
  | .halfFirst => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.goto fun _ => .halfSecond)
        (.push .accumulator (fun _ => false)
          (.load (fun _ => initialState) (.goto fun _ => .alphabet))))
  | .halfSecond => .pop .input (fun state _ => state)
      (.push .capacity (fun _ => true)
        (.push .accumulator (fun _ => true) (.goto fun _ => .halfFirst)))
  | .alphabet => copyField .alphabet .count
  | .count => .pop .input (fun state head => (state.1, head))
      (.push .accumulator (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (.push .remaining (fun _ => true) (.goto fun _ => .count))
          (.load (fun _ => initialState) (.goto fun _ => .guard))))
  | .guard => MachineUnaryCounter.guard .remaining .source .finishStart
  | .source => copyField .source .subtract
  | .subtract => .peek .capacity (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.pop .capacity (fun state _ => state)
          (.pop .input (fun state _ => state)
            (.push .saved (fun _ => true) (.goto fun _ => .subtract))))
        (.load (fun _ => initialState) (.goto fun _ => .restore)))
  | .restore => MachineTransfer.loopAt .saved .capacity id false .restore (some .target)
  | .target => copyField .target (.table 0)
  | .table completed =>
      if h : completed.val < q then
        copyField (.table completed) (.table ⟨completed.val + 1, by omega⟩)
      else .load (fun _ => initialState) (.goto fun _ => .guard)
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      () Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .start
  σ := State
  initialState := initialState
  m := program q

theorem finite_workAlphabet (q : Nat) (tape : (machine q).K) :
    Finite ((machine q).Γ tape) := by
  change Finite Bool
  infer_instance

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

theorem clearKeys_covers (tape : Tape) (ha : tape ≠ .accumulator)
    (ho : tape ≠ .output) : tape ∈ clearKeys := by
  cases tape <;> simp_all [clearKeys]

end DFVSGames.Explicit.MachineSingleOrbitProgram
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitStreams

open Turing DFVSGames.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram

def tapes (input capacity saved remaining accumulator output : List Bool) : Tape → List Bool
  | .input => input
  | .capacity => capacity
  | .saved => saved
  | .remaining => remaining
  | .accumulator => accumulator
  | .output => output

@[simp] theorem tapes_input (i c s r a o : List Bool) : tapes i c s r a o .input = i := rfl
@[simp] theorem tapes_capacity (i c s r a o : List Bool) : tapes i c s r a o .capacity = c := rfl
@[simp] theorem tapes_saved (i c s r a o : List Bool) : tapes i c s r a o .saved = s := rfl
@[simp] theorem tapes_remaining (i c s r a o : List Bool) : tapes i c s r a o .remaining = r := rfl
@[simp] theorem tapes_accumulator (i c s r a o : List Bool) : tapes i c s r a o .accumulator = a := rfl
@[simp] theorem tapes_output (i c s r a o : List Bool) : tapes i c s r a o .output = o := rfl

@[simp] theorem update_tapes (i c s r a o : List Bool) (t : Tape) (word : List Bool) :
    Function.update (tapes i c s r a o) t word =
      tapes (if t = .input then word else i) (if t = .capacity then word else c)
        (if t = .saved then word else s) (if t = .remaining then word else r)
        (if t = .accumulator then word else a) (if t = .output then word else o) := by
  cases t <;> funext k <;> cases k <;> simp [tapes]

def cfg {q : Nat} (label : Label q) (register : Option Bool)
    (i c s r a o : List Bool) : TM2.Cfg (fun _ : Tape => Bool) (Label q) State :=
  ⟨some label, ((), register), tapes i c s r a o⟩

theorem copyStep_true {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (true :: i) c s r a o) =
      some (cfg loopLabel (some true) i c s r (true :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg]

theorem copyStep_false {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (false :: i) c s r a o) =
      some (cfg exitLabel none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg, initialState]

theorem copyFieldTrace {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (n : Nat) (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg loopLabel register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg exitLabel none suffix c s r ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing a register with
  | zero =>
    simpa [encodeWord] using copyStep_false loopLabel exitLabel atLoop suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some,
      copyStep_true loopLabel exitLabel atLoop, ih]
    congr 2
    simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem tableTrace {q : Nat} (completed : Fin (q + 1)) (words : List Nat)
    (hcount : completed.val + words.length = q)
    (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some (cfg (.table completed) register (encodeWords words ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s r ((encodeWords words).reverse ++ a) o) := by
  induction words generalizing completed a register with
  | nil =>
    have hc : ¬ completed.val < q := by simp only [List.length_nil] at hcount; omega
    change some (TM2.stepAux (program q (.table completed)) _ _) = _
    simp [program, hc, TM2.stepAux, cfg, initialState, encodeWords]
  | cons n words ih =>
    have hc : completed.val < q := by simp only [List.length_cons] at hcount; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at hcount
      dsimp [next]
      omega
    have hp : program q (.table completed) = copyField (.table completed) (.table next) := by
      simp [program, hc, next]
    have first := copyFieldTrace (.table completed) (.table next) hp n
      (encodeWords words ++ suffix) c s r a o register
    have rest := ih next hn ((encodeWord n).reverse ++ a) none
    have ht : (encodeWords (n :: words)).length + 1 =
        ((encodeWords words).length + 1) + (n + 1) := by
      simp only [encodeWords, List.length_append, encodeWord_length]
      omega
    rw [ht, Function.iterate_add_apply]
    simp only [encodeWords, List.append_assoc]
    rw [first, rest]
    simp only [List.reverse_append, List.append_assoc]

end DFVSGames.Explicit.MachineSingleOrbitStreams
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
