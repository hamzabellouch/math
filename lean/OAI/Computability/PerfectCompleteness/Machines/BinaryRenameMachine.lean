import Mathlib.Data.List.Basic
import OAI.Computability.PerfectCompleteness.Machines.BinaryHeaderMachine
import OAI.Computability.PerfectCompleteness.Machines.BinaryRenameLoop
import OAI.Computability.PerfectCompleteness.Machines.BinaryRenameWords
import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet

namespace OAI


namespace PerfectCompleteness.BinaryRenameMachine


open Turing UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

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

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
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
  have full := joinTrace (joinTrace (joinTrace (joinTrace first second) third) fourth) fifth
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

end PerfectCompleteness.BinaryRenameMachine

end OAI
