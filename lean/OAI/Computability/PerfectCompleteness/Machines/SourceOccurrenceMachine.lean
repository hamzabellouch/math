import OAI.Computability.PerfectCompleteness.Machines.BinaryHeaderMachine
import OAI.Computability.PerfectCompleteness.Machines.SourceOccurrenceLoopMachine
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Tape := Fin 7
abbrev Alphabet (_ : Tape) := Bool
abbrev State := Unit × Option Bool

def clean : State := ((), none)

inductive Label
  | readVariables | readCount
  | loop (label : SourceOccurrenceLoopMachine.Label)
  | restore | clauseStart | clauseLoop | variableStart | variableLoop | reject
  deriving DecidableEq, Fintype

def loopTapes : Fin 5 → Tape
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5

theorem loopTapes_injective : Function.Injective loopTapes := by decide

def program : Label → TM2.Stmt Alphabet Label State
  | .readVariables => Hastad.SourceMachine.fieldLoop 0 1 .readVariables (some .readCount)
  | .readCount => Hastad.SourceMachine.fieldLoop 0 2 .readCount (some (.loop .guard))
  | .loop label => SourceOccurrenceLoopMachine.instruction loopTapes Label.loop
      (some .restore) (some .reject) label
  | .restore => loopAt 5 6 id false .restore (some .clauseStart)
  | .clauseStart => BinaryHeaderMachine.delimiter 6 .clauseLoop
  | .clauseLoop => loopAt 3 6 id false .clauseLoop (some .variableStart)
  | .variableStart => BinaryHeaderMachine.delimiter 6 .variableLoop
  | .variableLoop => loopAt 1 6 id false .variableLoop none
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 6
  Γ := Alphabet
  Λ := Label
  main := .readVariables
  σ := State
  initialState := clean
  m := program

def tapes (input variableCounter remaining index reversed output : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then variableCounter else if k = 2 then remaining
    else if k = 3 then index else if k = 5 then reversed else if k = 6 then output else []

def cfg (label : Option Label) (input variableCounter remaining index reversed output : List Bool) :
    machine.Cfg := ⟨label, clean, tapes input variableCounter remaining index reversed output⟩

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .readVariables) input [] [] [] [] [] := by
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

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem readVariablesTrace (n : Nat) (suffix : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .readVariables) (encodeWord n ++ suffix) [] [] [] [] [])) =
      some (cfg (some .readCount) suffix (List.replicate n true) [] [] [] []) := by
  change (advance (TM2.step program))^[n + 1]
    (some ⟨some .readVariables, ((), none),
      tapes (encodeWord n ++ suffix) [] [] [] [] []⟩) =
    some ⟨some .readCount, ((), none), tapes suffix (List.replicate n true) [] [] [] []⟩
  have updated (input variableCounter : List Bool) :
      Hastad.SourceMachine.fieldTapes (0 : Tape) 1 (tapes [] [] [] [] [] []) input variableCounter =
        tapes input variableCounter [] [] [] [] := by
    funext k
    fin_cases k <;> simp [Hastad.SourceMachine.fieldTapes, tapes]
  have run := Hastad.SourceMachine.fieldLoopTrace (0 : Tape) 1 (by decide)
    .readVariables (some .readCount) program rfl (tapes [] [] [] [] [] []) n suffix [] () none
  simp only [updated, List.append_nil] at run
  exact run

theorem readCountTrace (n m : Nat) (suffix : List Bool) :
    (advance machine.step)^[m + 1]
      (some (cfg (some .readCount) (encodeWord m ++ suffix) (List.replicate n true) [] [] [] [])) =
      some (cfg (some (.loop .guard)) suffix (List.replicate n true)
        (List.replicate m true) [] [] []) := by
  change (advance (TM2.step program))^[m + 1]
    (some ⟨some .readCount, ((), none),
      tapes (encodeWord m ++ suffix) (List.replicate n true) [] [] [] []⟩) =
    some ⟨some (.loop .guard), ((), none),
      tapes suffix (List.replicate n true) (List.replicate m true) [] [] []⟩
  have updated (input remaining : List Bool) :
      Hastad.SourceMachine.fieldTapes (0 : Tape) 2 (tapes [] (List.replicate n true) [] [] [] [])
        input remaining = tapes input (List.replicate n true) remaining [] [] [] := by
    funext k
    fin_cases k <;> simp [Hastad.SourceMachine.fieldTapes, tapes]
  have run := Hastad.SourceMachine.fieldLoopTrace (0 : Tape) 2 (by decide)
    .readCount (some (.loop .guard)) program rfl
    (tapes [] (List.replicate n true) [] [] [] []) m suffix [] () none
  simp only [updated, List.append_nil] at run
  exact run

theorem headersTrace (n m : Nat) (suffix : List Bool) :
    (advance machine.step)^[n + m + 2]
      (some (cfg (some .readVariables) (encodeWord n ++ encodeWord m ++ suffix) [] [] [] [] [])) =
      some (cfg (some (.loop .guard)) suffix (List.replicate n true)
        (List.replicate m true) [] [] []) := by
  have first := readVariablesTrace n (encodeWord m ++ suffix)
  have second := readCountTrace n m suffix
  have full := joinTrace first second
  have count : n + 1 + (m + 1) = n + m + 2 := by omega
  simpa only [count, List.append_assoc] using full

theorem restoreTrace (variableCounter index body : List Bool) :
    (advance machine.step)^[body.length + 1]
      (some (cfg (some .restore) [] variableCounter [] index body.reverse [])) =
      some (cfg (some .clauseStart) [] variableCounter [] index [] body) := by
  change (nextAt (6 : Tape) program)^[body.length + 1]
    (some (cfg (some .restore) [] variableCounter [] index body.reverse [])) = _
  have updated : tapesAt (5 : Tape) 6 (tapes [] variableCounter [] index body.reverse []) [] body =
      tapes [] variableCounter [] index [] body := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  have run := transferAt_fromTapes (Γ := Alphabet) (5 : Tape) 6 (by decide) id false
    .restore (some .clauseStart) program rfl (tapes [] variableCounter [] index body.reverse []) () none
  have source : tapes [] variableCounter [] index body.reverse [] 5 = body.reverse := rfl
  have output : tapes [] variableCounter [] index body.reverse [] 6 = [] := rfl
  rw [source, output, List.length_reverse, List.reverse_reverse, List.map_id_fun,
    List.append_nil, id_eq, updated] at run
  exact run

theorem headerOutputTrace (n m : Nat) (body : List Bool) :
    (advance machine.step)^[n + m + 4]
      (some (cfg (some .clauseStart) [] (List.replicate n true) []
        (List.replicate m true) [] body)) =
      some (cfg none [] [] [] [] [] (encodeWord n ++ encodeWord m ++ body)) := by
  change (advance (TM2.step program))^[n + m + 4]
    (some ⟨some .clauseStart, ((), none),
      tapes [] (List.replicate n true) [] (List.replicate m true) [] body⟩) =
    some ⟨none, ((), none), tapes [] [] [] [] [] (encodeWord n ++ encodeWord m ++ body)⟩
  have updated (variableCounter clauses output : List Bool) :
      BinaryHeaderMachine.tapes (1 : Tape) 3 6 (tapes [] [] [] [] [] []) variableCounter clauses output =
        tapes [] variableCounter [] clauses [] output := by
    funext k
    fin_cases k <;> simp [BinaryHeaderMachine.tapes, tapes]
  have run := BinaryHeaderMachine.headerTrace (1 : Tape) 3 6 (by decide) (by decide) (by decide)
    .clauseStart .clauseLoop .variableStart .variableLoop none program rfl rfl rfl rfl
    (tapes [] [] [] [] [] []) () n m body none
  simp only [updated] at run
  exact run

theorem formulaBits_eq (formula : Formula) :
    formulaBits formula = encodeWord formula.variables ++ encodeWord formula.clauses.length ++
      encodeWords (formula.clauses.flatMap clauseWords) := by
  simp only [formulaBits, formulaWords, encodeWords_append, encodeWords,
    List.append_nil, List.append_assoc]

theorem header_counts_le (formula : Formula) :
    formula.variables ≤ (formulaBits formula).length ∧
      formula.clauses.length ≤ (formulaBits formula).length := by
  rw [formulaBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem loopTrace (formula : Formula) :
    (advance machine.step)^[SourceOccurrenceLoopMachine.steps 0 formula.clauses]
      (some (cfg (some (.loop .guard)) (encodeWords (formula.clauses.flatMap clauseWords))
        (List.replicate formula.variables true) (List.replicate formula.clauses.length true)
        [] [] [])) =
      some (cfg (some .restore) [] (List.replicate formula.variables true) []
        (List.replicate formula.clauses.length true)
        (SourceOccurrenceEncoding.body 0 formula.clauses).reverse []) := by
  change (advance (TM2.step program))^[SourceOccurrenceLoopMachine.steps 0 formula.clauses]
    (some ⟨some (.loop .guard), ((), none),
      tapes (encodeWords (formula.clauses.flatMap clauseWords))
        (List.replicate formula.variables true) (List.replicate formula.clauses.length true)
        [] [] []⟩) =
    some ⟨some .restore, ((), none),
      tapes [] (List.replicate formula.variables true) []
        (List.replicate formula.clauses.length true)
        (SourceOccurrenceEncoding.body 0 formula.clauses).reverse []⟩
  have updated (input : List Bool) (remaining first : Nat) (output : List Bool) :
      SourceOccurrenceLoopMachine.loopTapes loopTapes
        (tapes [] (List.replicate formula.variables true) [] [] [] [])
        input remaining first output =
      tapes input (List.replicate formula.variables true) (List.replicate remaining true)
        (List.replicate first true) output [] := by
    funext k
    fin_cases k <;> simp [SourceOccurrenceLoopMachine.loopTapes, loopTapes, tapes]
  have run := SourceOccurrenceLoopMachine.loopTrace loopTapes loopTapes_injective Label.loop
    (some .restore) (some .reject) program (fun _ => rfl)
    (tapes [] (List.replicate formula.variables true) [] [] [] []) () formula.clauses [] 0 [] rfl
  simp only [updated, List.append_nil, List.replicate_zero, Nat.zero_add] at run
  exact run

def steps (formula : Formula) : Nat :=
  (formula.variables + formula.clauses.length + 2) +
    SourceOccurrenceLoopMachine.steps 0 formula.clauses +
    ((SourceOccurrenceEncoding.body 0 formula.clauses).length + 1) +
    (formula.variables + formula.clauses.length + 4)

theorem occurrenceTrace (formula : Formula) :
    (advance machine.step)^[steps formula] (some (initList machine (formulaBits formula))) =
      some (haltList machine (SourceOccurrenceEncoding.bits formula)) := by
  have first := headersTrace formula.variables formula.clauses.length
    (encodeWords (formula.clauses.flatMap clauseWords))
  have second := loopTrace formula
  have third := restoreTrace (List.replicate formula.variables true)
    (List.replicate formula.clauses.length true) (SourceOccurrenceEncoding.body 0 formula.clauses)
  have fourth := headerOutputTrace formula.variables formula.clauses.length
    (SourceOccurrenceEncoding.body 0 formula.clauses)
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  simpa only [steps, initList_eq, haltList_eq, formulaBits_eq,
    SourceOccurrenceEncoding.bits_eq] using full

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * (Polynomial.X + Polynomial.C 1) ^ 2

theorem steps_le (formula : Formula) :
    steps formula ≤ timePolynomial.eval (formulaBits formula).length := by
  let B := (formulaBits formula).length
  have variablesBound : formula.variables ≤ B := (header_counts_le formula).1
  have clausesBound : formula.clauses.length ≤ B := (header_counts_le formula).2
  have loopBound := SourceOccurrenceLoopMachine.steps_le 0 formula.clauses.length
    formula.clauses (by omega)
  have loopUniform : SourceOccurrenceLoopMachine.steps 0 formula.clauses ≤
      B * (5 * B + 11) + 1 :=
    loopBound.trans (Nat.add_le_add_right
      (Nat.mul_le_mul clausesBound (by omega)) 1)
  have bodyBound := SourceOccurrenceEncoding.body_length_le formula.clauses 0
    formula.clauses.length (by omega)
  have bodyUniform : (SourceOccurrenceEncoding.body 0 formula.clauses).length ≤
      B * (4 * B + 7) :=
    bodyBound.trans (Nat.mul_le_mul clausesBound (by omega))
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X]
  change steps formula ≤ 100 * (B + 1) ^ 2
  unfold steps
  nlinarith

def outputsInTime (formula : Formula) :
    TM2OutputsInTime machine (formulaBits formula)
      (some (SourceOccurrenceEncoding.bits formula))
      (timePolynomial.eval (formulaBits formula).length) where
  steps := steps formula
  evals_in_steps := occurrenceTrace formula
  steps_le_m := steps_le formula

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime formulaBits SourceOccurrenceEncoding.bits (id : Formula → Formula) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun formula := by
    change TM2OutputsInTime machine ((formulaBits formula).map id)
      (some ((SourceOccurrenceEncoding.bits formula).map id))
      (timePolynomial.eval (formulaBits formula).length)
    simpa only [List.map_id_fun, id_eq] using outputsInTime formula

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  machine_finiteAlphabet

end PerfectCompleteness.SourceOccurrenceMachine

end OAI
