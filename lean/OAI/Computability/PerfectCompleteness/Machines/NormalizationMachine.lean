import OAI.Computability.PerfectCompleteness.Machines.BinaryHeaderMachine
import OAI.Computability.PerfectCompleteness.Machines.NormalizationLoopMachine
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet

namespace OAI


namespace PerfectCompleteness.NormalizationMachine


open Turing UniqueGamesTheorem.Foundations Complexity
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Tape := Fin 10
abbrev Alphabet (_ : Tape) := Bool
abbrev State := NormalizationLoopMachine.State Unit

inductive Label
  | readVariables | readCount
  | loop (label : NormalizationLoopMachine.Label)
  | restore | clauseStart | clauseLoop | variableStart | variableLoop | reject
  deriving DecidableEq, Fintype

def loopTapes : Fin 9 → Tape := Fin.castSucc

theorem loopTapes_injective : Function.Injective loopTapes := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Tape => k.val) h

def program : Label → TM2.Stmt Alphabet Label State
  | .readVariables => Hastad.SourceMachine.fieldLoop 0 1 .readVariables (some .readCount)
  | .readCount => Hastad.SourceMachine.fieldLoop 0 2 .readCount (some (.loop .guard))
  | .loop label => NormalizationLoopMachine.instruction loopTapes Label.loop
      (some .restore) (some .reject) label
  | .restore => loopAt 8 9 id false .restore (some .clauseStart)
  | .clauseStart => BinaryHeaderMachine.delimiter 9 .clauseLoop
  | .clauseLoop => loopAt 3 9 id false .clauseLoop (some .variableStart)
  | .variableStart => BinaryHeaderMachine.delimiter 9 .variableLoop
  | .variableLoop => loopAt 1 9 id false .variableLoop none
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 9
  Γ := Alphabet
  Λ := Label
  main := .readVariables
  σ := State
  initialState := NormalizationLoopMachine.reset ()
  m := program

def tapes (input fresh remaining clauseCounter reversed output : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then fresh else if k = 2 then remaining
    else if k = 3 then clauseCounter else if k = 8 then reversed else if k = 9 then output else []

def cfg (label : Option Label) (input fresh remaining clauseCounter reversed output : List Bool) :
    machine.Cfg := ⟨label, NormalizationLoopMachine.reset (),
      tapes input fresh remaining clauseCounter reversed output⟩

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
  have updated (input fresh : List Bool) :
      Hastad.SourceMachine.fieldTapes (0 : Tape) 1 (tapes [] [] [] [] [] []) input fresh =
        tapes input fresh [] [] [] [] := by
    funext k
    fin_cases k <;> simp [Hastad.SourceMachine.fieldTapes, tapes]
  have run := Hastad.SourceMachine.fieldLoopTrace (0 : Tape) 1 (by decide)
    .readVariables (some .readCount) program rfl (tapes [] [] [] [] [] []) n suffix []
    (NormalizationLoopMachine.reset ()).1 none
  simp only [updated, List.append_nil] at run
  exact run

theorem readCountTrace (n m : Nat) (suffix : List Bool) :
    (advance machine.step)^[m + 1]
      (some (cfg (some .readCount) (encodeWord m ++ suffix) (List.replicate n true) [] [] [] [])) =
      some (cfg (some (.loop .guard)) suffix (List.replicate n true) (List.replicate m true) [] [] []) := by
  have updated (input remaining : List Bool) :
      Hastad.SourceMachine.fieldTapes (0 : Tape) 2 (tapes [] (List.replicate n true) [] [] [] [])
        input remaining = tapes input (List.replicate n true) remaining [] [] [] := by
    funext k
    fin_cases k <;> simp [Hastad.SourceMachine.fieldTapes, tapes]
  have run := Hastad.SourceMachine.fieldLoopTrace (0 : Tape) 2 (by decide)
    .readCount (some (.loop .guard)) program rfl
    (tapes [] (List.replicate n true) [] [] [] []) m suffix []
    (NormalizationLoopMachine.reset ()).1 none
  simp only [updated, List.append_nil] at run
  exact run

theorem headersTrace (n m : Nat) (suffix : List Bool) :
    (advance machine.step)^[n + m + 2]
      (some (cfg (some .readVariables) (encodeWord n ++ encodeWord m ++ suffix) [] [] [] [] [])) =
      some (cfg (some (.loop .guard)) suffix (List.replicate n true) (List.replicate m true) [] [] []) := by
  have first := readVariablesTrace n (encodeWord m ++ suffix)
  have second := readCountTrace n m suffix
  have full := joinTrace first second
  have count : n + 1 + (m + 1) = n + m + 2 := by omega
  simpa only [count, List.append_assoc] using full

theorem restoreTrace (fresh clauseCounter body : List Bool) :
    (advance machine.step)^[body.length + 1]
      (some (cfg (some .restore) [] fresh [] clauseCounter body.reverse [])) =
      some (cfg (some .clauseStart) [] fresh [] clauseCounter [] body) := by
  change (nextAt (9 : Tape) program)^[body.length + 1]
    (some (cfg (some .restore) [] fresh [] clauseCounter body.reverse [])) = _
  have updated : tapesAt (8 : Tape) 9 (tapes [] fresh [] clauseCounter body.reverse []) [] body =
      tapes [] fresh [] clauseCounter [] body := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  have run := transferAt_fromTapes (Γ := Alphabet) (8 : Tape) 9 (by decide) id false
    .restore (some .clauseStart) program rfl (tapes [] fresh [] clauseCounter body.reverse [])
    (NormalizationLoopMachine.reset ()).1 none
  have source : tapes [] fresh [] clauseCounter body.reverse [] 8 = body.reverse := rfl
  have output : tapes [] fresh [] clauseCounter body.reverse [] 9 = [] := rfl
  rw [source, output, List.length_reverse, List.reverse_reverse, List.map_id_fun,
    List.append_nil, id_eq, updated] at run
  exact run

theorem headerOutputTrace (n m : Nat) (body : List Bool) :
    (advance machine.step)^[n + m + 4]
      (some (cfg (some .clauseStart) [] (List.replicate n true) []
        (List.replicate m true) [] body)) =
      some (cfg none [] [] [] [] [] (encodeWord n ++ encodeWord m ++ body)) := by
  change (advance (TM2.step program))^[n + m + 4]
    (some ⟨some .clauseStart, ((NormalizationLoopMachine.reset ()).1, none),
      tapes [] (List.replicate n true) [] (List.replicate m true) [] body⟩) =
    some ⟨none, ((NormalizationLoopMachine.reset ()).1, none),
      tapes [] [] [] [] [] (encodeWord n ++ encodeWord m ++ body)⟩
  have updated (fresh clauses output : List Bool) :
      BinaryHeaderMachine.tapes (1 : Tape) 3 9 (tapes [] [] [] [] [] []) fresh clauses output =
        tapes [] fresh [] clauses [] output := by
    funext k
    fin_cases k <;> simp [BinaryHeaderMachine.tapes, tapes]
  have run := BinaryHeaderMachine.headerTrace (1 : Tape) 3 9 (by decide) (by decide) (by decide)
    .clauseStart .clauseLoop .variableStart .variableLoop none program rfl rfl rfl rfl
    (tapes [] [] [] [] [] []) (NormalizationLoopMachine.reset ()).1 n m body none
  simp only [updated] at run
  exact run

theorem loopTrace (formula : Target.Formula) :
    (advance machine.step)^[NormalizationLoopMachine.steps formula.variables formula.clauses]
      (some (cfg (some (.loop .guard)) (encodeWords (formula.clauses.flatMap clauseWords))
        (List.replicate formula.variables true) (List.replicate formula.clauses.length true)
        [] [] [])) =
      some (cfg (some .restore) []
        (List.replicate (formula.variables + 4 * formula.clauses.length) true) []
        (List.replicate (13 * formula.clauses.length) true)
        (NormalizationStream.blocks formula.variables formula.clauses).reverse []) := by
  change (advance (TM2.step program))^[NormalizationLoopMachine.steps formula.variables formula.clauses]
    (some ⟨some (.loop .guard), NormalizationLoopMachine.reset (),
      tapes (encodeWords (formula.clauses.flatMap clauseWords))
        (List.replicate formula.variables true) (List.replicate formula.clauses.length true)
        [] [] []⟩) =
    some ⟨some .restore, NormalizationLoopMachine.reset (),
      tapes [] (List.replicate (formula.variables + 4 * formula.clauses.length) true) []
        (List.replicate (13 * formula.clauses.length) true)
        (NormalizationStream.blocks formula.variables formula.clauses).reverse []⟩
  have updated (input : List Bool) (fresh remaining : Nat) (counter output : List Bool) :
      NormalizationLoopMachine.loopTapes loopTapes (tapes [] [] [] [] [] [])
        input fresh remaining counter output =
      tapes input (List.replicate fresh true) (List.replicate remaining true) counter output [] := by
    funext k
    fin_cases k <;> simp [NormalizationLoopMachine.loopTapes, loopTapes, tapes]
  have run := NormalizationLoopMachine.loopTrace loopTapes loopTapes_injective Label.loop
    (some .restore) (some .reject) program (fun _ => rfl)
    (tapes [] [] [] [] [] []) () formula.clauses [] formula.variables [] []
    (by intros; simp [tapes])
  simp only [updated, List.append_nil, List.replicate_zero] at run
  exact run

theorem formulaBits_eq (formula : Target.Formula) :
    formulaBits formula = encodeWord formula.variables ++ encodeWord formula.clauses.length ++
      encodeWords (formula.clauses.flatMap clauseWords) := by
  simp only [formulaBits, formulaWords, encodeWords_append, encodeWords,
    List.append_nil, List.append_assoc]

def steps (formula : Target.Formula) : Nat :=
  (formula.variables + formula.clauses.length + 2) +
    NormalizationLoopMachine.steps formula.variables formula.clauses +
    ((NormalizationStream.blocks formula.variables formula.clauses).length + 1) +
    ((formula.variables + 4 * formula.clauses.length) + 13 * formula.clauses.length + 4)

theorem normalizationTrace (formula : Target.Formula) :
    (advance machine.step)^[steps formula] (some (initList machine (formulaBits formula))) =
      some (haltList machine (formulaBits (Normalization.normalize formula))) := by
  have first := headersTrace formula.variables formula.clauses.length
    (encodeWords (formula.clauses.flatMap clauseWords))
  have second := loopTrace formula
  have third := restoreTrace
    (List.replicate (formula.variables + 4 * formula.clauses.length) true)
    (List.replicate (13 * formula.clauses.length) true)
    (NormalizationStream.blocks formula.variables formula.clauses)
  have fourth := headerOutputTrace (formula.variables + 4 * formula.clauses.length)
    (13 * formula.clauses.length) (NormalizationStream.blocks formula.variables formula.clauses)
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  rw [initList_eq, haltList_eq, NormalizationStream.encoded_normalize, formulaBits_eq]
  exact full

theorem header_counts_le (formula : Target.Formula) :
    formula.variables ≤ (formulaBits formula).length ∧
      formula.clauses.length ≤ (formulaBits formula).length := by
  rw [formulaBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1) ^ 2

theorem steps_le (formula : Target.Formula) :
    steps formula ≤ timePolynomial.eval (formulaBits formula).length := by
  let B := (formulaBits formula).length
  let M := formula.variables + 4 * formula.clauses.length
  have variablesBound : formula.variables ≤ B := (header_counts_le formula).1
  have clausesBound : formula.clauses.length ≤ B := (header_counts_le formula).2
  have addressBound : M ≤ 5 * B := by dsimp [M]; omega
  have loopBound := NormalizationLoopMachine.steps_le formula.variables M formula.clauses
    (by dsimp [M]; omega) (Nat.le_refl M)
  have loopUniform : NormalizationLoopMachine.steps formula.variables formula.clauses ≤
      B * (420 * B + 128) + 1 :=
    loopBound.trans (Nat.add_le_add_right
      (Nat.mul_le_mul clausesBound (by omega)) 1)
  have bodyBound := NormalizationStream.blocks_length_le formula.clauses formula.variables M
    (by dsimp [M]; omega) (Nat.le_refl M)
  have bodyUniform : (NormalizationStream.blocks formula.variables formula.clauses).length ≤
      B * (39 * (5 * B + 3)) :=
    bodyBound.trans (Nat.mul_le_mul clausesBound (by omega))
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X]
  change steps formula ≤ 1000 * (B + 1) ^ 2
  unfold steps
  nlinarith

def outputsInTime (formula : Target.Formula) :
    TM2OutputsInTime machine (formulaBits formula)
      (some (formulaBits (Normalization.normalize formula)))
      (timePolynomial.eval (formulaBits formula).length) where
  steps := steps formula
  evals_in_steps := normalizationTrace formula
  steps_le_m := steps_le formula

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime formulaBits formulaBits Normalization.normalize where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun formula := by
    change TM2OutputsInTime machine ((formulaBits formula).map id)
      (some ((formulaBits (Normalization.normalize formula)).map id))
      (timePolynomial.eval (formulaBits formula).length)
    simpa only [List.map_id_fun, id_eq] using outputsInTime formula

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  machine_finiteAlphabet

end PerfectCompleteness.NormalizationMachine

end OAI
