import OAI.Computability.UniqueGames.Games.UniformTarget
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineSubdivisionBodySpecLemmas
import OAI.Computability.UniqueGames.PCP.SourceRuntimeSpace

namespace OAI

/-! Whole-instance uniform copying: exact physical header arithmetic, repeated
body emission, actual cleanup, and a polynomial bound in the input codec length. -/

namespace UniqueGamesTheorem.Explicit.MachineUniformRun

open Turing UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Foundations Target
open UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad
open MachineUniformProgram

def outputBits (C n q Q : Nat) (body : List Bool) : List Bool :=
  encodeWords [n, q, C * Q] ++ MachineUniformCopyOrder.copyMajor C body

def afterScale (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineUniformHeaders.resultTapes n q Q body)
    .newOccurrences (encodeWord (C * Q))

def afterEmit (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterScale C n q Q body)
    .accumulator (outputBits C n q Q body)

def scaleInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩
      (some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩)
      (2 * (Q + 1) + 1) where
  steps := 2 * (Q + 1) + 1
  evals_in_steps := by
    change (MachineComposition.advance (machine C).step)^[2 * (Q + 1) + 1]
      (some ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩) =
      some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
    have h := MachineUnaryAffineAt.seededAffineTrace Tape.occurrences .affineScratch
      .newOccurrences (by decide) (by decide) (by decide) C 0
      (.scale 0 : Label C) (.scale 1) (.scale 2) (some (emitEntry C))
      (program C) rfl rfl rfl (MachineUniformHeaders.resultTapes n q Q body)
      Q [] (by simp [MachineUniformHeaders.resultTapes])
      (by simp [MachineUniformHeaders.resultTapes]) ((), ()) none
    simpa only [machine, FinTM2.step, FinTM2.Cfg,
      initialState, afterScale,
      show MachineUniformHeaders.resultTapes n q Q body .newOccurrences = [] from rfl,
      Nat.add_zero, List.append_nil] using! h
  steps_le_m := Nat.le_refl _

theorem repeated_template (C : Nat) (fields : Fin 4 → List Bool) :
    MachineFieldTemplate.templateOutput (List.replicate C (.copy 3)) fields =
      MachineUniformCopyOrder.copyMajor C (fields 3) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simp only [List.replicate_succ, MachineFieldTemplate.templateOutput,
      List.flatMap_cons, MachineFieldTemplate.tokenOutput,
      MachineUniformCopyOrder.copyMajor, List.flatten_cons] at *
    rw [ih]

theorem template_output (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) = outputBits C n q Q body := by
  simp only [tokens, MachineFieldTemplate.templateOutput, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, MachineFieldTemplate.tokenOutput]
  rw [show (List.replicate C (MachineFieldTemplate.Token.copy (3 : Fin 4))).flatMap
      (MachineFieldTemplate.tokenOutput (fun i => afterScale C n q Q body (emitField i))) =
        MachineUniformCopyOrder.copyMajor C (afterScale C n q Q body (emitField 3)) from
      repeated_template C _]
  simp [afterScale, MachineUniformHeaders.resultTapes, emitField, outputBits,
    encodeWords, List.append_assoc]

theorem template_copiedLength (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) =
        n + q + C * Q + 3 + C * body.length := by
  simp [MachineFieldTemplate.copiedLength, tokens, afterScale,
    MachineUniformHeaders.resultTapes, emitField, Nat.add_assoc]
  omega

def emitInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      (3 * (n + q + C * Q + 3 + C * body.length) + 3 * (C + 3) + 1) := by
  have h := MachineFieldTemplate.phaseInTime (tokens C) emitField
    Tape.copyScratch .accumulator
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide) (by decide)
    (Label.emit (C := C)) (some .finishStart) (program C) (fun _ => rfl)
    (afterScale C n q Q body) (by simp [afterScale, MachineUniformHeaders.resultTapes])
    initialState
  simpa only [machine, FinTM2.step, FinTM2.Cfg, emitEntry,
    MachineFieldTemplate.reset, initialState,
    template_output, template_copiedLength, afterEmit,
    show (tokens C).length = C + 3 by simp [tokens]] using! h

noncomputable def prefixPolynomial (C : Nat) : Polynomial Nat :=
  Polynomial.C (3 * C + 6) * Polynomial.X + Polynomial.C (3 * C + 16)

theorem input_length (n q Q : Nat) (body : List Bool) :
    (encodeWords [n, q, Q] ++ body).length = n + q + Q + 3 + body.length := by
  simp [Nat.add_assoc]

def prefixInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      ((prefixPolynomial C).eval (encodeWords [n, q, Q] ++ body).length) := by
  let first := MachineUniformHeaders.headersInTime C q n Q body
  let second := scaleInTime C n q Q body
  let third := emitInTime C n q Q body
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo third
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, input_length]
  have hcopy : n + q + C * Q + 3 + C * body.length ≤
      (C + 1) * (n + q + Q + 3 + body.length) := by nlinarith
  nlinarith

noncomputable def timePolynomial (C : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine C) clearKeys.length (prefixPolynomial C + 1)

theorem haltList_eq (C : Nat) (bits : List Bool) :
    haltList (machine C) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  (cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes, Function.update]); rfl

def finishStartInTime (C : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (C := C)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program C .finishStart) initialState base) = _
    rfl
  steps_le_m := Nat.le_refl _

/-- The complete actual run, including the physical cleanup and output reversal. -/
noncomputable def outputInTime (C n q Q : Nat) (body : List Bool) :
    TM2OutputsInTime (machine C) (encodeWords [n, q, Q] ++ body)
      (some (outputBits C n q Q body))
      ((timePolynomial C).eval (encodeWords [n, q, Q] ++ body).length) := by
  let initialRun := prefixInTime C n q Q body
  let bridge := finishStartInTime C (afterEmit C n q Q body)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initialRun bridge
  let prefixRun : StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (C := C)), initialState,
        afterEmit C n q Q body⟩)
      ((prefixPolynomial C + 1).eval (encodeWords [n, q, Q] ++ body).length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm]
      using joined.steps_le_m }
  have hout : afterEmit C n q Q body .output = [] := by
    simp [afterEmit, MachineFieldTemplate.outputTapes, afterScale,
      MachineUniformHeaders.resultTapes]
  let finish := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (C := C)) none (program C) (fun _ => rfl)
    (afterEmit C n q Q body) hout ((), ()) none
  let whole := SourceRuntimeSpace.prefixAndFinishInTime (machine C)
    (encodeWords [n, q, Q] ++ body) (prefixPolynomial C + 1) prefixRun
    clearKeys Tape.accumulator Tape.output accumulator_not_mem_clearKeys
    output_not_mem_clearKeys covers (afterEmit C n q Q body) hout (fun _ => rfl) finish
  have hword : (afterEmit C n q Q body .accumulator).reverse = outputBits C n q Q body := by
    simp [afterEmit, MachineFieldTemplate.outputTapes, afterScale,
      MachineUniformHeaders.resultTapes]
  change StateTransition.EvalsToInTime (machine C).step _
    (some (haltList (machine C) (outputBits C n q Q body))) _
  rw [haltList_eq, ← hword]
  exact whole

/-- A fixed actual program works for every game and every alphabet size. -/
noncomputable def computation {q : Nat} (C : Nat) (hC : 0 < C) :
    TM2ComputableInPolyTime gameBits gameBits (UniformTarget.construct (q := q) C hC) where
  tm := machine C
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial C
  outputsFun g := by
    change TM2OutputsInTime (machine C) ((gameBits g).map id)
      (some ((gameBits (UniformTarget.construct C hC g)).map id)) _
    have input_eq : @List.map ((machine C).Γ (machine C).k₀)
        ((machine C).Γ (machine C).k₀) id (gameBits g) = gameBits g := List.map_id _
    have output_eq : @List.map ((machine C).Γ (machine C).k₁)
        ((machine C).Γ (machine C).k₁) id (gameBits (UniformTarget.construct C hC g)) =
        gameBits (UniformTarget.construct C hC g) := List.map_id _
    simp only [input_eq, output_eq]
    rw [UniformTarget.gameBits_construct]
    have input : gameBits g = encodeWords [g.vertices, q, g.constraints.length] ++
        encodeWords (g.constraints.flatMap constraintWords) := by
      simp [gameBits, gameWords, encodeWords, List.append_assoc]
    rw [input]
    exact outputInTime C g.vertices q g.constraints.length
      (encodeWords (g.constraints.flatMap constraintWords))

theorem finiteAlphabet {q : Nat} (C : Nat) (hC : 0 < C) :
    MachineFiniteAlphabet.FiniteAlphabet (computation (q := q) C hC).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

end UniqueGamesTheorem.Explicit.MachineUniformRun

end OAI
