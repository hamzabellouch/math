import OAI.Computability.UniqueGames.Machines.MachineSingleOrbitProgramLemmas
import OAI.Computability.UniqueGames.PCP.SourceRuntimeSpace

namespace OAI

noncomputable section

/-! Actual tape cleanup, accumulator reversal, and halt for the one-orbit
postprocessor. The time bound is derived from an actual executed prefix. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitFinish

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem haltList_eq (q : Nat) (bits : List Bool) : haltList (machine q) bits =
    ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  change (⟨none, initialState, (haltList (machine q) bits).stk⟩ : (machine q).Cfg) = _
  apply congrArg (fun base => (⟨none, initialState, base⟩ : (machine q).Cfg))
  funext tape
  cases tape <;> simp [haltList, machine, SourceRuntimeFinish.canonicalTapes] <;> rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩) 1 where
  steps := 1
  evals_in_steps := by rfl
  steps_le_m := Nat.le_refl _

def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

/-- This helper consumes a proved prefix trace. The final runtime theorem
supplies that trace from the concrete header and complete row traversal. -/
def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using
        joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys clearKeys_covers
    () Label.finish none (program q) (fun _ => rfl) base outputEmpty () none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q) input (prefixTime + 1)
    prefixRun clearKeys Tape.accumulator Tape.output accumulator_not_mem_clearKeys
    output_not_mem_clearKeys clearKeys_covers base outputEmpty (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end UniqueGamesTheorem.Explicit.MachineSingleOrbitFinish

/-!
Complete finite-machine postprocessing of the doubled address representation.
Every input field and row is physically processed. The time polynomial is in
the literal input bit length, including the final reversal and all tape cleanup.
-/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitRuntime

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitCodec MachineSingleOrbitRows

def finalTapes {q : Nat} (I : Instance q) : Tape → List Bool :=
  tapes [] (encodeWord I.vertices) [] (encodeWord 0) (gameBits I).reverse []

def prefixCost {q : Nat} (I : Instance q) : Nat :=
  (gameBits (doubleInstance I)).length + (I.vertices + 4) * I.constraints.length + 2

/-- The complete prefix is obtained from the actual header and row traces. -/
theorem prefixTrace {q : Nat} (I : Instance q) :
    (advance (TM2.step (program q)))^[prefixCost I]
      (some (initList (machine q) (gameBits (doubleInstance I)))) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
  have hh := MachineSingleOrbitHeader.headerTrace q I.vertices I.constraints.length
    (doubledRowsBits I.constraints)
  have hr := rowsTrace I.constraints []
    (encodeWords [I.vertices, q, I.constraints.length]).reverse [] none
  have hbits : gameBits I =
      encodeWords [I.vertices, q, I.constraints.length] ++ rowsBits I.constraints := by
    simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc] using gameBits_eq I
  have hr' : (advance (TM2.step (program q)))^[rowsCost I.constraints]
      (some (cfg .guard none (doubledRowsBits I.constraints) (encodeWord I.vertices) []
        (encodeWord I.constraints.length)
        (encodeWords [I.vertices, q, I.constraints.length]).reverse [])) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
    simpa only [List.append_nil, cfg, finalTapes, hbits, List.reverse_append, initialState]
      using hr
  have run := joinTrace hh hr'
  have hcost : rowsCost I.constraints +
      (2 * I.vertices + q + I.constraints.length + 4) = prefixCost I := by
    rw [prefixCost, input_length_eq]
    unfold rowsCost
    omega
  rw [hcost] at run
  simpa only [doubled_gameBits_eq] using run

def prefixPolynomial : Polynomial Nat :=
  Polynomial.X + (Polynomial.X + Polynomial.C 4) * Polynomial.X + Polynomial.C 2

theorem prefixCost_le {q : Nat} (I : Instance q) :
    prefixCost I ≤ prefixPolynomial.eval (gameBits (doubleInstance I)).length := by
  have hC := vertices_le_input_length I
  have hm := rows_le_input_length I
  have hp := Nat.mul_le_mul (Nat.add_le_add_right hC 4) hm
  simp only [prefixCost, prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

def prefixInTime {q : Nat} (I : Instance q) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (gameBits (doubleInstance I)))
      (some ⟨some .finishStart, initialState, finalTapes I⟩)
      (prefixPolynomial.eval (gameBits (doubleInstance I)).length) where
  steps := prefixCost I
  evals_in_steps := prefixTrace I
  steps_le_m := prefixCost_le I

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSingleOrbitFinish.timePolynomial q prefixPolynomial

/-- Literal init-to-halt execution, with every non-output tape empty at halt. -/
def fullRunInTime {q : Nat} (I : Instance q) :
    TM2OutputsInTime (machine q) (gameBits (doubleInstance I))
      (some (gameBits I)) ((timePolynomial q).eval (gameBits (doubleInstance I)).length) := by
  let run := MachineSingleOrbitFinish.completePrefix q (gameBits (doubleInstance I))
    prefixPolynomial (finalTapes I) (prefixInTime I) rfl
  simpa only [finalTapes, tapes_accumulator, List.reverse_reverse, timePolynomial] using run

/-- A proved polynomial-time codec conversion, without an assumed time bound,
an output-size certificate, or an unbounded integer in finite machine state. -/
def computableInPolyTime (q : Nat) :
    TM2ComputableInPolyTime (fun I : Instance q => gameBits (doubleInstance I)) gameBits id where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun I := by
    change TM2OutputsInTime (machine q) ((gameBits (doubleInstance I)).map id)
      (some ((gameBits I).map id))
      ((timePolynomial q).eval (gameBits (doubleInstance I)).length)
    erw [List.map_id, List.map_id]
    exact fullRunInTime I

theorem workAlphabetFinite (q : Nat) (tape : (computableInPolyTime q).tm.K) :
    Finite ((computableInPolyTime q).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.Explicit.MachineSingleOrbitRuntime

end

end OAI
