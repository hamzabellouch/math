import OAI.Computability.PerfectCompleteness.Machines.PositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineTransducerCopy

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine


open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
open PostfixModel

inductive Tape where
  | remaining | current | threshold | scratch | reversed
  | rawInput | witnessBound | capacity | closure
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.remaining, .current, .threshold, .scratch,
  .reversed, .rawInput, .witnessBound, .capacity, .closure]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label where
  | guard | inputTag | scan | emit (symbol : Bool) | restore | test
  | result (value : Bool) | done
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool
abbrev State := (Unit × Unit) × Option Bool

def initialState : State := (((), ()), none)

def program : Label → TM2.Stmt Alphabet Label State
  | .guard => MachineUnaryCounter.guard .remaining .inputTag .done
  | .inputTag => pushWord .reversed (encodeWord 5) (.goto fun _ => .scan)
  | .scan => MachineTransducerCopy.scanLoop .current .scratch () (fun _ b => .emit b) .restore
  | .emit b => MachineTransducerCopy.emitter .reversed (fun _ _ => ())
      (fun _ symbol => [symbol]) .scan () b
  | .restore => Reduction.MachineTransfer.loopAt .scratch .current id false .restore (some .test)
  | .test => MachineUnaryCounter.guard .threshold (.result false) (.result true)
  | .result b => pushWord .reversed (encodeWords [if b then 1 else 0, 3])
      (.push .current (fun _ => true) (.goto fun _ => .guard))
  | .done => .halt

def machine : FinTM2 where
  K := Tape
  k₀ := .rawInput
  k₁ := .reversed
  Γ _ := Bool
  Λ := Label
  main := .guard
  σ := State
  initialState := initialState
  m := program

def tapes (base : Tape → List Bool) (remaining current threshold : Nat)
    (output : List Bool) : Tape → List Bool
  | .remaining => encodeWord remaining
  | .current => encodeWord current
  | .threshold => encodeWord threshold
  | .scratch => []
  | .reversed => output
  | tape => base tape

@[simp] theorem tapes_current (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    tapes base m i d output .current = encodeWord i := rfl

@[simp] theorem tapes_reversed (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    tapes base m i d output .reversed = output := rfl

theorem update_reversed (base : Tape → List Bool) (m i d : Nat)
    (output replacement : List Bool) :
    Function.update (tapes base m i d output) .reversed replacement =
      tapes base m i d replacement := by
  funext tape
  cases tape <;> simp [tapes]

theorem push_current (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    Function.update (tapes base m i d output) .current (true :: encodeWord i) =
      tapes base m (i + 1) d output := by
  funext tape
  cases tape <;> simp [tapes, encodeWord, List.replicate_succ]

theorem counterTapes_remaining (base : Tape → List Bool) (m i d r : Nat)
    (output : List Bool) :
    MachineUnaryCounter.counterTapes .remaining (tapes base m i d output) r [] =
      tapes base r i d output := by
  funext tape
  cases tape <;> simp [MachineUnaryCounter.counterTapes, tapes]

theorem counterTapes_threshold (base : Tape → List Bool) (m i d r : Nat)
    (output : List Bool) :
    MachineUnaryCounter.counterTapes .threshold (tapes base m i d output) r [] =
      tapes base m i r output := by
  funext tape
  cases tape <;> simp [MachineUnaryCounter.counterTapes, tapes]

private theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[m + n] x = z := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem inputTagStep (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    TM2.step program ⟨some .inputTag, initialState, tapes base m i d output⟩ =
      some ⟨some .scan, initialState,
        tapes base m i d ((encodeWord 5).reverse ++ output)⟩ := by
  change some (TM2.stepAux (program .inputTag) initialState (tapes base m i d output)) = _
  rw [program, stepAux_pushWord]
  change some (⟨some .scan, initialState, Function.update (tapes base m i d output)
    .reversed ((encodeWord 5).reverse ++ output)⟩ : TM2.Cfg Alphabet Label State) = _
  rw [update_reversed]

private theorem identity_output (input : List Bool) :
    Reduction.MachineTransducer.output (fun (_ : Unit) _ => ())
      (fun _ symbol => [symbol]) () input = input := by
  induction input with
  | nil => rfl
  | cons b input ih => simp [Reduction.MachineTransducer.output, ih]

theorem indexTrace (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * (i + 1) + 2]
      (some ⟨some .scan, initialState, tapes base m i d output⟩) =
      some ⟨some .test, initialState,
        tapes base m i d ((encodeWord i).reverse ++ output)⟩ := by
  have h := MachineTransducerCopy.transduceCopyTrace Tape.current Tape.scratch Tape.reversed
    (by decide) (by decide) (by decide) () (fun _ _ => ()) (fun _ symbol => [symbol])
    Label.scan Label.restore (fun _ b => Label.emit b) (some Label.test)
    program rfl (by intro control symbol; cases control; rfl) rfl
    (tapes base m i d output) rfl () () none
  simpa only [tapes_current, tapes_reversed, encodeWord_length, identity_output,
    update_reversed, initialState] using h

theorem thresholdStep (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    TM2.step program ⟨some .test, initialState, tapes base m i d output⟩ =
      some ⟨some (.result (decide (d = 0))), initialState,
        tapes base m i (d - 1) output⟩ := by
  cases d with
  | zero =>
    simpa only [counterTapes_threshold, Nat.zero_sub, decide_true, initialState] using
      MachineUnaryCounter.guardStep_zero Tape.threshold Label.test (.result false) (.result true)
        program rfl (tapes base m i 0 output) [] ((), ()) none
  | succ d =>
    simpa only [counterTapes_threshold, Nat.add_sub_cancel, Nat.succ_ne_zero,
      decide_false, initialState] using
      MachineUnaryCounter.guardStep_succ Tape.threshold Label.test (.result false) (.result true)
        program rfl (tapes base m i (d + 1) output) d [] ((), ()) none

theorem resultStep (base : Tape → List Bool) (m i d : Nat) (output : List Bool) (b : Bool) :
    TM2.step program ⟨some (.result b), initialState, tapes base m i d output⟩ =
      some ⟨some .guard, initialState, tapes base m (i + 1) d
        ((encodeWords [if b then 1 else 0, 3]).reverse ++ output)⟩ := by
  change some (TM2.stepAux (program (.result b)) initialState (tapes base m i d output)) = _
  rw [program, stepAux_pushWord]
  simp only [TM2.stepAux, tapes_reversed]
  rw [update_reversed, tapes_current, push_current]

def termTokens (i d : Nat) : List Token :=
  [.input i, .const (decide (d = 0)), .and]

theorem termTokens_bits (i d : Nat) :
    tokenBits (termTokens i d) = encodeWord 5 ++ encodeWord i ++
      encodeWords [if decide (d = 0) then 1 else 0, 3] := by
  by_cases hd : d = 0 <;>
    simp [termTokens, tokenBits, tokenWords, Token.words, hd, encodeWords, List.append_assoc]

def bodySteps (i : Nat) : Nat := 3 * (i + 1) + 5

theorem bodyTrace (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    (MachineComposition.advance (TM2.step program))^[bodySteps i]
      (some ⟨some .inputTag, initialState, tapes base m i d output⟩) =
      some ⟨some .guard, initialState, tapes base m (i + 1) (d - 1)
        ((tokenBits (termTokens i d)).reverse ++ output)⟩ := by
  have tag : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .inputTag, initialState, tapes base m i d output⟩) =
      some ⟨some .scan, initialState,
        tapes base m i d ((encodeWord 5).reverse ++ output)⟩ := by
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      inputTagStep base m i d output
  have index := indexTrace base m i d ((encodeWord 5).reverse ++ output)
  let out := (encodeWord i).reverse ++ ((encodeWord 5).reverse ++ output)
  have test : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .test, initialState, tapes base m i d out⟩) =
      some ⟨some (.result (decide (d = 0))), initialState,
        tapes base m i (d - 1) out⟩ := by
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      thresholdStep base m i d out
  have result : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some (.result (decide (d = 0))), initialState,
        tapes base m i (d - 1) out⟩) =
      some ⟨some .guard, initialState, tapes base m (i + 1) (d - 1)
        ((encodeWords [if decide (d = 0) then 1 else 0, 3]).reverse ++ out)⟩ := by
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      resultStep base m i (d - 1) out (decide (d = 0))
  have whole := chain (chain (chain tag index) test) result
  have htime : 1 + (3 * (i + 1) + 2) + 1 + 1 = bodySteps i := by
    unfold bodySteps
    omega
  rw [htime] at whole
  simpa only [termTokens_bits, List.reverse_append, List.append_assoc, out] using whole

theorem guardStep_succ (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    TM2.step program ⟨some .guard, initialState, tapes base (m + 1) i d output⟩ =
      some ⟨some .inputTag, initialState, tapes base m i d output⟩ := by
  simpa only [counterTapes_remaining, initialState] using
    MachineUnaryCounter.guardStep_succ Tape.remaining Label.guard Label.inputTag Label.done
      program rfl (tapes base (m + 1) i d output) m [] ((), ()) none

theorem guardStep_zero (base : Tape → List Bool) (i d : Nat) (output : List Bool) :
    TM2.step program ⟨some .guard, initialState, tapes base 0 i d output⟩ =
      some ⟨some .done, initialState, tapes base 0 i d output⟩ := by
  simpa only [counterTapes_remaining, initialState] using
    MachineUnaryCounter.guardStep_zero Tape.remaining Label.guard Label.inputTag Label.done
      program rfl (tapes base 0 i d output) [] ((), ()) none

theorem tokens_append_bits (xs ys : List Token) :
    tokenBits (xs ++ ys) = tokenBits xs ++ tokenBits ys := by
  simp [tokenBits, tokenWords, List.flatMap_append]

def selectorSteps : Nat → Nat → Nat
  | _, 0 => 1
  | i, m + 1 => 1 + bodySteps i + selectorSteps (i + 1) m

theorem selectorTrace (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    (MachineComposition.advance (TM2.step program))^[selectorSteps i m]
      (some ⟨some .guard, initialState, tapes base m i d output⟩) =
      some ⟨some .done, initialState, tapes base 0 (i + m) (d - m)
        ((tokenBits (InitializationTemplate.selectorLoopTokens m i d)).reverse ++ output)⟩ := by
  induction m generalizing i d output with
  | zero =>
    simpa only [selectorSteps, InitializationTemplate.selectorLoopTokens,
      InitializationTemplate.forTokens, tokenBits, tokenWords, List.flatMap_nil,
      encodeWords, List.reverse_nil, List.nil_append, Nat.add_zero, Nat.sub_zero,
      Function.iterate_one, MachineComposition.advance_some] using
      guardStep_zero base i d output
  | succ m ih =>
    have guard : (MachineComposition.advance (TM2.step program))^[1]
        (some ⟨some .guard, initialState, tapes base (m + 1) i d output⟩) =
        some ⟨some .inputTag, initialState, tapes base m i d output⟩ := by
      simpa only [Function.iterate_one, MachineComposition.advance_some] using
        guardStep_succ base m i d output
    have body := bodyTrace base m i d output
    have rest := ih (i + 1) (d - 1) ((tokenBits (termTokens i d)).reverse ++ output)
    have whole := chain (chain guard body) rest
    have hs : InitializationTemplate.selectorLoopTokens (m + 1) i d =
        termTokens i d ++ InitializationTemplate.selectorLoopTokens m (i + 1) (d - 1) :=
      InitializationTemplate.selectorLoopTokens_succ m i d
    rw [hs, tokens_append_bits, List.reverse_append, List.append_assoc]
    simpa only [selectorSteps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.sub_sub] using whole

theorem selectorSteps_le (i m : Nat) :
    selectorSteps i m ≤ m * (3 * (i + m) + 6) + 1 := by
  induction m generalizing i with
  | zero => simp [selectorSteps]
  | succ m ih =>
    let B := 3 * (i + (m + 1)) + 6
    have hbody : 1 + bodySteps i ≤ B := by unfold bodySteps B; omega
    have hrest : selectorSteps (i + 1) m ≤ m * B + 1 := by
      simpa only [B, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1)
    calc
      selectorSteps i (m + 1) = (1 + bodySteps i) + selectorSteps (i + 1) m := rfl
      _ ≤ B + (m * B + 1) := Nat.add_le_add hbody hrest
      _ = (m + 1) * B + 1 := by rw [Nat.succ_mul]; omega

def selectorInTime (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .guard, initialState, tapes base m i d output⟩
      (some ⟨some .done, initialState, tapes base 0 (i + m) (d - m)
        ((tokenBits (InitializationTemplate.selectorLoopTokens m i d)).reverse ++ output)⟩)
      (m * (3 * (i + m) + 6) + 1) where
  steps := selectorSteps i m
  evals_in_steps := selectorTrace base m i d output
  steps_le_m := selectorSteps_le i m

theorem tapes_rawInput (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    tapes base m i d output .rawInput = base .rawInput := rfl

theorem tapes_witnessBound (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    tapes base m i d output .witnessBound = base .witnessBound := rfl

theorem tapes_capacity (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    tapes base m i d output .capacity = base .capacity := rfl

theorem tapes_closure (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    tapes base m i d output .closure = base .closure := rfl

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine

end OAI
