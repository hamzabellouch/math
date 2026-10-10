import OAI.Computability.BinPacking.Search.SearchFinalizeMachine
import OAI.Computability.BinPacking.Search.SearchInitialItemsMachine
import OAI.Computability.BinPacking.Search.SearchInitialShapeMachine
import OAI.Computability.BinPacking.Search.SearchPrepareMachine
import OAI.Computability.BinPacking.Search.SearchUpdateMachine

namespace OAI

namespace BinPackingGap.SearchInitialEmitMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution
open SearchInitializeEncoding

abbrev Tape := Fin 7
abbrev Alphabet (_ : Tape) := Bool
abbrev Flags := Bool × Bool
abbrev Register := MachineUnaryMultiply.State Flags

inductive Label
  | start | count | fixed | reverseRaw | prependRaw | pushHeader | zeroFuel
  | multiply (phase : MachineUnaryMultiply.Label)
  deriving DecidableEq, Fintype

def clean (flags : Flags) : Register := ((flags, ()), none)

def mulTape : Fin 5 → Tape
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 6
  | _ => 4

def mulSlots : Fin 5 ↪ Tape :=
  ⟨mulTape, by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [mulTape]⟩

@[simp] private theorem mulSlots_apply (i : Fin 5) : mulSlots i = mulTape i := by
  simp only [mulSlots]
  rfl

def dispatch (valid : Bool) : Label := if valid then .fixed else .reverseRaw

def finishLabel (valid : Bool) : Label :=
  if valid then .multiply .copyDrain else .zeroFuel

def header (flags : Flags) : List Bool :=
  if flags.1 then
    if flags.2 then [false, false, true, false, false, false]
    else [true, false, false, false, false]
  else [true, true, false, false, false]

def code : Label → TM2.Stmt Alphabet Label Register
  | .start =>
      .pop 0 (fun _ bit => clean (bit.getD false, false))
        (.push 1 (fun _ => false)
          (.push 2 (fun _ => false)
            (.push 3 (fun _ => false)
              (.push 5 (fun _ => false) (.goto fun _ => .count)))))
  | .count =>
      .pop 0 (fun state bit => (state.1, bit))
        (.branch (fun state => state.2.getD false)
          (.push 2 (fun _ => true)
            (.push 3 (fun _ => true)
              (.push 5 (fun _ => true)
                (.load (fun state => clean (state.1.1.1, true))
                  (.goto fun _ => .count)))))
          (.push 3 (fun _ => true)
            (.load (fun state => clean state.1.1)
              (.goto fun state => dispatch state.1.1.1))))
  | .fixed =>
      .pop 5 (fun state bit => (state.1, bit))
        (.branch (fun state => state.2.getD false)
          (.push 1 (fun _ => false)
            (.push 1 (fun _ => true)
              (.load (fun state => clean state.1.1) (.goto fun _ => .fixed))))
          (.load (fun state => clean state.1.1) (.goto fun _ => .reverseRaw)))
  | .reverseRaw => loopAt 0 4 id false .reverseRaw (some .prependRaw)
  | .prependRaw => loopAt 4 1 id false .prependRaw (some .pushHeader)
  | .pushHeader =>
      .branch (fun state => state.1.1.1)
        (.branch (fun state => state.1.1.2)
          (pushWord 1 (header (true, true)).reverse
            (.goto fun _ => .multiply .copyDrain))
          (pushWord 1 (header (true, false)).reverse
            (.goto fun _ => .multiply .copyDrain)))
        (pushWord 1 (header (false, false)).reverse (.goto fun _ => .zeroFuel))
  | .zeroFuel => .push 1 (fun _ => false) .halt
  | .multiply phase => MachineUnaryMultiply.statement mulSlots Label.multiply none phase

def program : MachineCanonicalOutput.Program Tape Label Register where
  input := 0
  output := 1
  main := .start
  initial := clean (false, false)
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

def tapes (input output left right scratch fixed counter : List Bool) : Tape → List Bool
  | 0 => input
  | 1 => output
  | 2 => left
  | 3 => right
  | 4 => scratch
  | 5 => fixed
  | _ => counter

def cfg (label : Option Label) (flags : Flags)
    (input output left right scratch fixed counter : List Bool) : machine.Cfg :=
  ⟨label, clean flags, tapes input output left right scratch fixed counter⟩

@[simp] private theorem tapes_input (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 0 = input := rfl

@[simp] private theorem update_input (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 0 replacement =
      tapes replacement output left right scratch fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] private theorem tapes_output (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 1 = output := rfl

@[simp] private theorem update_output (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 1 replacement =
      tapes input replacement left right scratch fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] private theorem tapes_left (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 2 = left := rfl

@[simp] private theorem update_left (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 2 replacement =
      tapes input output replacement right scratch fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] private theorem tapes_right (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 3 = right := rfl

@[simp] private theorem update_right (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 3 replacement =
      tapes input output left replacement scratch fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] private theorem tapes_scratch (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 4 = scratch := rfl

@[simp] private theorem update_scratch (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 4 replacement =
      tapes input output left right replacement fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] private theorem tapes_fixed (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 5 = fixed := rfl

@[simp] private theorem update_fixed (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 5 replacement =
      tapes input output left right scratch replacement counter := by
  funext k; fin_cases k <;> rfl

@[simp] private theorem tapes_counter (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 6 = counter := rfl

@[simp] private theorem update_counter (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 6 replacement =
      tapes input output left right scratch fixed replacement := by
  funext k; fin_cases k <;> rfl

def oneStep {start finish : machine.Cfg}
    (step : machine.step start = some finish) :
    StateTransition.EvalsToInTime machine.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    change machine.step start = some finish
    exact step
  steps_le_m := Nat.le_refl _

def join {start middle finish : machine.Cfg} {firstTime secondTime : Nat}
    (first : StateTransition.EvalsToInTime machine.step start (some middle) firstTime)
    (second : StateTransition.EvalsToInTime machine.step middle (some finish) secondTime) :
    StateTransition.EvalsToInTime machine.step start (some finish) (firstTime + secondTime) := by
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans machine.step firstTime secondTime
      start middle (some finish) first second

def enlarge {start finish : machine.Cfg} {time budget : Nat}
    (run : StateTransition.EvalsToInTime machine.step start (some finish) time)
    (bounded : time ≤ budget) :
    StateTransition.EvalsToInTime machine.step start (some finish) budget where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans bounded

def observed (n : Nat) (seen : Bool) : Bool := if n = 0 then seen else true

@[simp] theorem observed_zero (seen : Bool) : observed 0 seen = seen := rfl

@[simp] theorem observed_succ (n : Nat) (seen : Bool) : observed (n + 1) seen = true := by
  simp [observed]

@[simp] theorem observed_true (n : Nat) : observed n true = true := by
  simp [observed]

def initialFlags (valid : Bool) (n : Nat) : Flags := (valid, observed n false)

def fixedWord (n : Nat) : List Bool := SearchEncoding.fixedBits (List.replicate n none)

@[simp] theorem fixedWord_zero : fixedWord 0 = [false] := rfl

@[simp] theorem fixedWord_succ (n : Nat) :
    fixedWord (n + 1) = true :: false :: fixedWord n := rfl

theorem startStep (valid : Bool) (input : List Bool) :
    machine.step (cfg (some .start) (false, false) (valid :: input) [] [] [] [] [] []) =
      some (cfg (some .count) (valid, false) input [false] [false] [false] [] [false] []) := by
  change some (TM2.stepAux (code .start) _ _) = _
  simp [code, cfg, clean, TM2.stepAux]
  all_goals rfl

theorem countStep_true (valid seen : Bool) (m : Nat) (input output : List Bool) :
    machine.step (cfg (some .count) (valid, seen) (true :: input) output
      (encodeWord m) (encodeWord m) [] (encodeWord m) []) =
      some (cfg (some .count) (valid, true) input output
        (encodeWord (m + 1)) (encodeWord (m + 1)) [] (encodeWord (m + 1)) []) := by
  change some (TM2.stepAux (code .count) _ _) = _
  simp [code, cfg, clean, TM2.stepAux, encodeWord, List.replicate_succ]
  all_goals rfl

theorem countStep_false (valid seen : Bool) (m : Nat) (input output : List Bool) :
    machine.step (cfg (some .count) (valid, seen) (false :: input) output
      (encodeWord m) (encodeWord m) [] (encodeWord m) []) =
      some (cfg (some (dispatch valid)) (valid, seen) input output
        (encodeWord m) (encodeWord (m + 1)) [] (encodeWord m) []) := by
  change some (TM2.stepAux (code .count) _ _) = _
  simp [code, cfg, clean, TM2.stepAux, encodeWord, List.replicate_succ]
  all_goals rfl

theorem countTrace (n m : Nat) (input output : List Bool) (valid seen : Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .count) (valid, seen) (encodeWord n ++ input) output
        (encodeWord m) (encodeWord m) [] (encodeWord m) [])) =
      some (cfg (some (dispatch valid)) (valid, observed n seen) input output
        (encodeWord (m + n)) (encodeWord (m + n + 1)) [] (encodeWord (m + n)) []) := by
  induction n generalizing m seen with
  | zero =>
      simpa only [Nat.zero_add, Nat.add_zero, observed_zero, Function.iterate_one,
        advance_some, encodeWord, List.replicate_zero, List.nil_append,
        List.singleton_append] using countStep_false valid seen m input output
  | succ n ih =>
      rw [show encodeWord (n + 1) ++ input = true :: (encodeWord n ++ input) by rfl]
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [countStep_true]
      simpa only [observed_true, observed_succ, Nat.add_assoc, Nat.add_comm 1 n] using
        ih (m + 1) true

def countInTime (valid seen : Bool) (n m : Nat) (input output : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .count) (valid, seen) (encodeWord n ++ input) output
        (encodeWord m) (encodeWord m) [] (encodeWord m) [])
      (some (cfg (some (dispatch valid)) (valid, observed n seen) input output
        (encodeWord (m + n)) (encodeWord (m + n + 1)) [] (encodeWord (m + n)) []))
      (n + 1) where
  steps := n + 1
  evals_in_steps := countTrace n m input output valid seen
  steps_le_m := Nat.le_refl _

theorem fixedStep_true (flags : Flags) (n m : Nat) (input left right : List Bool) :
    machine.step (cfg (some .fixed) flags input (fixedWord m)
      left right [] (encodeWord (n + 1)) []) =
      some (cfg (some .fixed) flags input (fixedWord (m + 1))
        left right [] (encodeWord n) []) := by
  change some (TM2.stepAux (code .fixed) _ _) = _
  simp [code, cfg, clean, TM2.stepAux, encodeWord, List.replicate_succ]
  all_goals rfl

theorem fixedStep_zero (flags : Flags) (m : Nat) (input left right : List Bool) :
    machine.step (cfg (some .fixed) flags input (fixedWord m)
      left right [] (encodeWord 0) []) =
      some (cfg (some .reverseRaw) flags input (fixedWord m) left right [] [] []) := by
  change some (TM2.stepAux (code .fixed) _ _) = _
  simp [code, cfg, clean, TM2.stepAux, encodeWord]
  all_goals rfl

theorem fixedTrace (n m : Nat) (flags : Flags) (input left right : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .fixed) flags input (fixedWord m)
        left right [] (encodeWord n) [])) =
      some (cfg (some .reverseRaw) flags input (fixedWord (m + n)) left right [] [] []) := by
  induction n generalizing m with
  | zero =>
      simpa only [Nat.zero_add, Nat.add_zero, Function.iterate_one, advance_some] using
        fixedStep_zero flags m input left right
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [fixedStep_true]
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih (m + 1)

def fixedInTime (n m : Nat) (flags : Flags) (input left right : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .fixed) flags input (fixedWord m) left right [] (encodeWord n) [])
      (some (cfg (some .reverseRaw) flags input (fixedWord (m + n)) left right [] [] []))
      (n + 1) where
  steps := n + 1
  evals_in_steps := fixedTrace n m flags input left right
  steps_le_m := Nat.le_refl _

def selectedFixed (valid : Bool) (n : Nat) : List Bool :=
  if valid then fixedWord n else fixedWord 0

def residualFixed (valid : Bool) (n : Nat) : List Bool :=
  if valid then [] else encodeWord n

def prepareInTime (valid : Bool) (n : Nat) (input : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .start) (false, false) (valid :: (encodeWord n ++ input)) [] [] [] [] [] [])
      (some (cfg (some .reverseRaw) (initialFlags valid n) input (selectedFixed valid n)
        (encodeWord n) (encodeWord (n + 1)) [] (residualFixed valid n) []))
      (2 * n + 3) := by
  have first := oneStep (startStep valid (encodeWord n ++ input))
  have counted := countInTime valid false n 0 input [false]
  simp only [Nat.zero_add] at counted
  have initialRun := join first counted
  cases valid with
  | false =>
      simpa only [dispatch, Bool.false_eq_true, ↓reduceIte, initialFlags, selectedFixed,
        residualFixed, fixedWord_zero] using
        enlarge initialRun (by omega : 1 + (n + 1) ≤ 2 * n + 3)
  | true =>
      have fixed := fixedInTime n 0 (initialFlags true n) input
        (encodeWord n) (encodeWord (n + 1))
      simp only [Nat.zero_add] at fixed
      have full := join initialRun fixed
      simpa [dispatch, ↓reduceIte, initialFlags, selectedFixed,
        residualFixed, fixedWord_zero] using
        enlarge full (by omega : (1 + (n + 1)) + (n + 1) ≤ 2 * n + 3)

def prependRawInTime (flags : Flags) (input output left right fixed : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .reverseRaw) flags input output left right [] fixed [])
      (some (cfg (some .pushHeader) flags [] (input ++ output) left right [] fixed []))
      (2 * (input.length + 1)) := by
  have first := transferAtInTime (0 : Tape) 4 (by decide) id false
    .reverseRaw (some .prependRaw) code rfl
    (tapes input output left right [] fixed []) (flags, ()) none
  have second := transferAtInTime (4 : Tape) 1 (by decide) id false
    .prependRaw (some .pushHeader) code rfl
    (tapes [] output left right input.reverse fixed []) (flags, ()) none
  have first' : StateTransition.EvalsToInTime machine.step
      (cfg (some .reverseRaw) flags input output left right [] fixed [])
      (some (cfg (some .prependRaw) flags [] output left right input.reverse fixed []))
      (input.length + 1) := by
    change StateTransition.EvalsToInTime (TM2.step code)
      ⟨some .reverseRaw, clean flags, tapes input output left right [] fixed []⟩
      (some ⟨some .prependRaw, clean flags, tapes [] output left right input.reverse fixed []⟩)
      (input.length + 1)
    simpa only [tapesAt, update_input, update_scratch, tapes_input, tapes_scratch,
      List.map_id_fun, id_eq, List.append_nil, cfg, clean] using first
  have second' : StateTransition.EvalsToInTime machine.step
      (cfg (some .prependRaw) flags [] output left right input.reverse fixed [])
      (some (cfg (some .pushHeader) flags [] (input ++ output) left right [] fixed []))
      (input.length + 1) := by
    change StateTransition.EvalsToInTime (TM2.step code)
      ⟨some .prependRaw, clean flags, tapes [] output left right input.reverse fixed []⟩
      (some ⟨some .pushHeader, clean flags, tapes [] (input ++ output) left right [] fixed []⟩)
      (input.length + 1)
    simpa only [tapesAt, update_scratch, update_output, tapes_scratch, tapes_output,
      List.map_id_fun, id_eq, List.reverse_reverse, List.length_reverse, cfg, clean] using second
  exact enlarge (join first' second') (by omega)

theorem headerStep (valid seen : Bool) (output left right fixed : List Bool) :
    machine.step (cfg (some .pushHeader) (valid, seen) [] output left right [] fixed []) =
      some (cfg (some (finishLabel valid)) (valid, seen) []
        (header (valid, seen) ++ output) left right [] fixed []) := by
  cases valid <;> cases seen <;>
    change some (TM2.stepAux (code .pushHeader) _ _) = _ <;>
    simp [code, header, finishLabel, cfg, clean, TM2.stepAux, pushWord]
  all_goals rfl

theorem zeroFuelStep (seen : Bool) (output left right fixed : List Bool) :
    machine.step (cfg (some .zeroFuel) (false, seen) [] output left right [] fixed []) =
      some (cfg none (false, seen) [] (false :: output) left right [] fixed []) := by
  change some (TM2.stepAux (code .zeroFuel) _ _) = _
  simp [code, cfg, clean, TM2.stepAux]
  all_goals rfl

def fuelValue (valid : Bool) (n : Nat) : Nat := if valid then n * (n + 1) else 0

def fuelTime (valid : Bool) (n : Nat) : Nat :=
  if valid then MachineUnaryMultiply.steps n (n + 1) else 1

def fuelInTime (valid seen : Bool) (n : Nat) (output fixed : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (finishLabel valid)) (valid, seen) [] output
        (encodeWord n) (encodeWord (n + 1)) [] fixed [])
      (some (cfg none (valid, seen) [] (encodeWord (fuelValue valid n) ++ output)
        (encodeWord n) (encodeWord (n + 1)) [] fixed []))
      (fuelTime valid n) := by
  cases valid with
  | false =>
      simpa only [finishLabel, fuelValue, fuelTime, Bool.false_eq_true, ↓reduceIte,
        encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
        oneStep (zeroFuelStep seen output (encodeWord n) (encodeWord (n + 1)) fixed)
  | true =>
      have run := MachineUnaryMultiply.multiplyInTime mulSlots Label.multiply none code
        (fun _ => rfl) (tapes [] output (encodeWord n) (encodeWord (n + 1)) [] fixed [])
        n (n + 1) rfl rfl rfl rfl (true, seen) none
      change StateTransition.EvalsToInTime (TM2.step code)
        ⟨some (.multiply .copyDrain), clean (true, seen),
          tapes [] output (encodeWord n) (encodeWord (n + 1)) [] fixed []⟩
        (some ⟨none, clean (true, seen),
          tapes [] (encodeWord (n * (n + 1)) ++ output)
            (encodeWord n) (encodeWord (n + 1)) [] fixed []⟩)
        (MachineUnaryMultiply.steps n (n + 1))
      simpa [finishLabel, fuelValue, fuelTime, ↓reduceIte,
        MachineUnaryMultiply.resultTapes, mulTape,
        tapes_output, update_output, cfg, clean] using! run

def bodyWord (valid : Bool) (n : Nat) (input : List Bool) : List Bool :=
  header (initialFlags valid n) ++ (input ++ selectedFixed valid n)

def outputWord (valid : Bool) (n : Nat) (input : List Bool) : List Bool :=
  encodeWord (fuelValue valid n) ++ bodyWord valid n input

def finishTapes (valid : Bool) (n : Nat) (input : List Bool) : Tape → List Bool :=
  tapes [] (outputWord valid n input) (encodeWord n) (encodeWord (n + 1))
    [] (residualFixed valid n) []

def rawSteps (valid : Bool) (n inputLength : Nat) : Nat :=
  (2 * n + 3) + 2 * (inputLength + 1) + 1 + fuelTime valid n

def emitInTime (valid : Bool) (n : Nat) (input : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .start) (false, false) (valid :: (encodeWord n ++ input)) [] [] [] [] [] [])
      (some ⟨none, clean (initialFlags valid n), finishTapes valid n input⟩)
      (rawSteps valid n input.length) := by
  have first := prepareInTime valid n input
  have second := prependRawInTime (initialFlags valid n) input (selectedFixed valid n)
    (encodeWord n) (encodeWord (n + 1)) (residualFixed valid n)
  have third := oneStep (headerStep valid (observed n false)
    (input ++ selectedFixed valid n) (encodeWord n) (encodeWord (n + 1))
    (residualFixed valid n))
  have fourth := fuelInTime valid (observed n false) n (bodyWord valid n input)
    (residualFixed valid n)
  have all := join (join (join first second) third) fourth
  simpa only [rawSteps, finishTapes, outputWord, bodyWord, initialFlags, cfg] using! all

theorem bodyWord_eq (items : RawInstance) (valid : Bool) :
    bodyWord valid items.length (BinaryEncoding.rawInstanceBits items) =
      SearchEncoding.stateBits (SearchSemantics.initial items valid) := by
  cases valid with
  | false =>
      simp [bodyWord, header, initialFlags, selectedFixed, SearchSemantics.initial,
        SearchEncoding.stateBits, SearchEncoding.phaseBits, fixedWord,
        SearchEncoding.fixedBits, BinaryEncoding.listBits, encodeWord]
  | true =>
      cases items with
      | nil =>
          simp [bodyWord, header, initialFlags, observed, selectedFixed,
            SearchSemantics.initial, SearchEncoding.stateBits, SearchEncoding.phaseBits,
            fixedWord, SearchEncoding.fixedBits, BinaryEncoding.listBits, encodeWord]
      | cons item items =>
          simp [bodyWord, header, initialFlags, observed, selectedFixed,
            SearchSemantics.initial, SearchEncoding.stateBits, SearchEncoding.phaseBits,
            fixedWord, encodeWord]

theorem outputWord_eq (items : RawInstance) (valid : Bool) :
    outputWord valid items.length (BinaryEncoding.rawInstanceBits items) =
      MachineBoundedIteration.inputBits SearchEncoding.stateBits (emit (items, valid)) := by
  simp only [outputWord, bodyWord_eq, MachineBoundedIteration.inputBits,
    emit, fuelValue, SearchSemantics.fuel]

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .start) (false, false) input [] [] [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  change Tape at k
  fin_cases k <;> rfl

noncomputable def rawTime : Polynomial Nat := 100 * (Polynomial.X + 1) ^ 2

private theorem rawSteps_le (items : RawInstance) (valid : Bool) :
    rawSteps valid items.length (BinaryEncoding.rawInstanceBits items).length ≤
      rawTime.eval (dataBits (items, valid)).length := by
  have hlen : (dataBits (items, valid)).length =
      items.length + (BinaryEncoding.rawInstanceBits items).length + 2 := by
    simp only [dataBits, List.length_cons, List.length_append, encodeWord_length]
    omega
  let n := items.length
  let r := (BinaryEncoding.rawInstanceBits items).length
  have hn : n ≤ n + r + 2 := by omega
  have hn' : n + 1 ≤ (n + r + 2) + 1 := by omega
  have hp := Nat.mul_le_mul hn hn'
  rw [hlen]
  change rawSteps valid n r ≤ rawTime.eval (n + r + 2)
  simp only [rawTime, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  cases valid <;>
    simp [rawSteps, fuelTime, Bool.false_eq_true, ↓reduceIte,
      MachineUnaryMultiply.steps] <;>
    nlinarith [Nat.zero_le ((n + r + 2) * (n + r + 2))]

noncomputable def rawRun (data : Data) :
    MachineCanonicalOutput.TerminalRun program (dataBits data)
      (MachineBoundedIteration.inputBits SearchEncoding.stateBits (emit data))
      (rawTime.eval (dataBits data).length) := by
  rcases data with ⟨items, valid⟩
  have run := emitInTime valid items.length (BinaryEncoding.rawInstanceBits items)
  refine {
    state := clean (initialFlags valid items.length)
    tapes := finishTapes valid items.length (BinaryEncoding.rawInstanceBits items)
    execution := ?_
    output_eq := ?_ }
  · simpa only [init_eq, dataBits] using enlarge run (rawSteps_le items valid)
  · change outputWord valid items.length (BinaryEncoding.rawInstanceBits items) = _
    exact outputWord_eq items valid

def cleanupTapes : List Tape := [0, 2, 3, 4, 5, 6]

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  fin_cases k <;> simp [cleanupTapes, program]

noncomputable def computation :
    TM2ComputableInPolyTime dataBits
      (MachineBoundedIteration.inputBits SearchEncoding.stateBits) emit :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    dataBits (MachineBoundedIteration.inputBits SearchEncoding.stateBits) emit rawTime rawRun

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes
    cleanup_complete dataBits (MachineBoundedIteration.inputBits SearchEncoding.stateBits)
    emit rawTime rawRun

end BinPackingGap.SearchInitialEmitMachine

namespace BinPackingGap.SearchInitializeMachine

open Turing BinPackingGames.Foundations.Complexity
open SearchInitializeEncoding

noncomputable def shapeComputation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) shapeBits
      (id : List Bool → List Bool) where
  tm := SearchInitialShapeMachine.machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    change TM2OutputsInTime SearchInitialShapeMachine.machine (input.map id)
      (some ((shapeBits input).map id))
      ((2 * Polynomial.X + 3 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, shapeBits, SearchInitialShapeMachine.decodeAccepts,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      using SearchInitialShapeMachine.outputsInTime input

theorem shapeFinite : MachineFiniteAlphabet.FiniteAlphabet shapeComputation.tm :=
  SearchInitialShapeMachine.machine_finiteAlphabet

noncomputable def composed :
    TM2ComputableInPolyTime (id : List Bool → List Bool)
      (MachineBoundedIteration.inputBits SearchEncoding.stateBits)
      (fun input => emit (classify input)) :=
  MachineSequential.composeBits (f := id) (g := fun input => emit (classify input))
    shapeComputation
    (MachineSequential.composeBits (f := classify) (g := emit)
      SearchInitialItemsMachine.computation
      SearchInitialEmitMachine.computation)

noncomputable def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool)
      (MachineBoundedIteration.inputBits SearchEncoding.stateBits)
      SearchMachineComposition.initialize where
  tm := composed.tm
  inputAlphabet := composed.inputAlphabet
  outputAlphabet := composed.outputAlphabet
  time := composed.time
  outputsFun input := by
    simpa only [emit_classify] using composed.outputsFun input

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm := by
  change MachineFiniteAlphabet.FiniteAlphabet composed.tm
  unfold composed
  exact MachineFiniteAlphabet.composeBits (f := id)
    (g := fun input => emit (classify input)) shapeComputation _ shapeFinite
    (MachineFiniteAlphabet.composeBits (f := classify) (g := emit)
      SearchInitialItemsMachine.computation
      SearchInitialEmitMachine.computation SearchInitialItemsMachine.finiteAlphabet
      SearchInitialEmitMachine.finiteAlphabet)

end BinPackingGap.SearchInitializeMachine

namespace BinPackingGap.SearchStageMachines

noncomputable def stages : SearchMachineComposition.Stages where
  initializeComputation := SearchInitializeMachine.computation
  initializeFinite := SearchInitializeMachine.finiteAlphabet
  prepareComputation := SearchPrepareMachine.computation
  prepareFinite := SearchPrepareMachine.finiteAlphabet
  updateComputation := SearchUpdateMachine.computation
  updateFinite := SearchUpdateMachine.finiteAlphabet
  finalizeComputation := SearchFinalizeMachine.computation
  finalizeFinite := SearchFinalizeMachine.finiteAlphabet

end BinPackingGap.SearchStageMachines

end OAI
