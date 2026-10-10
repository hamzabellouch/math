import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI


namespace PerfectCompleteness.BinaryPairMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Tape := Fin 3
abbrev Label := Fin 5
abbrev State := Unit × Option Bool
abbrev Alphabet (_ : Tape) := Bool

def stop (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => ((), none)) (.goto fun _ => label)

def count : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (stop 4)
      (.branch (fun state => state.2.getD false)
        (.push 1 (fun _ => true) (.goto fun _ => 0))
        (stop 1)))

def copy : TM2.Stmt Alphabet Label State :=
  .pop 1 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push 2 (fun state => state.2.getD false) (.goto fun _ => 1))
          (stop 4)))
      (stop 2))

def program (label : Label) : TM2.Stmt Alphabet Label State :=
  if label = 0 then count
  else if label = 1 then copy
  else if label = 2 then loopAt 2 1 id false 2 (some 3)
  else .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := 0
  σ := State
  initialState := ((), none)
  m := program

def tapes (input counter saved : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then counter else saved

def cfg (label : Option Label) (input counter saved : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input counter saved⟩

@[simp] private theorem tapes_zero (input counter saved : List Bool) :
    tapes input counter saved 0 = input := rfl

@[simp] private theorem tapes_one (input counter saved : List Bool) :
    tapes input counter saved 1 = counter := rfl

@[simp] private theorem tapes_two (input counter saved : List Bool) :
    tapes input counter saved 2 = saved := rfl

private theorem update_zero (input counter saved replacement : List Bool) :
    Function.update (tapes input counter saved) 0 replacement =
      tapes replacement counter saved := by
  funext k
  fin_cases k <;> simp [tapes]

private theorem update_one (input counter saved replacement : List Bool) :
    Function.update (tapes input counter saved) 1 replacement =
      tapes input replacement saved := by
  funext k
  fin_cases k <;> simp [tapes]

private theorem update_two (input counter saved replacement : List Bool) :
    Function.update (tapes input counter saved) 2 replacement =
      tapes input counter replacement := by
  funext k
  fin_cases k <;> simp [tapes]

theorem countStep_true (input counter saved : List Bool) (register : Option Bool) :
    machine.step (cfg (some 0) (true :: input) counter saved register) =
      some (cfg (some 0) input (true :: counter) saved (some true)) := by
  change some (TM2.stepAux (program 0) _ _) = _
  simp [program, count, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem countStep_false (input counter saved : List Bool) (register : Option Bool) :
    machine.step (cfg (some 0) (false :: input) counter saved register) =
      some (cfg (some 1) input counter saved) := by
  change some (TM2.stepAux (program 0) _ _) = _
  simp [program, count, stop, cfg, TM2.stepAux, update_zero]
  rfl

theorem countTrace (n : Nat) (input counter saved : List Bool) (register : Option Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some 0) (encodeWord n ++ input) counter saved register)) =
      some (cfg (some 1) input (List.replicate n true ++ counter) saved) := by
  induction n generalizing counter register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, advance_some, encodeWord,
        List.replicate_zero, List.nil_append, List.singleton_append] using
        countStep_false input counter saved register
  | succ n ih =>
      rw [show encodeWord (n + 1) ++ input = true :: (encodeWord n ++ input) by
        simp only [encodeWord, List.replicate_succ, List.cons_append]]
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [countStep_true]
      rw [ih]
      rw [List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]

theorem copyStep_empty (input saved : List Bool) (register : Option Bool) :
    machine.step (cfg (some 1) input [] saved register) =
      some (cfg (some 2) input [] saved) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, copy, stop, cfg, TM2.stepAux, update_one]
  rfl

theorem copyStep_cons (bit : Bool) (input counter saved : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some 1) (bit :: input) (true :: counter) saved register) =
      some (cfg (some 1) input counter (bit :: saved) (some bit)) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, copy, cfg, TM2.stepAux, update_zero, update_one, update_two]
  rfl

theorem copyTrace (input suffix saved : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 1) (input ++ suffix) (List.replicate input.length true) saved register)) =
      some (cfg (some 2) suffix [] (input.reverse ++ saved)) := by
  induction input generalizing saved register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.nil_append, List.replicate_zero, List.reverse_nil] using
        copyStep_empty suffix saved register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.cons_append, List.replicate_succ, advance_some]
      rw [copyStep_cons, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem restoreTrace (input witness : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 2) witness [] input.reverse register)) =
      some (cfg (some 3) witness input []) := by
  change (nextAt (Γ := Alphabet) (1 : Tape) program)^[input.length + 1]
    (some ⟨some (2 : Label), ((), register), tapes witness [] input.reverse⟩) =
    some ⟨some (3 : Label), ((), none), tapes witness input []⟩
  have h := transferAt_steps (Γ := Alphabet) (σ := Unit) (2 : Tape) 1 (by decide)
    id false (2 : Label) (some 3) program (by simp [program])
    (tapes witness [] []) input.reverse [] () register
  simpa only [tapesAt, update_two, update_one, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, List.append_nil] using h

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some 0) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem pairTrace (input witness : List Bool) :
    (advance machine.step)^[3 * input.length + 3]
      (some (initList machine (CookLevin.pairBits (input, witness)))) =
      some (cfg (some 3) witness input []) := by
  have first := countTrace input.length (input ++ witness) [] [] none
  simp only [List.append_nil] at first
  have second := copyTrace input witness [] none
  simp only [List.append_nil] at second
  have third := restoreTrace input witness none
  have full := joinTrace (joinTrace first second) third
  have htime : (input.length + 1 + (input.length + 1)) + (input.length + 1) =
      3 * input.length + 3 := by omega
  rw [htime] at full
  simpa only [initList_eq, CookLevin.pairBits, List.append_assoc] using full

def pairInTime (input witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (CookLevin.pairBits (input, witness)))
      (some (cfg (some 3) witness input [])) (3 * input.length + 3) where
  steps := 3 * input.length + 3
  evals_in_steps := pairTrace input witness
  steps_le_m := Nat.le_refl _

theorem haltStep (input witness : List Bool) :
    machine.step (cfg (some 3) witness input []) = some (cfg none witness input []) := by
  change some (TM2.stepAux (program 3) _ _) = _
  simp [program, cfg, TM2.stepAux]
  rfl

def pairHaltInTime (input witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (CookLevin.pairBits (input, witness)))
      (some (cfg none witness input [])) (3 * input.length + 4) where
  steps := 3 * input.length + 4
  evals_in_steps := by
    change (advance machine.step)^[3 * input.length + 4]
      (some (initList machine (CookLevin.pairBits (input, witness)))) = _
    rw [show 3 * input.length + 4 = (3 * input.length + 3) + 1 by omega,
      Function.iterate_succ_apply', pairTrace, advance_some, haltStep]
  steps_le_m := Nat.le_refl _

theorem pairSteps_le_pairedLength (input witness : List Bool) :
    3 * input.length + 4 ≤ 3 * (CookLevin.pairBits (input, witness)).length + 4 := by
  rw [CookLevin.pairBits_length]
  dsimp only
  omega

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.BinaryPairMachine

end OAI
