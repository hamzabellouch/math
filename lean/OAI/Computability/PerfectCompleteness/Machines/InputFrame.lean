import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InputFrame


open Turing MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Tape := Fin 3
abbrev Label := Fin 5
abbrev State := Unit × Option Bool
abbrev Alphabet (_ : Tape) := Bool

def scan : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun s head => (s.1, head))
    (.branch (fun s => s.2.isSome)
      (.push 1 (fun s => s.2.getD false)
        (.push 2 (fun _ => true) (.goto fun _ => 1)))
      (.goto fun _ => 2))

def program (label : Label) : TM2.Stmt Alphabet Label State :=
  if label = 0 then .push 2 (fun _ => false) (.goto fun _ => 1)
  else if label = 1 then scan
  else if label = 2 then loopAt 1 0 id false 2 (some 3)
  else if label = 3 then loopAt 2 1 id false 3 (some 4)
  else loopAt 1 0 id false 4 none

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := 0
  σ := State
  initialState := ((), none)
  m := program

def tapes (input saved counter : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then saved else counter

def cfg (label : Option Label) (input saved counter : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input saved counter⟩

@[simp] private theorem tapes_zero (input saved counter : List Bool) :
    tapes input saved counter 0 = input := rfl

@[simp] private theorem tapes_one (input saved counter : List Bool) :
    tapes input saved counter 1 = saved := rfl

@[simp] private theorem tapes_two (input saved counter : List Bool) :
    tapes input saved counter 2 = counter := rfl

private theorem update_zero (input saved counter replacement : List Bool) :
    Function.update (tapes input saved counter) 0 replacement =
      tapes replacement saved counter := by
  funext k
  fin_cases k <;> simp [tapes]

private theorem update_one (input saved counter replacement : List Bool) :
    Function.update (tapes input saved counter) 1 replacement =
      tapes input replacement counter := by
  funext k
  fin_cases k <;> simp [tapes]

private theorem update_two (input saved counter replacement : List Bool) :
    Function.update (tapes input saved counter) 2 replacement =
      tapes input saved replacement := by
  funext k
  fin_cases k <;> simp [tapes]

theorem scanStep_nil (saved counter : List Bool) (register : Option Bool) :
    machine.step (cfg (some 1) [] saved counter register) =
      some (cfg (some 2) [] saved counter) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, scan, cfg, TM2.stepAux, tapes, update_zero]
  rfl

theorem scanStep_cons (bit : Bool) (input saved counter : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some 1) (bit :: input) saved counter register) =
      some (cfg (some 1) input (bit :: saved) (true :: counter) (some bit)) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, scan, cfg, TM2.stepAux, tapes, update_zero, update_one, update_two]
  rfl

theorem scanTrace (input saved counter : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 1) input saved counter register)) =
        some (cfg (some 2) [] (input.reverse ++ saved)
          (List.replicate input.length true ++ counter)) := by
  induction input generalizing saved counter register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
      List.reverse_nil, List.replicate_zero, List.nil_append] using
      scanStep_nil saved counter register
  | cons bit input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [scanStep_cons, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [List.replicate_succ']
    simp only [List.append_assoc, List.singleton_append]

theorem startStep (input : List Bool) :
    machine.step (initList machine input) = some (cfg (some 1) input [] [false]) := by
  change some (TM2.stepAux (program 0) ((),none) _) = _
  simp [program, TM2.stepAux, cfg]
  exact congrArg (fun stk : Tape → List Bool =>
    some (⟨some 1, ((), none), stk⟩ : machine.Cfg)) (by
      funext k
      fin_cases k <;> simp [tapes])

theorem restoreTrace (input : List Bool) (n : Nat) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 2) [] input.reverse (encodeWord n))) =
        some (cfg (some 3) input [] (encodeWord n)) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 0 (by decide)
    id false 2 (some 3) program (by simp [program])
    (tapes [] input.reverse (encodeWord n)) () none
  have ht : tapesAt 1 0 (tapes [] input.reverse (encodeWord n)) [] input =
      tapes input [] (encodeWord n) := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 0 program)^[input.length + 1]
    (some (cfg (some 2) [] input.reverse (encodeWord n))) = _
  simpa only [tapes_one, tapes_zero, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, List.append_nil, ht, nextAt, advance, cfg] using! h

theorem reverseCounterTrace (input : List Bool) (n : Nat) :
    (advance machine.step)^[n + 2]
      (some (cfg (some 3) input [] (encodeWord n))) =
        some (cfg (some 4) input (encodeWord n).reverse []) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 2 1 (by decide)
    id false 3 (some 4) program (by simp [program])
    (tapes input [] (encodeWord n)) () none
  have ht : tapesAt 2 1 (tapes input [] (encodeWord n)) [] (encodeWord n).reverse =
      tapes input (encodeWord n).reverse [] := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 1 program)^[n + 2]
    (some (cfg (some 3) input [] (encodeWord n))) = _
  simpa only [tapes_two, tapes_one, List.map_id_fun, id_eq, List.append_nil,
    encodeWord_length, Nat.add_assoc, ht, nextAt, advance, cfg] using! h

theorem prependTrace (input : List Bool) (n : Nat) :
    (advance machine.step)^[n + 2]
      (some (cfg (some 4) input (encodeWord n).reverse [])) =
        some (cfg none (encodeWord n ++ input) [] []) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 0 (by decide)
    id false 4 none program (by simp [program])
    (tapes input (encodeWord n).reverse []) () none
  have ht : tapesAt 1 0 (tapes input (encodeWord n).reverse []) [] (encodeWord n ++ input) =
      tapes (encodeWord n ++ input) [] [] := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 0 program)^[n + 2]
    (some (cfg (some 4) input (encodeWord n).reverse [])) = _
  simpa only [tapes_one, tapes_zero, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, encodeWord_length, Nat.add_assoc, ht, nextAt, advance, cfg] using! h

theorem stopped_eq_haltList (output : List Bool) :
    cfg none output [] [] = haltList machine output := by
  unfold cfg haltList
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem frameTrace (input : List Bool) :
    (advance machine.step)^[4 * input.length + 7]
      (some (initList machine input)) =
        some (haltList machine (encodeWord input.length ++ input)) := by
  have join :
      (advance machine.step)^[input.length + 2]
        ((advance machine.step)^[input.length + 2]
          ((advance machine.step)^[input.length + 1]
            ((advance machine.step)^[input.length + 1]
              ((advance machine.step)^[1] (some (initList machine input)))))) =
        (advance machine.step)^[4 * input.length + 7]
          (some (initList machine input)) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      ← Function.iterate_add_apply, ← Function.iterate_add_apply]
    congr 1
    omega
  rw [← join]
  simp only [Function.iterate_one, advance_some]
  rw [startStep, scanTrace]
  simp only [List.append_nil]
  change (advance machine.step)^[input.length + 2]
    ((advance machine.step)^[input.length + 2]
      ((advance machine.step)^[input.length + 1]
        (some (cfg (some 2) [] input.reverse (encodeWord input.length))))) = _
  rw [restoreTrace, reverseCounterTrace, prependTrace, stopped_eq_haltList]

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (fun input => encodeWord input.length ++ input) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * Polynomial.X + 7
  outputsFun input := {
    steps := 4 * input.length + 7
    evals_in_steps := by
      change (advance machine.step)^[4 * input.length + 7]
        (some (initList machine (input.map id))) =
          some (haltList machine ((encodeWord input.length ++ input).map id))
      simp only [List.map_id_fun, id_eq]
      exact frameTrace input
    steps_le_m := by simp }

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InputFrame

end OAI
