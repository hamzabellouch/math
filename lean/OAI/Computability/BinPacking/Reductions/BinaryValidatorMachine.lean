import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Reductions.BinaryTokenMachine

namespace OAI

namespace BinPackingCompleteness.BinaryValidatorMachine

open BinaryEncoding BinaryFormula

inductive Mode
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3) (last : Bool)
  | digit (slot : Fin 3)
  | done
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Mode :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

def nextMode : Mode → Bool → Mode
  | .clause, true => .sign 0
  | .clause, false => .done
  | .sign slot, _ => .name slot true
  | .name slot _, true => .digit slot
  | .name slot last, false => if last then afterName slot else .reject
  | .digit slot, bit => .name slot bit
  | .done, _ => .reject
  | .reject, _ => .reject

def run : Mode → List Bool → Mode
  | mode, [] => mode
  | mode, bit :: rest => run (nextMode mode bit) rest

@[simp] theorem run_reject (input : List Bool) : run .reject input = .reject := by
  induction input with
  | nil => rfl
  | cons bit input ih => simpa only [run, nextMode] using ih

theorem run_done_iff (input : List Bool) : run .done input = .done ↔ input = [] := by
  cases input with
  | nil => simp [run]
  | cons bit rest => simp [run, nextMode]

private theorem finalDigit_true_iff (bits : List Bool) :
    BinaryNameMachine.finalDigit bits (some true) = some true ↔
      BinaryNameMachine.canonical bits = true := by
  cases bits with
  | nil => simp [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
  | cons bit bits =>
      simp only [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
      have hsome : ∀ (ds : List Bool) (b : Bool),
          ∃ last, BinaryNameMachine.finalDigit ds (some b) = some last := by
        intro ds
        induction ds with
        | nil => intro b; exact ⟨b, rfl⟩
        | cons d ds ih => intro b; exact ih d
      obtain ⟨last, hlast⟩ := hsome bits bit
      rw [hlast]
      simp

theorem run_frame (slot : Fin 3) (bits rest : List Bool) (last : Bool)
    (valid : BinaryNameMachine.finalDigit bits (some last) = some true) :
    run (.name slot last) (frame bits ++ rest) = run (afterName slot) rest := by
  induction bits generalizing last with
  | nil =>
      have hlast : last = true := by simpa [BinaryNameMachine.finalDigit] using valid
      subst last
      simp [frame, run, nextMode]
  | cons bit bits ih =>
      have hvalid : BinaryNameMachine.finalDigit bits (some bit) = some true := valid
      simpa only [frame, List.cons_append, run, nextMode] using ih bit hvalid

theorem run_name (slot : Fin 3) (name : Nat) (rest : List Bool) :
    run (.name slot true) (nameBits name ++ rest) = run (afterName slot) rest := by
  apply run_frame
  exact (finalDigit_true_iff name.bits).mpr (BinaryParsing.canonical_nat_bits name)

theorem run_literal (slot : Fin 3) (literal : Literal) (rest : List Bool) :
    run (.sign slot) (literalBits literal ++ rest) = run (afterName slot) rest := by
  simpa only [literalBits, List.cons_append, run, nextMode] using
    run_name slot literal.name rest

theorem run_clause (clause : Clause) (rest : List Bool) :
    run (.sign 0) (clauseBits clause ++ rest) = run .clause rest := by
  simp [clauseBits, List.append_assoc, run_literal, afterName]

theorem run_clauses (clauses : List Clause) : run .clause (clausesBits clauses) = .done := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      change run (.sign 0) (clauseBits clause ++ clausesBits clauses) = .done
      rw [run_clause, ih]

theorem run_formula (formula : Formula) : run .clause (formulaBits formula) = .done :=
  run_clauses formula.clauses

theorem frame_inverse (slot : Fin 3) (last : Bool) (input : List Bool)
    (accepted : run (.name slot last) input = .done) :
    ∃ bits rest, input = frame bits ++ rest ∧
      BinaryNameMachine.finalDigit bits (some last) = some true ∧
      run (afterName slot) rest = .done := by
  induction input using List.twoStepInduction generalizing last with
  | nil => simp [run] at accepted
  | singleton flag =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], [], rfl, rfl, by simpa [run, nextMode] using accepted⟩
      | true => simp [run, nextMode] at accepted
  | cons_cons flag bit input ih _ =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], bit :: input, rfl, rfl,
                by simpa [run, nextMode] using accepted⟩
      | true =>
          have haccepted : run (.name slot bit) input = .done := by
            simpa only [run, nextMode] using accepted
          obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := ih bit haccepted
          refine ⟨bit :: bits, rest, ?_, hvalid, hrest⟩
          simp [frame, hinput]

theorem name_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.name slot true) input = .done) :
    ∃ name rest, input = nameBits name ++ rest ∧ run (afterName slot) rest = .done := by
  obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := frame_inverse slot true input accepted
  have hcanonical := (finalDigit_true_iff bits).mp hvalid
  have hbits := (BinaryParsing.canonical_iff bits).mp hcanonical
  refine ⟨bitsValue bits, rest, ?_, hrest⟩
  simpa only [nameBits, hbits] using hinput

theorem literal_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.sign slot) input = .done) :
    ∃ literal rest, input = literalBits literal ++ rest ∧ run (afterName slot) rest = .done := by
  cases input with
  | nil => simp [run] at accepted
  | cons sign input =>
      have haccepted : run (.name slot true) input = .done := accepted
      obtain ⟨name, rest, hinput, hrest⟩ := name_inverse slot input haccepted
      refine ⟨⟨name, sign⟩, rest, ?_, hrest⟩
      simp [literalBits, hinput]

theorem clause_inverse (input : List Bool) (accepted : run (.sign 0) input = .done) :
    ∃ clause rest, input = clauseBits clause ++ rest ∧ run .clause rest = .done := by
  obtain ⟨a, afterA, hA, acceptedA⟩ := literal_inverse 0 input accepted
  have hacceptedA : run (.sign 1) afterA = .done := by
    simpa [afterName] using acceptedA
  obtain ⟨b, afterB, hB, acceptedB⟩ := literal_inverse 1 afterA hacceptedA
  have hacceptedB : run (.sign 2) afterB = .done := by
    simpa [afterName] using acceptedB
  obtain ⟨c, rest, hC, acceptedC⟩ := literal_inverse 2 afterB hacceptedB
  have hrest : run .clause rest = .done := by simpa [afterName] using acceptedC
  refine ⟨#v[a, b, c], rest, ?_, hrest⟩
  simp [clauseBits, hA, hB, hC, List.append_assoc]

private theorem clauses_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .clause input = .done) :
    ∃ clauses, input = clausesBits clauses := by
  induction fuel generalizing input with
  | zero => omega
  | succ fuel ih =>
      cases input with
      | nil => simp [run] at accepted
      | cons flag input =>
          cases flag with
          | false =>
              have hdone : run .done input = .done := accepted
              have hempty := (run_done_iff input).mp hdone
              subst input
              exact ⟨[], rfl⟩
          | true =>
              have haccepted : run (.sign 0) input = .done := accepted
              obtain ⟨clause, rest, hinput, hrest⟩ := clause_inverse input haccepted
              have hlength := congrArg List.length hinput
              simp only [List.length_append] at hlength
              have henough : rest.length < fuel := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨clauses, hclauses⟩ := ih rest henough hrest
              refine ⟨clause :: clauses, ?_⟩
              simp [clausesBits, hinput, hclauses]

theorem run_clause_iff (input : List Bool) :
    run .clause input = .done ↔ ∃ formula, input = formulaBits formula := by
  constructor
  · intro accepted
    obtain ⟨clauses, hclauses⟩ :=
      clauses_inverse_aux (input.length + 1) input (by omega) accepted
    exact ⟨⟨clauses⟩, hclauses⟩
  · rintro ⟨formula, rfl⟩
    exact run_formula formula

def accepts (input : List Bool) : Bool := decide (run .clause input = .done)

theorem accepts_eq_decode (input : List Bool) :
    accepts input = (decodeFormula input).isSome := by
  cases parsed : decodeFormula input with
  | none =>
      have rejected : run .clause input ≠ .done := by
        intro accepted
        obtain ⟨formula, encoded⟩ := (run_clause_iff input).mp accepted
        have roundtrip := decodeFormula_encoded formula
        rw [← encoded, parsed] at roundtrip
        cases roundtrip
      simp [accepts, rejected]
  | some formula =>
      have encoded := BinaryParsing.decodeFormula_sound input formula parsed
      have accepted := (run_clause_iff input).mpr ⟨formula, encoded⟩
      simp [accepts, accepted]

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition

abbrev Alphabet (_ : Bool) := Bool
abbrev State := Mode × Option Bool

def instruction : TM2.Stmt Alphabet Unit State :=
  .pop false (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => (nextMode state.1 (state.2.getD false), none))
        (.goto fun _ => ()))
      (.push true (fun state => decide (state.1 = .done))
        (.load (fun _ => (.clause, none)) .halt)))

abbrev machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Alphabet
  Λ := Unit
  main := ()
  σ := State
  initialState := (.clause, none)
  m _ := instruction

def tapes (input output : List Bool) : Bool → List Bool
  | false => input
  | true => output

def cfg (label : Option Unit) (input output : List Bool) (mode : Mode)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input output⟩

@[simp] private theorem tapes_input (input output : List Bool) :
    tapes input output false = input := rfl

@[simp] private theorem tapes_output (input output : List Bool) :
    tapes input output true = output := rfl

private theorem update_input (input output replacement : List Bool) :
    Function.update (tapes input output) false replacement = tapes replacement output := by
  funext k
  cases k <;> rfl

private theorem update_output (input output replacement : List Bool) :
    Function.update (tapes input output) true replacement = tapes input replacement := by
  funext k
  cases k <;> rfl

theorem step_empty (mode : Mode) (output : List Bool) (register : Option Bool) :
    machine.step (cfg (some ()) [] output mode register) =
      some (cfg none [] (decide (mode = .done) :: output) .clause) := by
  change some (TM2.stepAux instruction _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input, update_output]
  rfl

theorem step_cons (mode : Mode) (bit : Bool) (input output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some ()) (bit :: input) output mode register) =
      some (cfg (some ()) input output (nextMode mode bit)) := by
  change some (TM2.stepAux instruction _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input]
  rfl

theorem runTrace (input output : List Bool) (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some ()) input output mode register)) =
      some (cfg none [] (decide (run mode input = .done) :: output) .clause) := by
  induction input generalizing mode register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run] using! step_empty mode output register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_cons]
      exact ih (nextMode mode bit) none

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some ()) input [] .clause := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] output .clause := by
  unfold haltList cfg
  congr 1
  funext k
  cases k <;> rfl

theorem validatorTrace (input : List Bool) :
    (advance machine.step)^[input.length + 1]
      (some (initList machine input)) =
      some (haltList machine [(BinaryEncoding.decodeFormula input).isSome]) := by
  rw [initList_eq, haltList_eq]
  have h := runTrace input [] .clause none
  change (advance machine.step)^[input.length + 1]
    (some (cfg (some ()) input [] .clause)) =
    some (cfg none [] [accepts input] .clause) at h
  rw [accepts_eq_decode] at h
  exact h

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input (some [(BinaryEncoding.decodeFormula input).isSome])
      (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := validatorTrace input
  steps_le_m := Nat.le_refl _

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun input => [(BinaryEncoding.decodeFormula input).isSome]) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id)
      (some ([(BinaryEncoding.decodeFormula input).isSome].map id))
      ((Polynomial.X + 1 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one] using outputsInTime input

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end BinPackingCompleteness.BinaryValidatorMachine

end OAI
