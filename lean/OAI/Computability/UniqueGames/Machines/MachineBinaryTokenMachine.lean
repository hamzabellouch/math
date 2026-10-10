import Mathlib.Tactic.DeriveFintype
import OAI.Computability.UniqueGames.Machines.MachineBinaryFormulaLemmas
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

/-!
An actual finite Boolean-stack machine which removes formula/clause markers
from valid ordinary-binary 3CNF encodings. Literal signs and every bit of each
framed binary name survive in their original occurrence order. The first pass
accumulates the output in reverse; the checked transfer routine restores order.

The machine is specified on the semantic encoded-input domain. It does not
claim to reject every malformed or noncanonical input. In particular, the
name-copying loop does not check canonicality: valid input already supplies it.
All transitions inspect only finite control and one popped bit. No branch or
load computes a whole-list function or converts a binary name to unary.
-/

namespace UniqueGamesTheorem.BinaryTokenMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open BinaryFormula BinaryEncoding

abbrev Tape := Fin 3
abbrev Alphabet (_ : Tape) := Bool
abbrev State := Unit × Option Bool

inductive Label where
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3)
  | restore
  | accept
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Label :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

@[simp] theorem afterName_zero : afterName 0 = .sign 1 := rfl
@[simp] theorem afterName_one : afterName 1 = .sign 2 := rfl
@[simp] theorem afterName_two : afterName 2 = .clause := rfl

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => ((), none)) (.goto fun _ => label)

/-- Discard a clause marker, or finish at the final formula terminator. -/
def clauseInstruction : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (jump (.sign 0)) (jump .restore)))

def signInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
      (jump .reject))

/-- Copy both symbols of a payload pair, or copy the name terminator. -/
def nameInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (.push 1 (fun _ => true)
          (.pop 0 (fun state head => (state.1, head))
            (.branch (fun state => state.2.isSome)
              (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
              (jump .reject))))
        (.push 1 (fun _ => false) (jump (afterName slot)))))

def program : Label → TM2.Stmt Alphabet Label State
  | .clause => clauseInstruction
  | .sign slot => signInstruction slot
  | .name slot => nameInstruction slot
  | .restore => loopAt 1 2 id false .restore (some .accept)
  | .accept => .halt
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := Label
  main := .clause
  σ := State
  initialState := ((), none)
  m := program

def tapes (input reversed output : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then reversed else output

def cfg (label : Option Label) (input reversed output : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input reversed output⟩

@[simp] private theorem tapes_zero (input reversed output : List Bool) :
    tapes input reversed output 0 = input := rfl

@[simp] private theorem tapes_one (input reversed output : List Bool) :
    tapes input reversed output 1 = reversed := rfl

@[simp] private theorem tapes_two (input reversed output : List Bool) :
    tapes input reversed output 2 = output := rfl

private theorem update_zero (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 0 replacement =
      tapes replacement reversed output := by
  funext k
  fin_cases k <;> simp [tapes]

private theorem update_one (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 1 replacement =
      tapes input replacement output := by
  funext k
  fin_cases k <;> simp [tapes]

theorem clauseStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (true :: input) reversed output register) =
      some (cfg (some (.sign 0)) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]
  rfl

theorem finalStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (false :: input) reversed output register) =
      some (cfg (some .restore) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]
  rfl

theorem signStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.sign slot)) (bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: reversed) output) := by
  change some (TM2.stepAux (program (.sign slot)) _ _) = _
  simp [program, signInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem nameEndStep (slot : Fin 3) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.name slot)) (false :: input) reversed output register) =
      some (cfg (some (afterName slot)) input (false :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem nameDigitStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step
      (cfg (some (.name slot)) (true :: bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: true :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem nameTrace (slot : Fin 3) (bits suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[bits.length + 1]
      (some (cfg (some (.name slot)) (frame bits ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix ((frame bits).reverse ++ reversed) output) := by
  induction bits generalizing reversed register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        frame, List.singleton_append, List.reverse_singleton] using
        nameEndStep slot suffix reversed output register
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [frame, List.cons_append, advance_some]
      rw [nameDigitStep, ih]
      simp only [List.reverse_cons, List.append_assoc,
        List.cons_append, List.nil_append]

theorem literalTrace (slot : Fin 3) (literal : Literal)
    (suffix reversed output : List Bool) (register : Option Bool) :
    (advance machine.step)^[literal.name.size + 2]
      (some (cfg (some (.sign slot)) (literalBits literal ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix
        ((literalBits literal).reverse ++ reversed) output) := by
  rw [show literal.name.size + 2 = (literal.name.bits.length + 1) + 1 by
    rw [Nat.size_eq_bits_len]]
  rw [Function.iterate_succ_apply]
  simp only [literalBits, List.cons_append, advance_some]
  rw [signStep]
  change (advance machine.step)^[literal.name.bits.length + 1]
    (some (cfg (some (.name slot)) (frame literal.name.bits ++ suffix)
      (literal.positive :: reversed) output)) = _
  rw [nameTrace]
  simp only [nameBits, List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

/-- Three literal subroutines return to the next clause boundary. -/
theorem clauseTrace (clause : Clause) (suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[clauseNameSize clause + 6]
      (some (cfg (some (.sign 0)) (clauseBits clause ++ suffix) reversed output register)) =
      some (cfg (some .clause) suffix ((clauseBits clause).reverse ++ reversed) output) := by
  have first := literalTrace 0 clause[0]
    (literalBits clause[1] ++ literalBits clause[2] ++ suffix) reversed output register
  have second := literalTrace 1 clause[1] (literalBits clause[2] ++ suffix)
    ((literalBits clause[0]).reverse ++ reversed) output none
  have third := literalTrace 2 clause[2] suffix
    ((literalBits clause[1]).reverse ++ ((literalBits clause[0]).reverse ++ reversed)) output none
  simp only [afterName_zero, afterName_one, afterName_two, List.append_assoc]
    at first second third
  have full := joinTrace (joinTrace first second) third
  have htime : (clause[0].name.size + 2 + (clause[1].name.size + 2)) +
      (clause[2].name.size + 2) = clauseNameSize clause + 6 := by
    simp [clauseNameSize, clauseNames]
    omega
  rw [htime] at full
  simpa only [clauseBits, List.append_assoc, List.reverse_append] using full

def tokens (clauses : List Clause) : List Bool := clauses.flatMap clauseBits

@[simp] theorem tokens_nil : tokens [] = [] := rfl

@[simp] theorem tokens_cons (clause : Clause) (clauses : List Clause) :
    tokens (clause :: clauses) = clauseBits clause ++ tokens clauses := by
  simp [tokens]

@[simp] theorem tokens_length (clauses : List Clause) :
    (tokens clauses).length = 6 * clauses.length + 2 * namesBitSize clauses := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [tokens_cons, List.length_append, clauseBits_length, ih,
        List.length_cons, namesBitSize_cons]
      omega

/-- Exact first-pass run, retaining the unread suffix and ambient output. -/
theorem stripTrace (clauses : List Clause) (suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[7 * clauses.length + namesBitSize clauses + 1]
      (some (cfg (some .clause) (clausesBits clauses ++ suffix) reversed output register)) =
      some (cfg (some .restore) suffix ((tokens clauses).reverse ++ reversed) output) := by
  induction clauses generalizing reversed register with
  | nil =>
      simpa only [List.length_nil, Nat.mul_zero, namesBitSize_nil, Nat.add_zero,
        Nat.zero_add, Function.iterate_one, advance_some, clausesBits,
        List.singleton_append, tokens_nil, List.reverse_nil, List.nil_append] using
        finalStep suffix reversed output register
  | cons clause clauses ih =>
      have first : (advance machine.step)^[1]
          (some (cfg (some .clause)
            (true :: (clauseBits clause ++ (clausesBits clauses ++ suffix)))
            reversed output register)) =
          some (cfg (some (.sign 0))
            (clauseBits clause ++ (clausesBits clauses ++ suffix)) reversed output) := by
        simpa only [Function.iterate_one, advance_some] using
          clauseStep (clauseBits clause ++ (clausesBits clauses ++ suffix)) reversed output register
      have second := clauseTrace clause (clausesBits clauses ++ suffix) reversed output none
      have third := ih ((clauseBits clause).reverse ++ reversed) none
      have full := joinTrace (joinTrace first second) third
      have htime : (1 + (clauseNameSize clause + 6)) +
          (7 * clauses.length + namesBitSize clauses + 1) =
          7 * (clause :: clauses).length + namesBitSize (clause :: clauses) + 1 := by
        simp only [List.length_cons, namesBitSize_cons]
        omega
      rw [htime] at full
      simpa only [clausesBits, List.cons_append, List.append_assoc,
        tokens_cons, List.reverse_append] using full

theorem restoreTrace (input unread output : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .restore) unread input.reverse output register)) =
      some (cfg (some .accept) unread [] (input ++ output)) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 2 (by decide)
    id false .restore (some .accept) program rfl
    (tapes unread input.reverse output) () register
  have ht : tapesAt 1 2 (tapes unread input.reverse output) [] (input ++ output) =
      tapes unread [] (input ++ output) := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 2 program)^[input.length + 1]
    (some (cfg (some .restore) unread input.reverse output register)) = _
  simp only [tapes_one, tapes_two, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, ht] at h
  exact h

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .clause) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] [] output := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem acceptTrace (formula : Formula) :
    (advance machine.step)^[13 * formula.clauses.length +
        3 * namesBitSize formula.clauses + 2]
      (some (initList machine (formulaBits formula))) =
      some (cfg (some .accept) [] [] (tokens formula.clauses)) := by
  have first := stripTrace formula.clauses [] [] [] none
  simp only [List.append_nil] at first
  have second := restoreTrace (tokens formula.clauses) [] [] none
  simp only [List.append_nil] at second
  have full := joinTrace first second
  have htime : (7 * formula.clauses.length + namesBitSize formula.clauses + 1) +
      ((tokens formula.clauses).length + 1) =
      13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 2 := by
    rw [tokens_length]
    omega
  rw [htime] at full
  simpa only [initList_eq, BinaryEncoding.formulaBits] using full

theorem haltStep (output : List Bool) :
    machine.step (cfg (some .accept) [] [] output) = some (cfg none [] [] output) := by
  change some (TM2.stepAux (program .accept) _ _) = _
  rfl

/-- Exact transition count for the complete finite-machine computation. -/
theorem tokenTrace (formula : Formula) :
    (advance machine.step)^[13 * formula.clauses.length +
        3 * namesBitSize formula.clauses + 3]
      (some (initList machine (formulaBits formula))) =
      some (haltList machine (tokens formula.clauses)) := by
  rw [show 13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3 =
    (13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 2) + 1 by omega,
    Function.iterate_succ_apply', acceptTrace, advance_some, haltStep, haltList_eq]

theorem tokenSteps_le (formula : Formula) :
    13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3 ≤
      3 * (formulaBits formula).length + 3 := by
  rw [BinaryEncoding.formulaBits_length]
  omega

def outputsInTime (formula : Formula) :
    TM2OutputsInTime machine (formulaBits formula) (some (tokens formula.clauses))
      (3 * (formulaBits formula).length + 3) where
  steps := 13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3
  evals_in_steps := tokenTrace formula
  steps_le_m := tokenSteps_le formula

/-- A displayed finite machine and linear polynomial in the ordinary input
bit length, proved by the transitions above rather than assumed by a caller. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits (id : List Bool → List Bool)
      (fun formula => tokens formula.clauses) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
  outputsFun formula := by
    change TM2OutputsInTime machine ((formulaBits formula).map id)
      (some ((tokens formula.clauses).map id))
      ((Polynomial.C 3 * Polynomial.X + Polynomial.C 3 : Polynomial Nat).eval
        (formulaBits formula).length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using outputsInTime formula

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.BinaryTokenMachine

end OAI
