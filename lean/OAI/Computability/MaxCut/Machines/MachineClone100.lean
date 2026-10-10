import Mathlib
import OAI.Computability.MaxCut.Machines.MachineBinaryParsing
import OAI.Computability.MaxCut.Games.Clone100Counting
import OAI.Computability.MaxCut.Machines.MachineClone100Triples

namespace OAI

namespace MaxCutGames.Explicit.MachineClone100

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations.Complexity

noncomputable section

def indices (t : Outer.Clone100Triples.GoodTriple) : Nat × Nat × Nat :=
  (t.val.1.val, t.val.2.1.val, t.val.2.2.val)

def triples : List (Nat × Nat × Nat) := Outer.Clone100.triples.map indices

theorem triples_length : triples.length = 970200 := by
  simp [triples, Outer.Clone100.triples_length]

theorem triples_nonempty : triples ≠ [] := by
  apply List.length_pos_iff.mp
  rw [triples_length]
  decide

theorem equation_words {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Outer.Clone100Triples.GoodTriple) :
    SourceEncoding.equationWords (Outer.Clone100.equation e t) =
      MachineClone100Table.cloneEquationWords e (indices t) := by
  simp [SourceEncoding.equationWords, Outer.Clone100.equation,
    Outer.Clone100.nameEquiv, finProdFinEquiv,
    MachineClone100Table.cloneEquationWords, indices, Nat.mul_comm]

theorem body_words {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    (Outer.Clone100.equations es).flatMap SourceEncoding.equationWords =
      es.flatMap (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [Outer.Clone100.equations, List.flatMap_assoc, List.flatMap_map,
    equation_words, triples]

theorem input_words_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputWords (Outer.Clone100.clonedInput input) =
      [100 * input.«variables», triples.length * input.equations.length] ++
        input.equations.flatMap
          (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [SourceEncoding.inputWords, Outer.Clone100.clonedInput,
    Outer.Clone100.equations_length, body_words, triples_length]
  simp [Nat.mul_comm]

theorem input_bits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits (Outer.Clone100.clonedInput input) =
      MachineClone100Run.outputBits triples input := by
  rw [SourceEncoding.inputBits, input_words_eq, encodeWords_append]
  rfl

private theorem serialized_polynomial_inline_MachineClone100 (D N n m : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    n * 100 + m * D + 2 + m * D * (300 * n + 2) ≤
      (300 * D) * N * N + (100 + 3 * D) * N + 2 := by
  have hproduct := Nat.mul_le_mul_left (300 * D) (Nat.mul_le_mul hm hn)
  have hvariables := Nat.mul_le_mul_left 100 hn
  have hoccurrences := Nat.mul_le_mul_left (3 * D) hm
  calc
    _ = (300 * D) * (m * n) + 100 * n + (3 * D) * m + 2 := by ring
    _ ≤ (300 * D) * (N * N) + 100 * N + (3 * D) * N + 2 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hproduct hvariables) hoccurrences)
        (Nat.le_refl 2)
    _ = _ := by ring

theorem size_bound (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (Outer.Clone100.clonedInput input)).length ≤
      (300 * triples.length) * (SourceEncoding.inputBits input).length *
        (SourceEncoding.inputBits input).length +
      (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2 := by
  rw [triples_length]
  exact (Outer.Clone100.clonedInput_bits_length_le input).trans
    (serialized_polynomial_inline_MachineClone100 970200 (SourceEncoding.inputBits input).length
      input.«variables» input.equations.length
      (SourceEncoding.inputBits_length_ge_variables input)
      (SourceEncoding.inputBits_length_ge_equations input))

def computation : TM2ComputableInPolyTime SourceEncoding.inputBits
    SourceEncoding.inputBits Outer.Clone100.clonedInput :=
  MachineClone100Certified.certifiedFunction triples triples_nonempty
    Outer.Clone100.clonedInput input_bits_eq size_bound

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

def fullRunInTime (input : SourceEncoding.Input) := computation.outputsFun input

end

end MaxCutGames.Explicit.MachineClone100

/-!
A finite-state validator for the concrete ordinary-binary formula encoding.
It checks clause and literal framing, canonical name payloads, and the unique
terminal formula marker. The last-digit register starts at true for each name,
so the empty payload is accepted as zero while a nonempty payload must end in
one. Every bit following the terminal formula marker causes rejection.
-/

namespace MaxCutGames.BinaryValidatorMachine

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

private theorem finalDigit_true_iff_inline_MachineBinaryValidatorMachine (bits : List Bool) :
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

/-- A valid framed payload advances exactly to the next literal or clause. -/
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
  exact (finalDigit_true_iff_inline_MachineBinaryValidatorMachine name.bits).mpr (BinaryParsing.canonical_nat_bits name)

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

/-- Any accepting name phase consumes a complete frame with a valid last digit. -/
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
  have hcanonical := (finalDigit_true_iff_inline_MachineBinaryValidatorMachine bits).mp hvalid
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

private theorem clauses_inverse_aux_inline_MachineBinaryValidatorMachine (fuel : Nat) (input : List Bool)
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

/-- Exact language recognition, including rejection of incomplete, padded,
or trailing input. -/
theorem run_clause_iff (input : List Bool) :
    run .clause input = .done ↔ ∃ formula, input = formulaBits formula := by
  constructor
  · intro accepted
    obtain ⟨clauses, hclauses⟩ :=
      clauses_inverse_aux_inline_MachineBinaryValidatorMachine (input.length + 1) input (by omega) accepted
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

/-! ## Concrete finite-stack execution -/

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition

abbrev Alphabet (_ : Bool) := Bool
abbrev State := Mode × Option Bool

/-- Every nonempty pop performs exactly one finite DFA transition. The empty
pop emits the final acceptance bit, resets control, and halts. -/
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

@[simp] theorem tapes_input (input output : List Bool) :
    tapes input output false = input := rfl

@[simp] theorem tapes_output (input output : List Bool) :
    tapes input output true = output := rfl

private theorem update_input_inline_MachineBinaryValidatorMachine (input output replacement : List Bool) :
    Function.update (tapes input output) false replacement = tapes replacement output := by
  funext k
  cases k <;> rfl

private theorem update_output_inline_MachineBinaryValidatorMachine (input output replacement : List Bool) :
    Function.update (tapes input output) true replacement = tapes input replacement := by
  funext k
  cases k <;> rfl

theorem step_empty (mode : Mode) (output : List Bool) (register : Option Bool) :
    machine.step (cfg (some ()) [] output mode register) =
      some (cfg none [] (decide (mode = .done) :: output) .clause) := by
  change some (TM2.stepAux instruction _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryValidatorMachine, update_output_inline_MachineBinaryValidatorMachine]
  rfl

theorem step_cons (mode : Mode) (bit : Bool) (input output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some ()) (bit :: input) output mode register) =
      some (cfg (some ()) input output (nextMode mode bit)) := by
  change some (TM2.stepAux instruction _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryValidatorMachine]
  rfl

/-- Exact execution on every word, including malformed, noncanonical, and
trailing input. Rejection drains the entire input through a finite sink state. -/
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

/-- A total raw-bit validator with the exact same answer as the binary codec. -/
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

/-- The polynomial certificate supplies the explicit machine above. There is
no assumed parser, verifier, or runtime hypothesis. -/
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

end MaxCutGames.BinaryValidatorMachine

/-!
Total raw-input preprocessing for the ordinary binary formula codec. The
machine copies each input bit onto a reverse stack while running the finite
validator. Accepted words are restored verbatim; rejected words are drained
and replaced by the fixed contradictory formula. All three stack alphabets
and all control/register types are finite.
-/

namespace MaxCutGames.BinaryTotalInputMachine

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer
open MaxCutGames.Reduction.MachineSubstitution
open BinaryValidatorMachine (Mode nextMode run)

inductive Label
  | scan
  | restore
  | drain
  | rejectOutput
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .restore, .drain, .rejectOutput]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := Mode × Option Bool

def rejectedWord : List Bool := BinaryEncoding.formulaBits BinaryLanguage.rejectBinary

/-- Stack zero is the input, one the output, and two the reversed input.
Branches inspect only the finite validator state and the popped symbol. -/
def instruction : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push 2 (fun state => state.2.getD false)
            (.load (fun state => (nextMode state.1 (state.2.getD false), none))
              (.goto fun _ => .scan)))
          (.branch (fun state => decide (state.1 = .done))
            (.load (fun _ => (.clause, none)) (.goto fun _ => .restore))
            (.load (fun _ => (.clause, none)) (.goto fun _ => .drain))))
  | .restore => loopAt 2 1 id false .restore none
  | .drain => MachineDrain.drain 2 .drain (some .rejectOutput)
  | .rejectOutput => pushWord 1 rejectedWord.reverse .halt

abbrev machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (.clause, none)
  m := instruction

def tapes (input output saved : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => output
  | _ => saved

def cfg (label : Option Label) (input output saved : List Bool) (mode : Mode := .clause)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input output saved⟩

@[simp] theorem tapes_input (input output saved : List Bool) :
    tapes input output saved 0 = input := rfl

@[simp] theorem tapes_output (input output saved : List Bool) :
    tapes input output saved 1 = output := rfl

@[simp] theorem tapes_saved (input output saved : List Bool) :
    tapes input output saved 2 = saved := rfl

private theorem update_input_inline_MachineBinaryTotalInputMachine (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 0 replacement =
      tapes replacement output saved := by
  funext k
  fin_cases k <;> rfl

private theorem update_output_inline_MachineBinaryTotalInputMachine (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 1 replacement =
      tapes input replacement saved := by
  funext k
  fin_cases k <;> rfl

private theorem update_saved_inline_MachineBinaryTotalInputMachine (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 2 replacement =
      tapes input output replacement := by
  funext k
  fin_cases k <;> rfl

def afterScan (mode : Mode) : Label := if mode = .done then .restore else .drain

theorem step_scan_empty (output saved : List Bool) (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) [] output saved mode register) =
      some (cfg (some (afterScan mode)) [] output saved) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  by_cases accepted : mode = .done <;>
    simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryTotalInputMachine, afterScan, accepted] <;> rfl

theorem step_scan_cons (bit : Bool) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) (bit :: input) output saved mode register) =
      some (cfg (some .scan) input output (bit :: saved) (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryTotalInputMachine, update_saved_inline_MachineBinaryTotalInputMachine]
  rfl

/-- The finite DFA reads every bit, including all bits in its rejection sink.
The trace also records the physical reversed copy needed by the second phase. -/
theorem scanTrace (input output saved : List Bool) (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .scan) input output saved mode register)) =
      some (cfg (some (afterScan (run mode input))) [] output (input.reverse ++ saved)) := by
  induction input generalizing saved mode register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run, List.reverse_nil, List.nil_append] using
          step_scan_empty output saved mode register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_scan_cons]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (bit :: saved) (nextMode mode bit) none

theorem restoreTrace (saved output : List Bool) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .restore) [] output saved .clause register)) =
      some (cfg none [] (saved.reverse ++ output) []) := by
  change (nextAt (1 : Fin 3) instruction)^[saved.length + 1]
    (some ⟨some .restore, (Mode.clause, register), tapes [] output saved⟩) =
    some ⟨none, (Mode.clause, none), tapes [] (saved.reverse ++ output) []⟩
  have trace := transferAt_steps (2 : Fin 3) 1 (by decide) id false .restore none
    instruction rfl (tapes [] [] []) saved output Mode.clause register
  simpa only [tapesAt, update_saved_inline_MachineBinaryTotalInputMachine, update_output_inline_MachineBinaryTotalInputMachine,
    List.map_id_fun, id_eq] using trace

theorem drainTrace (saved output : List Bool) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .drain) [] output saved .clause register)) =
      some (cfg (some .rejectOutput) [] output []) := by
  change (advance (TM2.step instruction))^[saved.length + 1]
    (some ⟨some .drain, (Mode.clause, register), tapes [] output saved⟩) =
    some ⟨some .rejectOutput, (Mode.clause, none), tapes [] output []⟩
  have trace := MachineDrain.drainTrace (2 : Fin 3) .drain (some .rejectOutput)
    instruction rfl (tapes [] output []) saved Mode.clause register
  simpa only [update_saved_inline_MachineBinaryTotalInputMachine] using trace

theorem step_rejectOutput (output : List Bool) :
    machine.step (cfg (some .rejectOutput) [] output []) =
      some (cfg none [] (rejectedWord ++ output) []) := by
  change some (TM2.stepAux
    (pushWord (Γ := Alphabet) (Λ := Label) (σ := State)
      (1 : Fin 3) rejectedWord.reverse .halt) _ _) = _
  rw [stepAux_pushWord]
  simp only [cfg, List.reverse_reverse, tapes_output, update_output_inline_MachineBinaryTotalInputMachine, TM2.stepAux]
  rfl

private theorem joinTrace_inline_MachineBinaryTotalInputMachine {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem acceptedTrace (input : List Bool) (accepted : run .clause input = .done) :
    (advance machine.step)^[2 * input.length + 2]
      (some (cfg (some .scan) input [] [])) = some (cfg none [] input []) := by
  have first := scanTrace input [] [] .clause none
  simp only [afterScan, accepted, ↓reduceIte, List.append_nil] at first
  have second := restoreTrace input.reverse [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at second
  have time : 2 * input.length + 2 = (input.length + 1) + (input.length + 1) := by omega
  rw [time]
  exact joinTrace_inline_MachineBinaryTotalInputMachine first second

theorem rejectedTrace (input : List Bool) (rejected : run .clause input ≠ .done) :
    (advance machine.step)^[2 * input.length + 3]
      (some (cfg (some .scan) input [] [])) = some (cfg none [] rejectedWord []) := by
  have first := scanTrace input [] [] .clause none
  simp only [afterScan, rejected, ↓reduceIte, List.append_nil] at first
  have second := drainTrace input.reverse [] none
  simp only [List.length_reverse] at second
  have third : (advance machine.step)^[1]
      (some (cfg (some .rejectOutput) [] [] [])) = some (cfg none [] rejectedWord []) := by
    simpa only [Function.iterate_one, advance_some, List.append_nil] using
      step_rejectOutput []
  have time : 2 * input.length + 3 = (input.length + 1) + (input.length + 1) + 1 := by omega
  rw [time]
  exact joinTrace_inline_MachineBinaryTotalInputMachine (joinTrace_inline_MachineBinaryTotalInputMachine first second) third

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .scan) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] output [] := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

def steps (input : List Bool) : Nat :=
  if run .clause input = .done then 2 * input.length + 2 else 2 * input.length + 3

theorem steps_le (input : List Bool) : steps input ≤ 2 * input.length + 3 := by
  unfold steps
  split <;> omega

/-- Full correspondence on every raw word, with no validity premise. -/
theorem totalTrace (input : List Bool) :
    (advance machine.step)^[steps input] (some (initList machine input)) =
      some (haltList machine (BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input))) := by
  rw [initList_eq, haltList_eq]
  cases parsed : BinaryEncoding.decodeFormula input with
  | none =>
      have rejected : run .clause input ≠ .done := by
        intro accepted
        obtain ⟨formula, encoded⟩ := (BinaryValidatorMachine.run_clause_iff input).mp accepted
        have roundtrip := BinaryEncoding.decodeFormula_encoded formula
        rw [← encoded, parsed] at roundtrip
        cases roundtrip
      simpa only [steps, rejected, ↓reduceIte, BinaryLanguage.totalParsed, parsed,
        Option.getD_none, rejectedWord] using rejectedTrace input rejected
  | some formula =>
      have encoded := BinaryParsing.decodeFormula_sound input formula parsed
      have accepted := (BinaryValidatorMachine.run_clause_iff input).mpr ⟨formula, encoded⟩
      simp only [steps, accepted, ↓reduceIte, BinaryLanguage.totalParsed, parsed,
        Option.getD_some]
      rw [← encoded]
      exact acceptedTrace input accepted

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input
      (some (BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input)))
      (2 * input.length + 3) where
  steps := steps input
  evals_in_steps := totalTrace input
  steps_le_m := steps_le input

/-- The certificate contains the displayed total machine and its linear trace;
it assumes no execution, parser-cost, or malformed-input premise. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) BinaryEncoding.formulaBits
      BinaryLanguage.totalParsed where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id)
      (some ((BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input)).map id))
      ((2 * Polynomial.X + 3 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat] using outputsInTime input

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  machine_finiteAlphabet

end MaxCutGames.BinaryTotalInputMachine

end OAI
