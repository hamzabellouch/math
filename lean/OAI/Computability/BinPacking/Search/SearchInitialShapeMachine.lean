import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Arithmetic.GraphTallyMachine

namespace OAI

namespace BinPackingGap.SearchInitialShapeMachine

open BinaryEncoding
open BinPackingCompleteness.BinaryNameMachine (finalDigit canonical)

inductive Continuation
  | numerator
  | denominator
  deriving DecidableEq

protected abbrev Continuation.enumList : List Continuation := [.numerator, .denominator]

protected theorem Continuation.enumList_getElem?_ctorIdx_eq (x : Continuation) :
    Continuation.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Continuation.enumList_nodup : Continuation.enumList.Nodup := by decide

instance : Fintype Continuation where
  elems := ⟨Continuation.enumList, Continuation.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Mode
  | name (next : Continuation) (last : Bool)
  | digit (next : Continuation)
  | items
  | done
  | reject
  deriving DecidableEq, Fintype

def afterName : Continuation → Mode
  | .numerator => .name .denominator true
  | .denominator => .items

def nextMode : Mode → Bool → Mode
  | .name next _, true => .digit next
  | .name next last, false => if last then afterName next else .reject
  | .digit next, bit => .name next bit
  | .items, true => .name .numerator true
  | .items, false => .done
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
    finalDigit bits (some true) = some true ↔ canonical bits = true := by
  cases bits with
  | nil => simp [finalDigit, canonical]
  | cons bit bits =>
      simp only [finalDigit, canonical]
      have hsome : ∀ (ds : List Bool) (b : Bool),
          ∃ last, finalDigit ds (some b) = some last := by
        intro ds
        induction ds with
        | nil => intro b; exact ⟨b, rfl⟩
        | cons d ds ih => intro b; exact ih d
      obtain ⟨last, hlast⟩ := hsome bits bit
      rw [hlast]
      simp

theorem run_frame (next : Continuation) (bits rest : List Bool) (last : Bool)
    (valid : finalDigit bits (some last) = some true) :
    run (.name next last) (BinPackingCompleteness.BinaryEncoding.frame bits ++ rest) =
      run (afterName next) rest := by
  induction bits generalizing last with
  | nil =>
      have hlast : last = true := by simpa [finalDigit] using valid
      subst last
      simp [BinPackingCompleteness.BinaryEncoding.frame, run, nextMode]
  | cons bit bits ih =>
      have hvalid : finalDigit bits (some bit) = some true := valid
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append, run, nextMode]
        using ih bit hvalid

theorem run_name (next : Continuation) (name : Nat) (rest : List Bool) :
    run (.name next true) (natBits name ++ rest) = run (afterName next) rest := by
  apply run_frame
  exact (finalDigit_true_iff name.bits).mpr
    (BinPackingCompleteness.BinaryParsing.canonical_nat_bits name)

theorem run_items (items : RawInstance) (rest : List Bool) :
    run .items (rawInstanceBits items ++ rest) = run .done rest := by
  induction items with
  | nil => simp [rawInstanceBits, listBits, run, nextMode]
  | cons q items ih =>
      simp only [rawInstanceBits, listBits, List.cons_append, run, nextMode,
        pairBits, List.append_assoc, run_name, afterName]
      exact ih

theorem run_rawInstanceBits (items : RawInstance) :
    run .items (rawInstanceBits items) = .done := by
  simpa only [List.append_nil, run] using run_items items []

theorem frame_inverse (next : Continuation) (last : Bool) (input : List Bool)
    (accepted : run (.name next last) input = .done) :
    ∃ bits rest, input = BinPackingCompleteness.BinaryEncoding.frame bits ++ rest ∧
      finalDigit bits (some last) = some true ∧
      run (afterName next) rest = .done := by
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
          have haccepted : run (.name next bit) input = .done := by
            simpa only [run, nextMode] using accepted
          obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := ih bit haccepted
          refine ⟨bit :: bits, rest, ?_, hvalid, hrest⟩
          simp [BinPackingCompleteness.BinaryEncoding.frame, hinput]

theorem name_inverse (next : Continuation) (input : List Bool)
    (accepted : run (.name next true) input = .done) :
    ∃ name rest, input = natBits name ++ rest ∧ run (afterName next) rest = .done := by
  obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := frame_inverse next true input accepted
  have hcanonical := (finalDigit_true_iff bits).mp hvalid
  have hbits := (BinPackingCompleteness.BinaryParsing.canonical_iff bits).mp hcanonical
  refine ⟨BinPackingCompleteness.BinaryEncoding.bitsValue bits, rest, ?_, hrest⟩
  simpa only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits, hbits] using hinput

private theorem items_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .items input = .done) :
    ∃ items, input = rawInstanceBits items := by
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
              have haccepted : run (.name .numerator true) input = .done := accepted
              obtain ⟨num, afterNum, hnum, hafterNum⟩ :=
                name_inverse .numerator input haccepted
              obtain ⟨den, rest, hden, hrest⟩ :=
                name_inverse .denominator afterNum hafterNum
              have hlength := congrArg List.length hnum
              have hlength' := congrArg List.length hden
              simp only [List.length_append] at hlength hlength'
              have henough : rest.length < fuel := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨items, htail⟩ := ih rest henough hrest
              refine ⟨(num, den) :: items, ?_⟩
              simp [rawInstanceBits, listBits, pairBits, hnum, hden, htail, List.append_assoc]

theorem run_items_iff (input : List Bool) :
    run .items input = .done ↔ ∃ items, input = rawInstanceBits items := by
  constructor
  · intro accepted
    exact items_inverse_aux (input.length + 1) input (by omega) accepted
  · rintro ⟨items, rfl⟩
    exact run_rawInstanceBits items

def accepts (input : List Bool) : Bool := decide (run .items input = .done)

def decodeAccepts (input : List Bool) : Bool := (decodeRawInstance input).isSome

theorem accepts_eq_decode (input : List Bool) :
    accepts input = (decodeRawInstance input).isSome := by
  cases parsed : decodeRawInstance input with
  | none =>
      have rejected : run .items input ≠ .done := by
        intro accepted
        obtain ⟨items, encoded⟩ := (run_items_iff input).mp accepted
        have roundtrip := decodeRawInstance_rawInstanceBits items
        rw [← encoded, parsed] at roundtrip
        cases roundtrip
      simp [accepts, rejected]
  | some items =>
      have encoded := decodeRawInstance_sound parsed
      have accepted := (run_items_iff input).mpr ⟨items, encoded⟩
      simp [accepts, accepted]

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution

inductive Label
  | scan
  | restore
  | finish
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .restore, .finish]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := Mode × Option Bool

def instruction : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push 2 (fun state => state.2.getD false)
            (.load (fun state => (nextMode state.1 (state.2.getD false), none))
              (.goto fun _ => .scan)))
          (.load (fun state => (state.1, none)) (.goto fun _ => .restore)))
  | .restore => loopAt 2 1 id false .restore (some .finish)
  | .finish =>
      .push 1 (fun state => decide (state.1 = .done))
        (.load (fun _ => (Mode.items, none)) .halt)

abbrev machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (Mode.items, none)
  m := instruction

def tapes (input output saved : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => output
  | _ => saved

def cfg (label : Option Label) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input output saved⟩

@[simp] private theorem tapes_input (input output saved : List Bool) :
    tapes input output saved 0 = input := rfl

@[simp] private theorem tapes_output (input output saved : List Bool) :
    tapes input output saved 1 = output := rfl

@[simp] private theorem tapes_saved (input output saved : List Bool) :
    tapes input output saved 2 = saved := rfl

private theorem update_input (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 0 replacement =
      tapes replacement output saved := by
  funext k
  fin_cases k <;> rfl

private theorem update_output (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 1 replacement =
      tapes input replacement saved := by
  funext k
  fin_cases k <;> rfl

private theorem update_saved (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 2 replacement =
      tapes input output replacement := by
  funext k
  fin_cases k <;> rfl

theorem step_scan_empty (output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) [] output saved mode register) =
      some (cfg (some .restore) [] output saved mode) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input]
  all_goals rfl

theorem step_scan_cons (bit : Bool) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) (bit :: input) output saved mode register) =
      some (cfg (some .scan) input output (bit :: saved) (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input, update_saved]
  all_goals rfl

theorem scanTrace (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .scan) input output saved mode register)) =
      some (cfg (some .restore) [] output (input.reverse ++ saved) (run mode input)) := by
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

theorem restoreTrace (saved output : List Bool)
    (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .restore) [] output saved mode register)) =
      some (cfg (some .finish) [] (saved.reverse ++ output) [] mode) := by
  change (nextAt (1 : Fin 3) instruction)^[saved.length + 1]
    (some ⟨some .restore, (mode, register), tapes [] output saved⟩) =
    some ⟨some .finish, (mode, none), tapes [] (saved.reverse ++ output) []⟩
  have trace := transferAt_steps (2 : Fin 3) 1 (by decide) id false .restore (some .finish)
    instruction rfl (tapes [] [] []) saved output mode register
  simpa only [tapesAt, update_saved, update_output, List.map_id_fun, id_eq] using trace

theorem step_finish (output : List Bool) (mode : Mode)
    (register : Option Bool) :
    machine.step (cfg (some .finish) [] output [] mode register) =
      some (cfg none [] (decide (mode = .done) :: output) [] Mode.items) := by
  change some (TM2.stepAux (instruction .finish) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_output]
  all_goals rfl

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem rawTrace (input : List Bool) :
    (advance machine.step)^[2 * input.length + 3]
      (some (cfg (some .scan) input [] [] Mode.items)) =
      some (cfg none [] (accepts input :: input) [] Mode.items) := by
  have first := scanTrace input [] [] Mode.items none
  simp only [List.append_nil] at first
  have second := restoreTrace input.reverse [] (run Mode.items input) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at second
  have third : (advance machine.step)^[1]
      (some (cfg (some .finish) [] input [] (run Mode.items input))) =
      some (cfg none [] (accepts input :: input) [] Mode.items) := by
    simpa only [Function.iterate_one, advance_some, accepts] using
      step_finish input (run Mode.items input) none
  have time : 2 * input.length + 3 = (input.length + 1) + (input.length + 1) + 1 := by omega
  rw [time]
  exact joinTrace (joinTrace first second) third

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .scan) input [] [] Mode.items := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] output [] Mode.items := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem totalTrace (input : List Bool) :
    (advance machine.step)^[2 * input.length + 3]
      (some (initList machine input)) =
      some (haltList machine (decodeAccepts input :: input)) := by
  rw [initList_eq, haltList_eq]
  simpa only [accepts_eq_decode, decodeAccepts] using rawTrace input

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input (some (decodeAccepts input :: input))
      (2 * input.length + 3) where
  steps := 2 * input.length + 3
  evals_in_steps := totalTrace input
  steps_le_m := Nat.le_refl _

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun input => decodeAccepts input :: input) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id)
      (some ((decodeAccepts input :: input).map id))
      ((2 * Polynomial.X + 3 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat] using outputsInTime input

theorem machine_finiteAlphabet (k : machine.K) :
    Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  machine_finiteAlphabet

end BinPackingGap.SearchInitialShapeMachine

end OAI
