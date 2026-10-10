import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Arithmetic.GraphTallyMachine

namespace OAI

namespace BinPackingGap.ExtensionShapeMachine

open BinaryEncoding
open BinPackingCompleteness.BinaryNameMachine (finalDigit canonical)

inductive Kind
  | extension
  | assignments
  deriving DecidableEq

protected abbrev Kind.enumList : List Kind := [.extension, .assignments]

protected theorem Kind.enumList_getElem?_ctorIdx_eq (x : Kind) :
    Kind.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Kind.enumList_nodup : Kind.enumList.Nodup := by decide

instance : Fintype Kind where
  elems := ⟨Kind.enumList, Kind.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Continuation
  | bins
  | numerator
  | denominator
  | fixed
  | assignment
  deriving DecidableEq

protected abbrev Continuation.enumList : List Continuation := [.bins, .numerator, .denominator,
  .fixed, .assignment]

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
  | fixedList
  | fixedOption
  | assignments
  | done
  | reject
  deriving DecidableEq, Fintype

def start : Kind → Mode
  | .extension => .name .bins true
  | .assignments => .assignments

def afterName : Continuation → Mode
  | .bins => .items
  | .numerator => .name .denominator true
  | .denominator => .items
  | .fixed => .fixedList
  | .assignment => .assignments

def nextMode : Mode → Bool → Mode
  | .name next _, true => .digit next
  | .name next last, false => if last then afterName next else .reject
  | .digit next, bit => .name next bit
  | .items, true => .name .numerator true
  | .items, false => .fixedList
  | .fixedList, true => .fixedOption
  | .fixedList, false => .done
  | .fixedOption, true => .name .fixed true
  | .fixedOption, false => .fixedList
  | .assignments, true => .name .assignment true
  | .assignments, false => .done
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

theorem run_items (r : RawInstance) (rest : List Bool) :
    run .items (rawInstanceBits r ++ rest) = run .fixedList rest := by
  induction r with
  | nil => simp [rawInstanceBits, listBits, run, nextMode]
  | cons q r ih =>
      simp only [rawInstanceBits, listBits, List.cons_append, run, nextMode,
        pairBits, List.append_assoc, run_name, afterName]
      exact ih

theorem run_fixed (fixed : List (Option Nat)) (rest : List Bool) :
    run .fixedList (listBits (optionBits natBits) fixed ++ rest) = run .done rest := by
  induction fixed with
  | nil => simp [listBits, run, nextMode]
  | cons value fixed ih =>
      cases value with
      | none => simpa only [listBits, optionBits, List.cons_append, List.singleton_append,
          List.nil_append, run, nextMode] using ih
      | some n =>
          simpa only [listBits, optionBits, List.cons_append, List.append_assoc,
            run, nextMode, run_name, afterName] using ih

theorem run_assignments (a : List Nat) (rest : List Bool) :
    run .assignments (assignmentBits a ++ rest) = run .done rest := by
  induction a with
  | nil => simp [assignmentBits, listBits, run, nextMode]
  | cons n a ih =>
      simpa only [assignmentBits, listBits, List.cons_append, List.append_assoc,
        run, nextMode, run_name, afterName] using ih

theorem run_extension (bins : Nat) (r : RawInstance) (fixed : List (Option Nat)) :
    run (start .extension) (extensionBits bins r fixed) = .done := by
  simp only [start, extensionBits, List.append_assoc, run_name, afterName,
    run_items]
  simpa only [List.append_nil, run] using run_fixed fixed []

theorem run_assignmentBits (a : List Nat) :
    run (start .assignments) (assignmentBits a) = .done := by
  simpa only [start, List.append_nil, run] using run_assignments a []

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

private theorem fixed_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .fixedList input = .done) :
    ∃ fixed, input = listBits (optionBits natBits) fixed := by
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
              cases input with
              | nil => simp [run, nextMode] at accepted
              | cons present input =>
                  cases present with
                  | false =>
                      have haccepted : run .fixedList input = .done := accepted
                      have henough : input.length < fuel := by
                        simp only [List.length_cons] at enough
                        omega
                      obtain ⟨fixed, hfixed⟩ := ih input henough haccepted
                      exact ⟨none :: fixed, by simp [listBits, optionBits, hfixed]⟩
                  | true =>
                      have haccepted : run (.name .fixed true) input = .done := accepted
                      obtain ⟨n, rest, hinput, hrest⟩ := name_inverse .fixed input haccepted
                      have hlength := congrArg List.length hinput
                      simp only [List.length_append] at hlength
                      have henough : rest.length < fuel := by
                        simp only [List.length_cons] at enough
                        omega
                      obtain ⟨fixed, hfixed⟩ := ih rest henough hrest
                      exact ⟨some n :: fixed, by
                        simp [listBits, optionBits, hinput, hfixed]⟩

private theorem assignments_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .assignments input = .done) :
    ∃ a, input = assignmentBits a := by
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
              have haccepted : run (.name .assignment true) input = .done := accepted
              obtain ⟨n, rest, hinput, hrest⟩ := name_inverse .assignment input haccepted
              have hlength := congrArg List.length hinput
              simp only [List.length_append] at hlength
              have henough : rest.length < fuel := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨a, ha⟩ := ih rest henough hrest
              exact ⟨n :: a, by simp [assignmentBits, listBits, hinput, ha]⟩

private theorem items_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .items input = .done) :
    ∃ r fixed, input = rawInstanceBits r ++ listBits (optionBits natBits) fixed := by
  induction fuel generalizing input with
  | zero => omega
  | succ fuel ih =>
      cases input with
      | nil => simp [run] at accepted
      | cons flag input =>
          cases flag with
          | false =>
              have haccepted : run .fixedList input = .done := accepted
              obtain ⟨fixed, hfixed⟩ :=
                fixed_inverse_aux (input.length + 1) input (by omega) haccepted
              exact ⟨[], fixed, by simp [rawInstanceBits, listBits, hfixed]⟩
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
              obtain ⟨r, fixed, htail⟩ := ih rest henough hrest
              refine ⟨(num, den) :: r, fixed, ?_⟩
              simp [rawInstanceBits, listBits, pairBits, hnum, hden, htail, List.append_assoc]

theorem run_extension_iff (input : List Bool) :
    run (start .extension) input = .done ↔
      ∃ bins r fixed, input = extensionBits bins r fixed := by
  constructor
  · intro accepted
    obtain ⟨bins, rest, hinput, hrest⟩ := name_inverse .bins input accepted
    obtain ⟨r, fixed, htail⟩ := items_inverse_aux (rest.length + 1) rest (by omega) hrest
    exact ⟨bins, r, fixed, by simp [extensionBits, hinput, htail, List.append_assoc]⟩
  · rintro ⟨bins, r, fixed, rfl⟩
    exact run_extension bins r fixed

theorem run_assignments_iff (input : List Bool) :
    run (start .assignments) input = .done ↔ ∃ a, input = assignmentBits a := by
  constructor
  · intro accepted
    exact assignments_inverse_aux (input.length + 1) input (by omega) accepted
  · rintro ⟨a, rfl⟩
    exact run_assignmentBits a

def accepts (kind : Kind) (input : List Bool) : Bool :=
  decide (run (start kind) input = .done)

def decodeAccepts : Kind → List Bool → Bool
  | .extension, input => (decodeExtension input).isSome
  | .assignments, input => (decodeAssignments input).isSome

theorem accepts_eq_decode (kind : Kind) (input : List Bool) :
    accepts kind input = decodeAccepts kind input := by
  cases kind with
  | extension =>
      cases parsed : decodeExtension input with
      | none =>
          have rejected : run (start .extension) input ≠ .done := by
            intro accepted
            obtain ⟨bins, r, fixed, encoded⟩ := (run_extension_iff input).mp accepted
            have roundtrip := decodeExtension_extensionBits bins r fixed
            rw [← encoded, parsed] at roundtrip
            cases roundtrip
          simp [accepts, decodeAccepts, parsed, rejected]
      | some value =>
          rcases value with ⟨bins, r, fixed⟩
          have encoded := decodeExtension_sound parsed
          have accepted := (run_extension_iff input).mpr ⟨bins, r, fixed, encoded⟩
          simp [accepts, decodeAccepts, parsed, accepted]
  | assignments =>
      cases parsed : decodeAssignments input with
      | none =>
          have rejected : run (start .assignments) input ≠ .done := by
            intro accepted
            obtain ⟨a, encoded⟩ := (run_assignments_iff input).mp accepted
            have roundtrip := decodeAssignments_assignmentBits a
            rw [← encoded, parsed] at roundtrip
            cases roundtrip
          simp [accepts, decodeAccepts, parsed, rejected]
      | some a =>
          have encoded := decodeAssignments_sound parsed
          have accepted := (run_assignments_iff input).mpr ⟨a, encoded⟩
          simp [accepts, decodeAccepts, parsed, accepted]

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

def instruction (kind : Kind) : Label → TM2.Stmt Alphabet Label State
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
        (.load (fun _ => (start kind, none)) .halt)

abbrev machine (kind : Kind) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (start kind, none)
  m := instruction kind

def tapes (input output saved : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => output
  | _ => saved

def cfg (kind : Kind) (label : Option Label) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool := none) : (machine kind).Cfg :=
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

theorem step_scan_empty (kind : Kind) (output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    (machine kind).step (cfg kind (some .scan) [] output saved mode register) =
      some (cfg kind (some .restore) [] output saved mode) := by
  change some (TM2.stepAux (instruction kind .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input]
  all_goals rfl

theorem step_scan_cons (kind : Kind) (bit : Bool) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    (machine kind).step (cfg kind (some .scan) (bit :: input) output saved mode register) =
      some (cfg kind (some .scan) input output (bit :: saved) (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction kind .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input, update_saved]
  all_goals rfl

theorem scanTrace (kind : Kind) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    (advance (machine kind).step)^[input.length + 1]
      (some (cfg kind (some .scan) input output saved mode register)) =
      some (cfg kind (some .restore) [] output (input.reverse ++ saved) (run mode input)) := by
  induction input generalizing saved mode register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run, List.reverse_nil, List.nil_append] using
          step_scan_empty kind output saved mode register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_scan_cons]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (bit :: saved) (nextMode mode bit) none

theorem restoreTrace (kind : Kind) (saved output : List Bool)
    (mode : Mode) (register : Option Bool) :
    (advance (machine kind).step)^[saved.length + 1]
      (some (cfg kind (some .restore) [] output saved mode register)) =
      some (cfg kind (some .finish) [] (saved.reverse ++ output) [] mode) := by
  change (nextAt (1 : Fin 3) (instruction kind))^[saved.length + 1]
    (some ⟨some .restore, (mode, register), tapes [] output saved⟩) =
    some ⟨some .finish, (mode, none), tapes [] (saved.reverse ++ output) []⟩
  have trace := transferAt_steps (2 : Fin 3) 1 (by decide) id false .restore (some .finish)
    (instruction kind) rfl (tapes [] [] []) saved output mode register
  simpa only [tapesAt, update_saved, update_output, List.map_id_fun, id_eq] using trace

theorem step_finish (kind : Kind) (output : List Bool) (mode : Mode)
    (register : Option Bool) :
    (machine kind).step (cfg kind (some .finish) [] output [] mode register) =
      some (cfg kind none [] (decide (mode = .done) :: output) [] (start kind)) := by
  change some (TM2.stepAux (instruction kind .finish) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_output]
  all_goals rfl

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem rawTrace (kind : Kind) (input : List Bool) :
    (advance (machine kind).step)^[2 * input.length + 3]
      (some (cfg kind (some .scan) input [] [] (start kind))) =
      some (cfg kind none [] (accepts kind input :: input) [] (start kind)) := by
  have first := scanTrace kind input [] [] (start kind) none
  simp only [List.append_nil] at first
  have second := restoreTrace kind input.reverse [] (run (start kind) input) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at second
  have third : (advance (machine kind).step)^[1]
      (some (cfg kind (some .finish) [] input [] (run (start kind) input))) =
      some (cfg kind none [] (accepts kind input :: input) [] (start kind)) := by
    simpa only [Function.iterate_one, advance_some, accepts] using
      step_finish kind input (run (start kind) input) none
  have time : 2 * input.length + 3 = (input.length + 1) + (input.length + 1) + 1 := by omega
  rw [time]
  exact joinTrace (joinTrace first second) third

theorem initList_eq (kind : Kind) (input : List Bool) :
    initList (machine kind) input = cfg kind (some .scan) input [] [] (start kind) := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltList_eq (kind : Kind) (output : List Bool) :
    haltList (machine kind) output = cfg kind none [] output [] (start kind) := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem totalTrace (kind : Kind) (input : List Bool) :
    (advance (machine kind).step)^[2 * input.length + 3]
      (some (initList (machine kind) input)) =
      some (haltList (machine kind) (decodeAccepts kind input :: input)) := by
  rw [initList_eq, haltList_eq]
  simpa only [accepts_eq_decode] using rawTrace kind input

def outputsInTime (kind : Kind) (input : List Bool) :
    TM2OutputsInTime (machine kind) input (some (decodeAccepts kind input :: input))
      (2 * input.length + 3) where
  steps := 2 * input.length + 3
  evals_in_steps := totalTrace kind input
  steps_le_m := Nat.le_refl _

noncomputable def computableInPolyTime (kind : Kind) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun input => decodeAccepts kind input :: input) where
  tm := machine kind
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    change TM2OutputsInTime (machine kind) (input.map id)
      (some ((decodeAccepts kind input :: input).map id))
      ((2 * Polynomial.X + 3 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat] using outputsInTime kind input

theorem machine_finiteAlphabet (kind : Kind) (k : (machine kind).K) :
    Finite ((machine kind).Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet (kind : Kind) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime kind).tm :=
  machine_finiteAlphabet kind

end BinPackingGap.ExtensionShapeMachine

end OAI
