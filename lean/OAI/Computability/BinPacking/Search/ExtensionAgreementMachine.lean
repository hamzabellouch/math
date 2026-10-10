import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Search.SearchInitializeEncoding

namespace OAI

namespace BinPackingGap.ExtensionAgreementMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

inductive Label
  | entry | option | skipFlag | skipDigit | compareFlag | compareDigit | checkEnd
  | drainFixed | drainAssignments | accept | reject
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.entry, .option, .skipFlag, .skipDigit,
  .compareFlag, .compareDigit, .checkEnd, .drainFixed, .drainAssignments, .accept, .reject]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Fin 2) := Bool
abbrev State := Option Bool × Option Bool

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => (none, none)) (.goto fun _ => label)

def readBoth (zero one : Label) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (head, state.2))
    (.pop 1 (fun state head => (state.1, head))
      (.branch (fun state => state.1.isSome && state.2.isSome)
        (.branch (fun state => decide (state.1 = state.2))
          (.branch (fun state => state.1.getD false) (jump one) (jump zero))
          (jump .drainFixed))
        (jump .drainFixed)))

def program : Label → TM2.Stmt Alphabet Label State
  | .entry => readBoth .checkEnd .option
  | .option => .pop 0 (fun state head => (head, state.2))
      (.branch (fun state => state.1.isSome)
        (.branch (fun state => state.1.getD false)
          (jump .compareFlag) (jump .skipFlag))
        (jump .drainFixed))
  | .skipFlag => .pop 1 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.branch (fun state => state.2.getD false)
          (jump .skipDigit) (jump .entry))
        (jump .drainFixed))
  | .skipDigit => .pop 1 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome) (jump .skipFlag) (jump .drainFixed))
  | .compareFlag => readBoth .entry .compareDigit
  | .compareDigit => readBoth .compareFlag .compareFlag
  | .checkEnd => .pop 0 (fun state head => (head, state.2))
      (.pop 1 (fun state head => (state.1, head))
        (.branch (fun state => state.1.isNone && state.2.isNone)
          (jump .accept) (jump .drainFixed)))
  | .drainFixed => .pop 0 (fun state head => (head, state.2))
      (.branch (fun state => state.1.isSome)
        (jump .drainFixed) (jump .drainAssignments))
  | .drainAssignments => .pop 1 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (jump .drainAssignments) (jump .reject))
  | .accept => .push 0 (fun _ => true) .halt
  | .reject => .push 0 (fun _ => false) .halt

abbrev machine : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := .entry
  σ := State
  initialState := (none, none)
  m := program

def tapes (fixed assignments : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then fixed else assignments

def cfg (label : Label) (fixed assignments : List Bool) : machine.Cfg :=
  ⟨some label, (none, none), tapes fixed assignments⟩

private theorem update_fixed (fixed assignments replacement : List Bool) :
    Function.update (tapes fixed assignments) 0 replacement = tapes replacement assignments := by
  funext k; fin_cases k <;> simp [tapes]

private theorem update_assignments (fixed assignments replacement : List Bool) :
    Function.update (tapes fixed assignments) 1 replacement = tapes fixed replacement := by
  funext k; fin_cases k <;> simp [tapes]

structure View where
  label : Label
  fixed : List Bool
  assignments : List Bool

def View.cfg (view : View) : machine.Cfg :=
  BinPackingGap.ExtensionAgreementMachine.cfg view.label view.fixed view.assignments

def bothView (zero one : Label) (fixed assignments : List Bool) : View :=
  if fixed.head?.isSome && assignments.head?.isSome then
    if fixed.head? = assignments.head? then
      ⟨if fixed.head?.getD false then one else zero, fixed.tail, assignments.tail⟩
    else ⟨.drainFixed, fixed.tail, assignments.tail⟩
  else ⟨.drainFixed, fixed.tail, assignments.tail⟩

def next (view : View) : View :=
  match view.label with
  | .entry => bothView .checkEnd .option view.fixed view.assignments
  | .option =>
      if view.fixed.head?.isSome then
        ⟨if view.fixed.head?.getD false then .compareFlag else .skipFlag,
          view.fixed.tail, view.assignments⟩
      else ⟨.drainFixed, view.fixed.tail, view.assignments⟩
  | .skipFlag =>
      if view.assignments.head?.isSome then
        ⟨if view.assignments.head?.getD false then .skipDigit else .entry,
          view.fixed, view.assignments.tail⟩
      else ⟨.drainFixed, view.fixed, view.assignments.tail⟩
  | .skipDigit =>
      ⟨if view.assignments.head?.isSome then .skipFlag else .drainFixed,
        view.fixed, view.assignments.tail⟩
  | .compareFlag => bothView .entry .compareDigit view.fixed view.assignments
  | .compareDigit => bothView .compareFlag .compareFlag view.fixed view.assignments
  | .checkEnd =>
      ⟨if view.fixed.head?.isNone && view.assignments.head?.isNone then
          .accept else .drainFixed, view.fixed.tail, view.assignments.tail⟩
  | .drainFixed =>
      ⟨if view.fixed.head?.isSome then .drainFixed else .drainAssignments,
        view.fixed.tail, view.assignments⟩
  | .drainAssignments =>
      ⟨if view.assignments.head?.isSome then .drainAssignments else .reject,
        view.fixed, view.assignments.tail⟩
  | .accept | .reject => view

def Terminal (label : Label) : Prop := label = .accept ∨ label = .reject

instance (label : Label) : Decidable (Terminal label) := inferInstanceAs
  (Decidable (label = .accept ∨ label = .reject))

def rank : Label → Nat
  | .accept | .reject => 0
  | .drainAssignments => 1
  | .drainFixed => 2
  | _ => 3

def potential (view : View) : Nat :=
  view.fixed.length + view.assignments.length + rank view.label

theorem next_decreases (view : View) (active : ¬ Terminal view.label) :
    potential (next view) < potential view := by
  rcases view with ⟨label, fixed, assignments⟩
  cases label <;> cases fixed <;> cases assignments <;>
    simp_all [Terminal, next, bothView, potential, rank] <;>
    (try split_ifs) <;> (try simp_all) <;> omega

theorem step_view (view : View) (active : ¬ Terminal view.label) :
    machine.step view.cfg = some (next view).cfg := by
  rcases view with ⟨label, fixed, assignments⟩
  change (some (TM2.stepAux (program label) (none, none) (tapes fixed assignments)) :
    Option (TM2.Cfg Alphabet Label State)) =
    some ⟨some (next ⟨label, fixed, assignments⟩).label, (none, none),
      tapes (next ⟨label, fixed, assignments⟩).fixed
        (next ⟨label, fixed, assignments⟩).assignments⟩
  cases label <;> cases fixed <;> cases assignments <;>
    simp_all [Terminal, program, readBoth, jump,
      TM2.stepAux, next, bothView, update_fixed, update_assignments,
      tapes, Bool.cond_eq_ite] <;>
    (try split_ifs) <;> simp_all

def run (view : View) : View :=
  if _stopped : Terminal view.label then view else run (next view)
termination_by potential view
decreasing_by exact next_decreases view _stopped

theorem run_step (view : View) (active : ¬ Terminal view.label) :
    run view = run (next view) := by
  rw [run, dite_eq_right active]

theorem run_terminal (view : View) (stopped : Terminal view.label) : run view = view := by
  rw [run, dite_eq_left stopped]

theorem runTrace (view : View) :
    ∃ steps, steps ≤ potential view ∧
      (advance machine.step)^[steps] (some view.cfg) = some (run view).cfg := by
  induction view using (measure potential).wf.induction with
  | h view ih =>
      by_cases stopped : Terminal view.label
      · refine ⟨0, Nat.zero_le _, ?_⟩
        simp only [Function.iterate_zero, id_eq, run_terminal view stopped]
      · have smaller := next_decreases view stopped
        obtain ⟨steps, bounded, trace⟩ := ih (next view) smaller
        refine ⟨steps + 1, by omega, ?_⟩
        rw [Function.iterate_succ_apply]
        simp only [advance_some, step_view view stopped]
        rw [trace, run_step view stopped]

theorem run_isTerminal (view : View) : Terminal (run view).label := by
  induction view using (measure potential).wf.induction with
  | h view ih =>
      by_cases stopped : Terminal view.label
      · rw [run_terminal view stopped]
        exact stopped
      · rw [run_step view stopped]
        exact ih (next view) (next_decreases view stopped)

def resultView (accepted : Bool) : View :=
  ⟨if accepted then .accept else .reject, [], []⟩

theorem run_drainAssignments (assignments : List Bool) :
    run ⟨.drainAssignments, [], assignments⟩ = resultView false := by
  induction assignments with
  | nil =>
      rw [run_step _ (by simp [Terminal])]
      exact run_terminal _ (Or.inr rfl)
  | cons bit assignments ih =>
      rw [run_step _ (by simp [Terminal])]
      exact ih

theorem run_drainFixed (fixed assignments : List Bool) :
    run ⟨.drainFixed, fixed, assignments⟩ = resultView false := by
  induction fixed with
  | nil =>
      rw [run_step _ (by simp [Terminal])]
      exact run_drainAssignments assignments
  | cons bit fixed ih =>
      rw [run_step _ (by simp [Terminal])]
      exact ih

theorem run_checkEnd_empty : run ⟨.checkEnd, [], []⟩ = resultView true := by
  rw [run_step _ (by simp [Terminal])]
  exact run_terminal _ (Or.inl rfl)

theorem run_skipFrame (bits fixed suffix : List Bool) :
    run ⟨.skipFlag, fixed, BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix⟩ =
      run ⟨.entry, fixed, suffix⟩ := by
  induction bits with
  | nil =>
      rw [run_step _ (by simp [Terminal])]
      rfl
  | cons bit bits ih =>
      rw [run_step _ (by simp [Terminal])]
      change run ⟨.skipDigit, fixed,
        bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix)⟩ = _
      rw [run_step _ (by simp [Terminal])]
      exact ih

theorem run_compareFrame (left right fixedSuffix assignmentSuffix : List Bool) :
    run ⟨.compareFlag,
        BinPackingCompleteness.BinaryEncoding.frame left ++ fixedSuffix,
        BinPackingCompleteness.BinaryEncoding.frame right ++ assignmentSuffix⟩ =
      if left = right then run ⟨.entry, fixedSuffix, assignmentSuffix⟩
        else resultView false := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, BinPackingCompleteness.BinaryEncoding.frame]
      | cons bit right =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, BinPackingCompleteness.BinaryEncoding.frame, run_drainFixed]
  | cons bit left ih =>
      cases right with
      | nil =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, BinPackingCompleteness.BinaryEncoding.frame, run_drainFixed]
      | cons digit right =>
          rw [run_step _ (by simp [Terminal])]
          change run ⟨.compareDigit,
            bit :: (BinPackingCompleteness.BinaryEncoding.frame left ++ fixedSuffix),
            digit :: (BinPackingCompleteness.BinaryEncoding.frame right ++ assignmentSuffix)⟩ = _
          rw [run_step _ (by simp [Terminal])]
          by_cases equal : bit = digit
          · subst digit
            cases bit <;> simpa [next, bothView, BinPackingCompleteness.BinaryEncoding.frame] using ih right
          · simp [next, bothView, equal, run_drainFixed]

abbrev fixedBits (fixed : List (Option Nat)) : List Bool :=
  BinaryEncoding.listBits (BinaryEncoding.optionBits BinaryEncoding.natBits) fixed

theorem run_encoded (fixed : List (Option Nat)) (assignments : List Nat) :
    run ⟨.entry, fixedBits fixed, BinaryEncoding.assignmentBits assignments⟩ =
      resultView (ExtensionCertificate.agreesBool fixed assignments) := by
  induction fixed generalizing assignments with
  | nil =>
      cases assignments with
      | nil =>
          rw [run_step _ (by simp [Terminal])]
          exact run_checkEnd_empty
      | cons value assignments =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, fixedBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, ExtensionCertificate.agreesBool, run_drainFixed]
  | cons entry fixed ih =>
      cases assignments with
      | nil =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, fixedBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, ExtensionCertificate.agreesBool, run_drainFixed]
      | cons value assignments =>
          rw [run_step _ (by simp [Terminal])]
          change run ⟨.option,
            BinaryEncoding.optionBits BinaryEncoding.natBits entry ++ fixedBits fixed,
            BinaryEncoding.natBits value ++ BinaryEncoding.assignmentBits assignments⟩ = _
          cases entry with
          | none =>
              rw [run_step _ (by simp [Terminal])]
              change run ⟨.skipFlag, fixedBits fixed,
                BinPackingCompleteness.BinaryEncoding.frame value.bits ++
                  BinaryEncoding.assignmentBits assignments⟩ =
                resultView (ExtensionCertificate.agreesBool fixed assignments)
              rw [run_skipFrame]
              exact ih assignments
          | some label =>
              rw [run_step _ (by simp [Terminal])]
              change run ⟨.compareFlag,
                BinPackingCompleteness.BinaryEncoding.frame label.bits ++ fixedBits fixed,
                BinPackingCompleteness.BinaryEncoding.frame value.bits ++
                  BinaryEncoding.assignmentBits assignments⟩ =
                resultView (decide (label = value) &&
                  ExtensionCertificate.agreesBool fixed assignments)
              rw [run_compareFrame]
              have bits_iff : label.bits = value.bits ↔ label = value := by
                constructor
                · intro h
                  have values := congrArg BinPackingCompleteness.BinaryEncoding.bitsValue h
                  simpa only [BinPackingCompleteness.BinaryEncoding.bitsValue_bits] using values
                · rintro rfl
                  rfl
              by_cases equal : label = value
              · subst value
                simpa using ih assignments
              · simp [bits_iff, equal]

noncomputable def agreementTime : Polynomial Nat := Polynomial.X + 3

structure RawRun (fixed assignments : List Bool) where
  finish : View
  terminal : Terminal finish.label
  execution : StateTransition.EvalsToInTime machine.step (cfg .entry fixed assignments)
    (some finish.cfg) (agreementTime.eval (fixed.length + assignments.length))

noncomputable def rawInTime (fixed assignments : List Bool) : RawRun fixed assignments := by
  let view : View := ⟨.entry, fixed, assignments⟩
  let trace := runTrace view
  let steps := Classical.choose trace
  let result := Classical.choose_spec trace
  refine ⟨run view, run_isTerminal view, ?_⟩
  exact {
    steps := steps
    evals_in_steps := by
      change (advance machine.step)^[steps] (some view.cfg) = some (run view).cfg
      exact result.2
    steps_le_m := by
      simpa only [steps, view, potential, rank, agreementTime, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_ofNat] using result.1 }

noncomputable def agreementInTime (fixed : List (Option Nat)) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg .entry (fixedBits fixed) (BinaryEncoding.assignmentBits assignments))
      (some (cfg (if ExtensionCertificate.agreesBool fixed assignments then
        .accept else .reject) [] []))
      (agreementTime.eval
        ((fixedBits fixed).length + (BinaryEncoding.assignmentBits assignments).length)) := by
  have trace := (rawInTime (fixedBits fixed) (BinaryEncoding.assignmentBits assignments)).execution
  change StateTransition.EvalsToInTime machine.step _
    (some (run ⟨.entry, fixedBits fixed, BinaryEncoding.assignmentBits assignments⟩).cfg) _ at trace
  rw [run_encoded] at trace
  simpa only [resultView, View.cfg] using trace

theorem flagStep (accepted : Bool) :
    machine.step (cfg (if accepted then .accept else .reject) [] []) =
      some ⟨none, (none, none), tapes [accepted] []⟩ := by
  cases accepted <;>
    simp [FinTM2.step, TM2.step, machine, program, cfg, TM2.stepAux, update_fixed, tapes] <;> rfl

noncomputable def agreementFlagInTime (fixed : List (Option Nat)) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg .entry (fixedBits fixed) (BinaryEncoding.assignmentBits assignments))
      (some ⟨none, (none, none), tapes [ExtensionCertificate.agreesBool fixed assignments] []⟩)
      (agreementTime.eval
        ((fixedBits fixed).length + (BinaryEncoding.assignmentBits assignments).length) + 1) := by
  let stage := agreementInTime fixed assignments
  let finish : machine.Cfg :=
    ⟨none, (none, none), tapes [ExtensionCertificate.agreesBool fixed assignments] []⟩
  have last : StateTransition.EvalsToInTime machine.step
      (cfg (if ExtensionCertificate.agreesBool fixed assignments then .accept else .reject) [] [])
      (some finish) 1 := {
    steps := 1
    evals_in_steps := by
      change machine.step
        (cfg (if ExtensionCertificate.agreesBool fixed assignments then .accept else .reject) [] []) =
        some finish
      exact flagStep (ExtensionCertificate.agreesBool fixed assignments)
    steps_le_m := Nat.le_refl _ }
  simpa only [Nat.add_comm] using StateTransition.EvalsToInTime.trans machine.step
    _ 1 _ _ (some finish) stage last

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end BinPackingGap.ExtensionAgreementMachine

end OAI
