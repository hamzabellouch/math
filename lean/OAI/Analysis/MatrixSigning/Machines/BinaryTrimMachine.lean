import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FiniteDispatch
import OAI.Analysis.MatrixSigning.Machines.BinaryNormalize

namespace OAI

namespace KS.W19.BinaryTrimMachine
open KS.W29

def dispatch (s : Fin 2) (heads : Fin 27) (_coin : Bool) : Instruction 2 :=
  let top := heads.val / 9
  if top = 0 then Instruction.halt 2
  else if s = 0 ∧ top = 1 then ⟨some 0, .stay, .stay, .pop⟩
  else ⟨some 1, .stay, .push (top == 2), .pop⟩

def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

def cfg (s : Option (Fin 2)) (input output scratch : List Bool) : Config 2 :=
  ⟨s, fun j => if j = 0 then input else if j = 1 then output else scratch⟩

theorem table_lookup (s : Fin 2) (c : Config 2) (coin : Bool) :
    machine.table.getD (transitionIndex s c coin) (Instruction.halt 2) =
      if topCode (c.«stacks» 2) = 0 then Instruction.halt 2
      else if s = 0 ∧ topCode (c.«stacks» 2) = 1 then ⟨some 0, .stay, .stay, .pop⟩
      else ⟨some 1, .stay, .push (topCode (c.«stacks» 2) == 2), .pop⟩ := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  have h2 := topCode_lt_three (c.«stacks» 2)
  have htop : headCode c / 9 = topCode (c.«stacks» 2) := by unfold headCode; omega
  unfold machine
  rw [FiniteDispatch.lookup_compile]
  simp only [dispatch, htop]
  rfl

theorem step_skip (input output scratch : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) input output (false :: scratch)) coin =
      cfg (some 0) input output scratch := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_first_one (input output scratch : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) input output (true :: scratch)) coin =
      cfg (some 1) input (true :: output) scratch := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_copy (b : Bool) (input output scratch : List Bool) (coin : Bool) :
    machine.step (cfg (some 1) input output (b :: scratch)) coin =
      cfg (some 1) input (b :: output) scratch := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_done (s : Fin 2) (input output : List Bool) (coin : Bool) :
    machine.step (cfg (some s) input output []) coin = cfg none input output [] := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_copy (input output scratch bits : List Bool)
    (hlen : bits.length = scratch.length + 1) :
    machine.run (cfg (some 1) input output scratch) bits =
      cfg none input (scratch.reverse ++ output) [] := by
  induction scratch generalizing output bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : rest = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
      subst rest
      simpa [BinaryMachine.run] using step_done 1 input output coin
  | cons b bs ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : rest.length = bs.length + 1 := by simpa using hlen
      erw [BinaryMachine.run.eq_2, step_copy, ih _ _ hr]
      simp [List.reverse_cons, List.append_assoc]
      rfl

theorem run_trim (input output scratch bits : List Bool)
    (hlen : bits.length = scratch.length + 1) :
    machine.run (cfg (some 0) input output scratch) bits =
      cfg none input (trimBits scratch.reverse ++ output) [] := by
  induction scratch generalizing output bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : rest = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
      subst rest
      simpa [BinaryMachine.run, trimBits] using step_done 0 input output coin
  | cons b bs ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : rest.length = bs.length + 1 := by simpa using hlen
      cases b
      · erw [BinaryMachine.run.eq_2, step_skip, ih _ _ hr]
        simp [List.reverse_cons, trimBits_append_false]
        rfl
      · erw [BinaryMachine.run.eq_2, step_first_one, run_copy input (true :: output) bs rest hr]
        simp [List.reverse_cons, trimBits_append_true, List.append_assoc]
        rfl

theorem run_payload (input raw bits : List Bool)
    (hlen : bits.length = raw.length + 1) :
    machine.run (cfg (some 0) input [] raw.reverse) bits =
      cfg none input (Computability.encodeNat (bitsValue raw)) [] := by
  have h := run_trim input [] raw.reverse bits (by simpa using hlen)
  simpa [trimBits_eq_encodeNat] using h

theorem table_length : machine.table.length = 108 := by
  simp only [machine, FiniteDispatch.compile, List.length_ofFn]

end KS.W19.BinaryTrimMachine

end OAI
