import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedSequential

namespace OAI

section

namespace KS.W29.FixedLoop
open KS.W29.FixedSequential (Program ofMachine ActiveFor HaltsAfter fetch)
open KS.W01.FixedStack (Config Instruction observedHeads)

inductive Choice where
  | halt
  | restart
  | call
  deriving DecidableEq

structure GuardInstruction (k : Nat) where
  choice : Choice
  actions : Vector KS.W29.StackAction k

def guardState {k : Nat} (P : Program k) : Fin (P.states + 1) := ⟨0, by omega⟩

def bodyState {k : Nat} (P : Program k) (s : Fin P.states) : Fin (P.states + 1) :=
  ⟨s.val + 1, by have h := s.isLt; omega⟩

def guardInstruction {k : Nat} (P : Program k) (i : GuardInstruction k) :
    KS.W01.FixedStack.Instruction k (P.states + 1) :=
  ⟨match i.choice with
    | .halt => none
    | .restart => some (guardState P)
    | .call => some (bodyState P P.initial), i.actions⟩

def bodyInstruction {k : Nat} (P : Program k) (i : KS.W01.FixedStack.Instruction k P.states) :
    KS.W01.FixedStack.Instruction k (P.states + 1) :=
  ⟨some (match i.next with
    | none => guardState P
    | some s => bodyState P s), i.actions⟩

def dispatch {k : Nat} (P : Program k)
    (guard : (Fin k → Fin 3) → Bool → GuardInstruction k)
    (s : Fin (P.states + 1)) (heads : Fin k → Fin 3) (b : Bool) :
    KS.W01.FixedStack.Instruction k (P.states + 1) :=
  if h : s.val = 0 then guardInstruction P (guard heads b)
  else bodyInstruction P (fetch P ⟨s.val - 1, by have hs := s.isLt; omega⟩ heads b)

def loop {k : Nat} (P : Program k)
    (guard : (Fin k → Fin 3) → Bool → GuardInstruction k) : Program k :=
  ofMachine (KS.W01.FixedStack.compile (guardState P) P.input P.output (dispatch P guard))

@[simp] theorem loop_states {k : Nat} (P : Program k) (guard) :
    (loop P guard).states = P.states + 1 := rfl

@[simp] theorem loop_input {k : Nat} (P : Program k) (guard) :
    (loop P guard).input = P.input := rfl

@[simp] theorem loop_output {k : Nat} (P : Program k) (guard) :
    (loop P guard).output = P.output := rfl

theorem loop_table_length {k : Nat} (P : Program k) (guard) :
    (loop P guard).table.length = (P.states + 1) * (3 ^ k * 2) := by
  change (KS.W01.FixedStack.compile (guardState P) P.input P.output
    (dispatch P guard)).table.length = _
  exact KS.W01.FixedStack.compile_table_length _ _ _ _

@[simp] theorem loop_initial {k : Nat} (P : Program k) (guard) :
    (loop P guard).initial = guardState P := rfl

@[simp] theorem loop_toMachine {k : Nat} (P : Program k) (guard) :
    (loop P guard).toMachine =
      KS.W01.FixedStack.compile (guardState P) P.input P.output (dispatch P guard) :=
  KS.W29.FixedSequential.toMachine_ofMachine _

@[simp] theorem dispatch_guard {k : Nat} (P : Program k) (guard) (heads) (b) :
    dispatch P guard (guardState P) heads b = guardInstruction P (guard heads b) := by
  simp [dispatch, guardState]

@[simp] theorem dispatch_body {k : Nat} (P : Program k) (guard) (s : Fin P.states) (heads) (b) :
    dispatch P guard (bodyState P s) heads b = bodyInstruction P (fetch P s heads b) := by
  simp [dispatch, bodyState]

def liftBody {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states) : KS.W01.FixedStack.Config k (P.states + 1) :=
  ⟨some (match c.state with
    | none => guardState P
    | some s => bodyState P s), c.«stacks»⟩

theorem step_guard {k : Nat} (P : Program k) (guard)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (loop P guard).toMachine.step ⟨some (guardState P), «stacks»⟩ b =
      let heads := observedHeads (KS.W01.FixedStack.Config.mk (some (guardState P)) «stacks»)
      let i := guardInstruction P (guard heads b)
      KS.W01.FixedStack.Config.mk i.next (fun j => (i.action j).apply («stacks» j)) := by
  change (KS.W01.FixedStack.compile (guardState P) P.input P.output
    (dispatch P guard)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_guard]

theorem step_body {k : Nat} (P : Program k) (guard) (s : Fin P.states)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (loop P guard).toMachine.step ⟨some (bodyState P s), «stacks»⟩ b =
      liftBody P (P.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (guardState P) P.input P.output
    (dispatch P guard)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_body]
  rfl

theorem step_liftBody {k : Nat} (P : Program k) (guard) (c : KS.W01.FixedStack.Config k P.states)
    (b : Bool) (h : c.state ≠ none) :
    (loop P guard).toMachine.step (liftBody P c) b =
      liftBody P (P.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => exact (h rfl).elim
  | some s => exact step_body P guard s «stacks» b

theorem run_body {k : Nat} (P : Program k) (guard) (c : KS.W01.FixedStack.Config k P.states)
    (bits : List Bool) (h : ActiveFor P c bits) :
    (loop P guard).toMachine.run (liftBody P c) bits =
      liftBody P (P.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (loop P guard).toMachine.run
        ((loop P guard).toMachine.step (liftBody P c) b) bs =
        liftBody P (P.toMachine.run (P.toMachine.step c b) bs)
      erw [step_liftBody P guard c b h.1]
      exact ih _ h.2

theorem run_body_then {k : Nat} (P : Program k) (guard) (c : KS.W01.FixedStack.Config k P.states)
    (first rest : List Bool) (h : HaltsAfter P c first) :
    (loop P guard).toMachine.run (liftBody P c) (first ++ rest) =
      (loop P guard).toMachine.run
        ⟨some (guardState P), (P.toMachine.run c first).«stacks»⟩ rest := by
  erw [KS.W01.FixedStack.Machine.run_append, run_body P guard c first h.1]
  have he : liftBody P (P.toMachine.run c first) =
      ⟨some (guardState P), (P.toMachine.run c first).«stacks»⟩ := by
    simp [liftBody, h.2]
  rw [he]
  rfl

theorem run_body_within {k : Nat} (P : Program k) (guard) (c : KS.W01.FixedStack.Config k P.states)
    (fuel : Nat) (h : KS.W29.FixedSequential.HaltsFromWithin P c fuel)
    (bits : List Bool) (hlen : fuel ≤ bits.length) :
    ∃ first rest : List Bool, bits = first ++ rest ∧ first.length ≤ fuel ∧
      HaltsAfter P c first ∧
      (loop P guard).toMachine.run (liftBody P c) bits =
        (loop P guard).toMachine.run
          ⟨some (guardState P), (P.toMachine.run c (bits.take fuel)).«stacks»⟩ rest := by
  have ht : (bits.take fuel).length = fuel := by
    simp [List.length_take, Nat.min_eq_left hlen]
  obtain ⟨first, leftover, heq, hf⟩ :=
    KS.W29.FixedSequential.exists_halting_prefix P c (bits.take fuel) (h _ ht)
  have hfl : first.length ≤ fuel := by
    have hh := congrArg List.length heq
    simp only [List.length_append, ht] at hh
    omega
  have hwhole : bits = first ++ (leftover ++ bits.drop fuel) := by
    calc
      bits = bits.take fuel ++ bits.drop fuel := (List.take_append_drop fuel bits).symm
      _ = first ++ (leftover ++ bits.drop fuel) := by rw [heq, List.append_assoc]
  have hout : P.toMachine.run c (bits.take fuel) = P.toMachine.run c first := by
    erw [heq, KS.W01.FixedStack.Machine.run_append]
    exact P.toMachine.run_halted _ hf.2 leftover
  refine ⟨first, leftover ++ bits.drop fuel, hwhole, hfl, hf, ?_⟩
  rw [hout]
  conv_lhs => rw [hwhole]
  exact run_body_then P guard c first _ hf

end KS.W29.FixedLoop

end

end OAI
