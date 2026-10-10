import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedSequential

namespace OAI

section

namespace KS.W29.FixedBranch
open KS.W29.FixedSequential (Program ofMachine fetch HaltsFromWithin)
open KS.W01.FixedStack (Config Instruction observedHeads)

inductive Choice where
  | halt
  | left
  | right
  deriving DecidableEq

structure SelectInstruction (k : Nat) where
  choice : Choice
  actions : Vector KS.W29.StackAction k

def start {k : Nat} (P Q : Program k) : Fin (P.states + Q.states + 1) := ⟨0, by omega⟩

def leftState {k : Nat} (P Q : Program k) (s : Fin P.states) :
    Fin (P.states + Q.states + 1) := ⟨s.val + 1, by have h := s.isLt; omega⟩

def rightState {k : Nat} (P Q : Program k) (s : Fin Q.states) :
    Fin (P.states + Q.states + 1) := ⟨P.states + s.val + 1, by have h := s.isLt; omega⟩

def selectInstruction {k : Nat} (P Q : Program k) (i : SelectInstruction k) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states + 1) :=
  ⟨match i.choice with
    | .halt => none
    | .left => some (leftState P Q P.initial)
    | .right => some (rightState P Q Q.initial), i.actions⟩

def leftInstruction {k : Nat} (P Q : Program k) (i : KS.W01.FixedStack.Instruction k P.states) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states + 1) := ⟨i.next.map (leftState P Q), i.actions⟩

def rightInstruction {k : Nat} (P Q : Program k) (i : KS.W01.FixedStack.Instruction k Q.states) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states + 1) := ⟨i.next.map (rightState P Q), i.actions⟩

def dispatch {k : Nat} (P Q : Program k)
    (select : (Fin k → Fin 3) → Bool → SelectInstruction k)
    (s : Fin (P.states + Q.states + 1)) (heads : Fin k → Fin 3) (b : Bool) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states + 1) :=
  if h₀ : s.val = 0 then selectInstruction P Q (select heads b)
  else if h₁ : s.val < P.states + 1 then
    leftInstruction P Q (fetch P ⟨s.val - 1, by omega⟩ heads b)
  else
    rightInstruction P Q
      (fetch Q ⟨s.val - (P.states + 1), by have hs := s.isLt; omega⟩ heads b)

def branch {k : Nat} (P Q : Program k) (output : Fin k)
    (select : (Fin k → Fin 3) → Bool → SelectInstruction k) : Program k :=
  ofMachine (KS.W01.FixedStack.compile (start P Q) P.input output (dispatch P Q select))

@[simp] theorem branch_toMachine {k : Nat} (P Q : Program k) (output) (select) :
    (branch P Q output select).toMachine =
      KS.W01.FixedStack.compile (start P Q) P.input output (dispatch P Q select) :=
  KS.W29.FixedSequential.toMachine_ofMachine _

@[simp] theorem branch_initial {k : Nat} (P Q : Program k) (output) (select) :
    (branch P Q output select).initial = start P Q := rfl

@[simp] theorem branch_states {k : Nat} (P Q : Program k) (output) (select) :
    (branch P Q output select).states = P.states + Q.states + 1 := rfl

@[simp] theorem dispatch_start {k : Nat} (P Q : Program k) (select) (heads) (b) :
    dispatch P Q select (start P Q) heads b = selectInstruction P Q (select heads b) := by
  simp [dispatch, start]

@[simp] theorem dispatch_left {k : Nat} (P Q : Program k) (select)
    (s : Fin P.states) (heads) (b) :
    dispatch P Q select (leftState P Q s) heads b = leftInstruction P Q (fetch P s heads b) := by
  have hs : s.val + 1 < P.states + 1 := by have h := s.isLt; omega
  simp [dispatch, leftState, hs]

@[simp] theorem dispatch_right {k : Nat} (P Q : Program k) (select)
    (s : Fin Q.states) (heads) (b) :
    dispatch P Q select (rightState P Q s) heads b = rightInstruction P Q (fetch Q s heads b) := by
  have hs : ¬ P.states + s.val + 1 < P.states + 1 := by omega
  have he : P.states + s.val + 1 - (P.states + 1) = s.val := by omega
  simp [dispatch, rightState, hs, he]

def liftLeft {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states) :
    KS.W01.FixedStack.Config k (P.states + Q.states + 1) := ⟨c.state.map (leftState P Q), c.«stacks»⟩

def liftRight {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k Q.states) :
    KS.W01.FixedStack.Config k (P.states + Q.states + 1) := ⟨c.state.map (rightState P Q), c.«stacks»⟩

theorem step_start {k : Nat} (P Q : Program k) (output) (select)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (branch P Q output select).toMachine.step ⟨some (start P Q), «stacks»⟩ b =
      let i := selectInstruction P Q (select (observedHeads (KS.W01.FixedStack.Config.mk (some (start P Q)) «stacks»)) b)
      KS.W01.FixedStack.Config.mk i.next (fun j => (i.action j).apply («stacks» j)) := by
  change (KS.W01.FixedStack.compile (start P Q) P.input output
    (dispatch P Q select)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_start]

theorem step_left {k : Nat} (P Q : Program k) (output) (select)
    (s : Fin P.states) («stacks» : Fin k → List Bool) (b : Bool) :
    (branch P Q output select).toMachine.step ⟨some (leftState P Q s), «stacks»⟩ b =
      liftLeft P Q (P.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (start P Q) P.input output
    (dispatch P Q select)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_left]
  rfl

theorem step_right {k : Nat} (P Q : Program k) (output) (select)
    (s : Fin Q.states) («stacks» : Fin k → List Bool) (b : Bool) :
    (branch P Q output select).toMachine.step ⟨some (rightState P Q s), «stacks»⟩ b =
      liftRight P Q (Q.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (start P Q) P.input output
    (dispatch P Q select)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_right]
  rfl

theorem step_liftLeft {k : Nat} (P Q : Program k) (output) (select)
    (c : KS.W01.FixedStack.Config k P.states) (b : Bool) :
    (branch P Q output select).toMachine.step (liftLeft P Q c) b =
      liftLeft P Q (P.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s => exact step_left P Q output select s «stacks» b

theorem step_liftRight {k : Nat} (P Q : Program k) (output) (select)
    (c : KS.W01.FixedStack.Config k Q.states) (b : Bool) :
    (branch P Q output select).toMachine.step (liftRight P Q c) b =
      liftRight P Q (Q.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s => exact step_right P Q output select s «stacks» b

theorem run_left {k : Nat} (P Q : Program k) (output) (select)
    (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool) :
    (branch P Q output select).toMachine.run (liftLeft P Q c) bits =
      liftLeft P Q (P.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (branch P Q output select).toMachine.run
        ((branch P Q output select).toMachine.step (liftLeft P Q c) b) bs =
        liftLeft P Q (P.toMachine.run (P.toMachine.step c b) bs)
      erw [step_liftLeft P Q output select c b]
      exact ih (P.toMachine.step c b)

theorem run_right {k : Nat} (P Q : Program k) (output) (select)
    (c : KS.W01.FixedStack.Config k Q.states) (bits : List Bool) :
    (branch P Q output select).toMachine.run (liftRight P Q c) bits =
      liftRight P Q (Q.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (branch P Q output select).toMachine.run
        ((branch P Q output select).toMachine.step (liftRight P Q c) b) bs =
        liftRight P Q (Q.toMachine.run (Q.toMachine.step c b) bs)
      erw [step_liftRight P Q output select c b]
      exact ih (Q.toMachine.step c b)

theorem haltsFromWithin {k : Nat} (P Q : Program k) (output) (select)
    («stacks» : Fin k → List Bool) (fuel : Nat)
    (hleft : ∀ b : Bool, (select (observedHeads
      (KS.W01.FixedStack.Config.mk (some (start P Q)) «stacks»)) b).choice = .left → HaltsFromWithin P
      ⟨some P.initial, fun j => ((select (observedHeads
        (KS.W01.FixedStack.Config.mk (some (start P Q)) «stacks»)) b).actions[j.val]).apply («stacks» j)⟩ fuel)
    (hright : ∀ b : Bool, (select (observedHeads
      (KS.W01.FixedStack.Config.mk (some (start P Q)) «stacks»)) b).choice = .right → HaltsFromWithin Q
      ⟨some Q.initial, fun j => ((select (observedHeads
        (KS.W01.FixedStack.Config.mk (some (start P Q)) «stacks»)) b).actions[j.val]).apply («stacks» j)⟩ fuel) :
    HaltsFromWithin (branch P Q output select) ⟨some (start P Q), «stacks»⟩ (fuel + 1) := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons b bs =>
      have hbs : bs.length = fuel := by simpa using hbits
      change ((branch P Q output select).toMachine.run
        ((branch P Q output select).toMachine.step ⟨some (start P Q), «stacks»⟩ b) bs).state = none
      erw [step_start]
      let i := select (observedHeads (KS.W01.FixedStack.Config.mk (some (start P Q)) «stacks»)) b
      cases hi : i.choice with
      | halt =>
          have hh : (selectInstruction P Q i).next = none := by simp [selectInstruction, hi]
          change ((branch P Q output select).toMachine.run
            ⟨(selectInstruction P Q i).next, _⟩ bs).state = none
          rw [KS.W01.FixedStack.Machine.run_halted _ _ hh]
          exact hh
      | left =>
          have he : (selectInstruction P Q i).next = some (leftState P Q P.initial) := by
            simp [selectInstruction, hi]
          change ((branch P Q output select).toMachine.run
            ⟨(selectInstruction P Q i).next, _⟩ bs).state = none
          rw [he]
          change ((branch P Q output select).toMachine.run (liftLeft P Q ⟨some P.initial, _⟩) bs).state = none
          erw [run_left]
          exact congrArg (Option.map (leftState P Q)) (hleft b hi bs hbs)
      | right =>
          have he : (selectInstruction P Q i).next = some (rightState P Q Q.initial) := by
            simp [selectInstruction, hi]
          change ((branch P Q output select).toMachine.run
            ⟨(selectInstruction P Q i).next, _⟩ bs).state = none
          rw [he]
          change ((branch P Q output select).toMachine.run (liftRight P Q ⟨some Q.initial, _⟩) bs).state = none
          erw [run_right]
          exact congrArg (Option.map (rightState P Q)) (hright b hi bs hbs)

end KS.W29.FixedBranch

end

end OAI
