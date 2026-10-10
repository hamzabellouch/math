import Mathlib

namespace OAI

section

namespace KS.W29

inductive StackAction where
  | stay
  | pop
  | push (bit : Bool)
  deriving DecidableEq, Repr

def StackAction.apply : StackAction → List Bool → List Bool
  | .stay, xs => xs
  | .pop, xs => xs.tail
  | .push b, xs => b :: xs

theorem StackAction.length_apply_le (a : StackAction) (xs : List Bool) :
    (a.apply xs).length ≤ xs.length + 1 := by
  cases a <;> cases xs <;> simp [StackAction.apply]
  omega

structure Instruction (q : Nat) where
  next : Option (Fin q)
  first : StackAction
  second : StackAction
  third : StackAction
  deriving DecidableEq, Repr

def Instruction.action {q : Nat} (i : Instruction q) (stack : Fin 3) : StackAction :=
  if stack = 0 then i.first else if stack = 1 then i.second else i.third

def Instruction.halt (q : Nat) : Instruction q :=
  ⟨none, .stay, .stay, .stay⟩

structure BinaryMachine where
  states : Nat
  initial : Fin states
  table : List (Instruction states)

structure Config (q : Nat) where
  state : Option (Fin q)
  «stacks» : Fin 3 → List Bool

def topCode : List Bool → Nat
  | [] => 0
  | false :: _ => 1
  | true :: _ => 2

theorem topCode_lt_three (xs : List Bool) : topCode xs < 3 := by
  cases xs with
  | nil => decide
  | cons b xs => cases b <;> simp [topCode]

def headCode {q : Nat} (c : Config q) : Nat :=
  topCode (c.«stacks» 0) + 3 * topCode (c.«stacks» 1) + 9 * topCode (c.«stacks» 2)

theorem headCode_lt (q : Nat) (c : Config q) : headCode c < 27 := by
  have h₀ := topCode_lt_three (c.«stacks» 0)
  have h₁ := topCode_lt_three (c.«stacks» 1)
  have h₂ := topCode_lt_three (c.«stacks» 2)
  unfold headCode
  omega

def bitCode (b : Bool) : Nat := if b then 1 else 0

def transitionIndex {q : Nat} (s : Fin q) (c : Config q) (b : Bool) : Nat :=
  54 * s.val + 2 * headCode c + bitCode b

theorem transitionIndex_lt {q : Nat} (s : Fin q) (c : Config q) (b : Bool) :
    transitionIndex s c b < 54 * q := by
  have hs := s.isLt
  have hc := headCode_lt q c
  have hb : bitCode b < 2 := by cases b <;> decide
  unfold transitionIndex
  omega

def BinaryMachine.step (M : BinaryMachine) (c : Config M.states) (b : Bool) :
    Config M.states :=
  match c.state with
  | none => c
  | some s =>
      let i := M.table.getD (transitionIndex s c b) (Instruction.halt M.states)
      ⟨i.next, fun j => (i.action j).apply (c.«stacks» j)⟩

def BinaryMachine.init (M : BinaryMachine) (input : List Bool) : Config M.states :=
  ⟨some M.initial, fun j => if j = 0 then input else []⟩

def BinaryMachine.run (M : BinaryMachine) : Config M.states → List Bool → Config M.states
  | c, [] => c
  | c, b :: bs => M.run (M.step c b) bs

def BinaryMachine.output (M : BinaryMachine) (input bits : List Bool) : List Bool :=
  (M.run (M.init input) bits).«stacks» 1

@[simp] theorem BinaryMachine.step_halted (M : BinaryMachine) (c : Config M.states)
    (h : c.state = none) (b : Bool) : M.step c b = c := by
  simp [BinaryMachine.step, h]

theorem BinaryMachine.run_halted (M : BinaryMachine) (c : Config M.states)
    (h : c.state = none) (bits : List Bool) : M.run c bits = c := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simpa [BinaryMachine.run, M.step_halted c h b] using ih

theorem BinaryMachine.run_append (M : BinaryMachine) (c : Config M.states)
    (xs ys : List Bool) : M.run c (xs ++ ys) = M.run (M.run c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons b bs ih => simpa [BinaryMachine.run] using ih (M.step c b)

theorem BinaryMachine.step_stack_length_le (M : BinaryMachine) (c : Config M.states)
    (b : Bool) (j : Fin 3) : ((M.step c b).«stacks» j).length ≤ (c.«stacks» j).length + 1 := by
  unfold BinaryMachine.step
  cases h : c.state with
  | none => simp
  | some s => exact StackAction.length_apply_le _ _

theorem BinaryMachine.run_stack_length_le (M : BinaryMachine) (c : Config M.states)
    (bits : List Bool) (j : Fin 3) :
    ((M.run c bits).«stacks» j).length ≤ (c.«stacks» j).length + bits.length := by
  induction bits generalizing c with
  | nil => simp [BinaryMachine.run]
  | cons b bs ih =>
      have hstep := M.step_stack_length_le c b j
      have hrun := ih (M.step c b)
      simp only [BinaryMachine.run, List.length_cons]
      omega

theorem BinaryMachine.output_length_le (M : BinaryMachine) (input bits : List Bool) :
    (M.output input bits).length ≤ bits.length := by
  have h := M.run_stack_length_le (M.init input) bits 1
  simpa [BinaryMachine.output, BinaryMachine.init] using h

def polynomialFuel (coefficient degree inputLength : Nat) : Nat :=
  coefficient * (inputLength + 1) ^ degree

abbrev FairSeed (fuel : Nat) := Fin fuel → Bool

def BinaryMachine.runSeed (M : BinaryMachine) (input : List Bool) {fuel : Nat}
    (seed : FairSeed fuel) : Config M.states := M.run (M.init input) (List.ofFn seed)

noncomputable def BinaryMachine.successCount (M : BinaryMachine) (input : List Bool)
    (fuel : Nat) (good : List Bool → Prop) : Nat := by
  classical
  exact (Finset.univ.filter fun seed : FairSeed fuel =>
    good ((M.runSeed input seed).«stacks» 1)).card

def BinaryMachine.HaltsWithin (M : BinaryMachine) (input : List Bool) (fuel : Nat) : Prop :=
  ∀ seed : FairSeed fuel, (M.runSeed input seed).state = none

def BinaryMachine.SucceedsTwoThirds (M : BinaryMachine) (input : List Bool) (fuel : Nat)
    (good : List Bool → Prop) : Prop :=
  2 * 2 ^ fuel ≤ 3 * M.successCount input fuel good

theorem BinaryMachine.haltsWithin_iff_bitLists (M : BinaryMachine) (input : List Bool)
    (fuel : Nat) : M.HaltsWithin input fuel ↔
      ∀ bits : List Bool, bits.length = fuel → (M.run (M.init input) bits).state = none := by
  constructor
  · intro h bits hlen
    subst fuel
    simpa [BinaryMachine.runSeed, List.ofFn_get] using h bits.get
  · intro h seed
    exact h (List.ofFn seed) (by simp)

theorem BinaryMachine.run_append_of_halted (M : BinaryMachine) (c : Config M.states)
    (xs ys : List Bool) (h : (M.run c xs).state = none) :
    M.run c (xs ++ ys) = M.run c xs := by
  rw [M.run_append, M.run_halted _ h]

theorem BinaryMachine.haltsWithin_mono (M : BinaryMachine) (input : List Bool)
    {fuel larger : Nat} (h : M.HaltsWithin input fuel) (hle : fuel ≤ larger) :
    M.HaltsWithin input larger := by
  rw [M.haltsWithin_iff_bitLists] at h ⊢
  intro bits hbits
  have htake : (bits.take fuel).length = fuel := by
    simp [List.length_take, hbits, Nat.min_eq_left hle]
  have hh := h (bits.take fuel) htake
  have heq : M.run (M.init input) bits = M.run (M.init input) (bits.take fuel) := by
    conv_lhs => rw [← List.take_append_drop fuel bits]
    exact M.run_append_of_halted _ _ _ hh
  rw [heq]
  exact hh

theorem BinaryMachine.runSeed_output_length_le (M : BinaryMachine) (input : List Bool)
    {fuel : Nat} (seed : FairSeed fuel) :
    ((M.runSeed input seed).«stacks» 1).length ≤ fuel := by
  simpa [BinaryMachine.runSeed, BinaryMachine.output] using
    M.output_length_le input (List.ofFn seed)

end KS.W29

end

end OAI
