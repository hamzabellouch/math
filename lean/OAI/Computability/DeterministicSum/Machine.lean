import Mathlib

namespace OAI

/-! Finite deterministic word-RAM states, exact costs and uniform decision specifications. -/

namespace DeterministicThreeSum

def ThreeSUM {n : ℕ} (x : Fin n → ℤ) : Prop :=
  ∃ i j k : Fin n, i < j ∧ j < k ∧ x i + x j + x k = 0

def InUniverse {n : ℕ} (C : ℕ) (x : Fin n → ℤ) : Prop :=
  ∀ i, |x i| ≤ (n : ℤ) ^ C

noncomputable def wordWidth (factor n : ℕ) : ℕ :=
  ⌈(factor : ℝ) * Real.logb 2 (n + 2)⌉₊

def wordModulus (w : ℕ) : ℕ := 2 ^ w

inductive Operand where
  | literal : ℕ → Operand
  | register : ℕ → Operand
  deriving DecidableEq

inductive BinOp where
  | add | sub | mul | quot | rem | band | bor | bxor | shl | shr
  deriving DecidableEq

inductive Test where
  | eq | lt | le
  deriving DecidableEq

inductive Instruction where
  | assign (dst : ℕ) (src : Operand)
  | binary (dst : ℕ) (op : BinOp) (left right : Operand)
  | load (dst : ℕ) (address : Operand)
  | store (address value : Operand)
  | branch (test : Test) (left right : Operand) (yes no : ℕ)
  | jump (target : ℕ)
  | halt (answer : Bool)
  deriving DecidableEq

abbrev Program := List Instruction

structure State where
  pc : ℕ
  registers : ℕ → ℕ
  memory : ℕ → Option ℕ
  answer : Option Bool

def readOperand (w : ℕ) (s : State) : Operand → ℕ
  | .literal v => v % wordModulus w
  | .register r => s.registers r % wordModulus w

def evalBinOp (w : ℕ) (op : BinOp) (a b : ℕ) : Option ℕ :=
  let q := wordModulus w
  match op with
  | .add => some ((a + b) % q)
  | .sub => some ((a + q - b) % q)
  | .mul => some ((a * b) % q)
  | .quot => if b = 0 then none else some (a / b)
  | .rem => if b = 0 then none else some (a % b)
  | .band => some ((a &&& b) % q)
  | .bor => some ((a ||| b) % q)
  | .bxor => some ((a ^^^ b) % q)
  | .shl => if b < w then some ((a <<< b) % q) else none
  | .shr => if b < w then some (a >>> b) else none

def evalTest : Test → ℕ → ℕ → Bool
  | .eq, a, b => decide (a = b)
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)

def putRegister (s : State) (dst value : ℕ) : State :=
  { s with registers := Function.update s.registers dst value, pc := s.pc + 1 }

def step (w : ℕ) (p : Program) (s : State) : Option State := do
  if s.answer.isSome then none else do
    let i ← p[s.pc]?
    match i with
    | .assign dst src => pure (putRegister s dst (readOperand w s src))
    | .binary dst op left right =>
      let value ← evalBinOp w op (readOperand w s left) (readOperand w s right)
      pure (putRegister s dst value)
    | .load dst address =>
      let value ← s.memory (readOperand w s address)
      pure (putRegister s dst value)
    | .store address value =>
      pure { s with
        pc := s.pc + 1
        memory := Function.update s.memory (readOperand w s address)
          (some (readOperand w s value)) }
    | .branch test left right yes no =>
      pure { s with pc := if evalTest test (readOperand w s left) (readOperand w s right) then yes else no }
    | .jump target => pure { s with pc := target }
    | .halt answer => pure { s with answer := some answer }

def encodeWord (w : ℕ) (a : ℤ) : ℕ :=
  (a % (wordModulus w : ℤ)).toNat

def initialState {n : ℕ} (w : ℕ) (x : Fin n → ℤ) : State where
  pc := 0
  registers := fun _ => 0
  memory := fun a =>
    if a = 0 then some (n % wordModulus w)
    else if h : a - 1 < n then some (encodeWord w (x ⟨a - 1, h⟩))
    else none
  answer := none

def run (w : ℕ) (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

def registerBound : Instruction → ℕ
  | .assign d (.register r) => max (d+1) (r+1)
  | .assign d _ => d+1
  | .binary d _ a b => max (d+1) (max (operandBound a) (operandBound b))
  | .load d a => max (d+1) (operandBound a)
  | .store a b => max (operandBound a) (operandBound b)
  | .branch _ a b _ _ => max (operandBound a) (operandBound b)
  | _ => 0
where operandBound : Operand → ℕ
  | .literal _ => 0
  | .register r => r+1

def setupCost (p : Program) (n : ℕ) : ℕ :=
  n + 1 + ((p.map registerBound).foldl max 0)

def ProgramDecidesWithin (p : Program) (widthFactor universeExponent : ℕ)
    (saving timeConstant : ℝ) : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ x : Fin n → ℤ, InUniverse universeExponent x →
    ∃ (t : ℕ) (s : State) (answer : Bool),
      run (wordWidth widthFactor n) p t
        (initialState (wordWidth widthFactor n) x) = some s ∧
      s.answer = some answer ∧
      (answer = true ↔ ThreeSUM x) ∧
      (t + setupCost p n : ℝ) ≤ timeConstant * (n : ℝ) ^ (2 - saving)

noncomputable def deterministicSaving : ℝ := (2 : ℝ) ^ (-(1546 : ℤ))

def DeterministicCubicStatement : Prop :=
  ∃ p : Program, ∃ C : ℝ, 0 < C ∧
    ProgramDecidesWithin p 4 3 deterministicSaving C

def PolynomialUniverseStatement : Prop :=
  ∀ C : ℕ, 0 < C → ∃ p : Program, ∃ A : ℝ, 0 < A ∧
    ProgramDecidesWithin p (C + 4) C deterministicSaving A

end DeterministicThreeSum

end OAI
