import Mathlib

namespace OAI

namespace CurrentKS

/-- Escaped binary words. -/
def frame : List Bool → List Bool
  | [] => [true]
  | b :: bs => false :: b :: frame bs

def encodeNat (n : ℕ) : List Bool := frame (Computability.encodeNat n)

def encodeInt : ℤ → List Bool
  | .ofNat n => false :: encodeNat n
  | .negSucc n => true :: encodeNat n

/-- The two binary fields are a numerator and a positive denominator. -/
structure RationalEntry where
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0 < denominator

def RationalEntry.value (a : RationalEntry) : ℚ :=
  (a.numerator : ℚ) / (a.denominator : ℚ)

def RationalEntry.encode (a : RationalEntry) : List Bool :=
  encodeInt a.numerator ++ encodeNat a.denominator

abbrev RationalComplex := RationalEntry × RationalEntry

def encodeComplex (z : RationalComplex) : List Bool := z.1.encode ++ z.2.encode

def toComplex (z : RationalComplex) : ℂ :=
  ⟨(z.1.value : ℝ), (z.2.value : ℝ)⟩

structure Input where
  d : ℕ
  N : ℕ
  entries : Fin N → Matrix (Fin d) (Fin d) RationalComplex

/-- Row-major entries; a matrix-record delimiter retains explicit list length
also for order-zero matrices. This constant-per-matrix framing is polynomially
equivalent to dense binary matrix listing in positive dimension. -/
def Input.encodeMatrix (x : Input) (i : Fin x.N) : List Bool :=
  true :: ((List.ofFn fun j : Fin x.d =>
    (List.ofFn fun k : Fin x.d => x.entries i j k).flatMap encodeComplex).flatten)

def Input.encode (x : Input) : List Bool :=
  encodeNat x.d ++ encodeNat x.N ++ (List.ofFn x.encodeMatrix).flatten

def Input.length (x : Input) : ℕ := x.encode.length

def Input.matrix (x : Input) (i : Fin x.N) : Matrix (Fin x.d) (Fin x.d) ℂ :=
  (x.entries i).map toComplex

noncomputable def opNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

def Admissible (x : Input) : Prop :=
  ∀ i, (x.matrix i).IsHermitian ∧ (x.matrix i).rank ≤ 1

def signValue (b : Bool) : ℝ := if b then 1 else -1

noncomputable def signedSum (x : Input) (bits : List Bool) :
    Matrix (Fin x.d) (Fin x.d) ℂ :=
  ∑ i, signValue (bits.getD i.val false) • x.matrix i

noncomputable def variance (x : Input) : Matrix (Fin x.d) (Fin x.d) ℂ :=
  ∑ i, x.matrix i * x.matrix i

def GoodOutput (x : Input) (bits : List Bool) : Prop :=
  bits.length = x.N ∧ opNorm (signedSum x bits) ≤ 40 * Real.sqrt (opNorm (variance x))

inductive StackAction where
  | stay
  | pop
  | push (bit : Bool)
  deriving DecidableEq

def StackAction.apply : StackAction → List Bool → List Bool
  | .stay, xs => xs
  | .pop, xs => xs.tail
  | .push b, xs => b :: xs

structure Instruction (k q : ℕ) where
  next : Option (Fin q)
  actions : Fin k → StackAction

def Instruction.halt (k q : ℕ) : Instruction k q := ⟨none, fun _ => .stay⟩

structure Machine where
  stackCount : ℕ
  states : ℕ
  initial : Fin states
  inputStack : Fin stackCount
  outputStack : Fin stackCount
  table : List (Instruction stackCount states)

structure Config (k q : ℕ) where
  state : Option (Fin q)
  «stacks» : Fin k → List Bool

def topCode : List Bool → ℕ
  | [] => 0
  | false :: _ => 1
  | true :: _ => 2

def headsCode : (k : ℕ) → (Fin k → List Bool) → ℕ
  | 0, _ => 0
  | k + 1, s => topCode (s 0) + 3 * headsCode k (fun j => s j.succ)

def Machine.step (M : Machine) (c : Config M.stackCount M.states) :
    Config M.stackCount M.states :=
  match c.state with
  | none => c
  | some q =>
    let instruction := M.table.getD
      (3 ^ M.stackCount * q.val + headsCode M.stackCount c.stacks)
      (Instruction.halt M.stackCount M.states)
    ⟨instruction.next, fun j => (instruction.actions j).apply (c.stacks j)⟩

def Machine.init (M : Machine) (input : List Bool) : Config M.stackCount M.states :=
  ⟨some M.initial, fun j => if j = M.inputStack then input else []⟩

def Machine.run (M : Machine) (input : List Bool) (fuel : ℕ) :
    Config M.stackCount M.states := (M.step^[fuel]) (M.init input)

def DeterministicRankOneSigning : Prop :=
  ∃ M : Machine, ∃ C degree : ℕ, 0 < C ∧
    ∀ x : Input, Admissible x →
      let result := M.run x.encode (C * (x.length + 1) ^ degree)
      result.state = none ∧ GoodOutput x (result.stacks M.outputStack)

end CurrentKS

end OAI
