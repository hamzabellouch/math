import Mathlib

namespace OAI

/-! Exact logarithmic-space derandomization for finite transition-table machines. -/

namespace ExactDerandomization

abbrev Word := List Bool
abbrev Language := Set Word
abbrev CoinTape := ℕ → Bool

inductive Direction where
  | left | stay | right
  deriving DecidableEq

inductive InputSymbol where
  | leftMarker | bit (b : Bool) | rightMarker
  deriving DecidableEq

def Direction.move (d : Direction) (z : ℤ) : ℤ :=
  match d with
  | .left => z - 1
  | .stay => z
  | .right => z + 1

def Direction.moveInput (d : Direction) {n : ℕ} (i : Fin (n + 2)) : Fin (n + 2) :=
  match d with
  | .left => ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  | .stay => i
  | .right => ⟨min (i.val + 1) (n + 1), by omega⟩

def readInput (x : Word) (i : Fin (x.length + 2)) : InputSymbol :=
  if i.val = 0 then .leftMarker else
    match x[i.val - 1]? with
    | some b => .bit b
    | none => .rightMarker

structure Action (q w h : ℕ) where
  nextState : Fin (q + 1)
  write : Fin w → Bool
  workMove : Fin w → Direction
  inputMove : Fin h → Direction

structure Machine (q w h : ℕ) where
  initialState : Fin (q + 1)
  output : Fin (q + 1) → Option Bool
  transition : Fin (q + 1) → (Fin h → InputSymbol) → (Fin w → Bool) → Bool →
    Action q w h

structure Configuration (q w h n : ℕ) where
  state : Fin (q + 1)
  inputPos : Fin h → Fin (n + 2)
  workPos : Fin w → ℤ
  work : Fin w → ℤ → Bool

namespace Machine

variable {q w h : ℕ}

def initial (M : Machine q w h) (n : ℕ) : Configuration q w h n where
  state := M.initialState
  inputPos := fun _ => ⟨0, by omega⟩
  workPos := fun _ => 0
  work := fun _ _ => false

def step (M : Machine q w h) (x : Word) (b : Bool)
    (c : Configuration q w h x.length) : Configuration q w h x.length :=
  match M.output c.state with
  | some _ => c
  | none =>
    let a := M.transition c.state (fun j => readInput x (c.inputPos j))
      (fun k => c.work k (c.workPos k)) b
    { state := a.nextState
      inputPos := fun j => (a.inputMove j).moveInput (c.inputPos j)
      workPos := fun k => (a.workMove k).move (c.workPos k)
      work := fun k => Function.update (c.work k) (c.workPos k) (a.write k) }

def run (M : Machine q w h) (x : Word) (coins : CoinTape) :
    ℕ → Configuration q w h x.length
  | 0 => M.initial x.length
  | t + 1 => M.step x (coins t) (M.run x coins t)

def spaceThrough (M : Machine q w h) (x : Word) (coins : CoinTape) (t : ℕ) : ℕ :=
  ∑ k : Fin w, ((Finset.range (t + 1)).image
    (fun s => (M.run x coins s).workPos k)).card

def LogSpace (M : Machine q w h) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ (x : Word) (coins : CoinTape) (t : ℕ),
    M.spaceThrough x coins t ≤ c * Nat.clog 2 (x.length + 2)

def Deterministic (M : Machine q w h) : Prop :=
  ∀ s i v, M.transition s i v false = M.transition s i v true

def HaltsBy (M : Machine q w h) (x : Word) (t : ℕ) : Prop :=
  ∀ coins : CoinTape, ∃ b : Bool, M.output (M.run x coins t).state = some b

def Decides (M : Machine q w h) (A : Language) : Prop :=
  ∀ x : Word, ∃ (t : ℕ) (b : Bool),
    (b = true ↔ x ∈ A) ∧ ∀ coins : CoinTape,
      M.output (M.run x coins t).state = some b

def extendCoins {t : ℕ} (bits : Fin t → Bool) : CoinTape :=
  fun s => if hs : s < t then bits ⟨s, hs⟩ else false

def acceptanceProbability (M : Machine q w h) (x : Word) (t : ℕ) : ℚ :=
  ((Finset.univ.filter (fun bits : Fin t → Bool =>
    M.output (M.run x (extendCoins bits) t).state = some true)).card : ℚ) /
    (2 : ℚ) ^ t

end Machine

def polynomialClock (c k n : ℕ) : ℕ := c * (n + 2) ^ k

def L : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.Deterministic ∧ M.LogSpace ∧ M.Decides A}

def RL : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.LogSpace ∧ ∃ (c k : ℕ), 0 < c ∧ ∀ x : Word,
      M.HaltsBy x (polynomialClock c k x.length) ∧
      (x ∈ A → (1 / 2 : ℚ) ≤ M.acceptanceProbability x
        (polynomialClock c k x.length)) ∧
      (x ∉ A → M.acceptanceProbability x (polynomialClock c k x.length) = 0)}

def BPL : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.LogSpace ∧ ∃ (c k : ℕ), 0 < c ∧ ∀ x : Word,
      M.HaltsBy x (polynomialClock c k x.length) ∧
      (x ∈ A → (2 / 3 : ℚ) ≤ M.acceptanceProbability x
        (polynomialClock c k x.length)) ∧
      (x ∉ A → M.acceptanceProbability x (polynomialClock c k x.length) ≤ (1 / 3 : ℚ))}


theorem exact_logarithmic_space_derandomization :
    L = RL ∧ RL = BPL := by
  sorry

end ExactDerandomization

end OAI
