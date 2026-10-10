import Mathlib

namespace OAI

namespace MeanPayoff
structure Game where
  n : ℕ
  positive : 0 < n
  m : ℕ
  tail : Fin m → Fin n
  head : Fin m → Fin n
  maxOwner : Fin n → Bool
  weight : Fin m → ℤ
  total : ∀ v : Fin n, ∃ e : Fin m, tail e = v

def Strategy (G : Game) :=
  List (Fin G.m) → (v : Fin G.n) → {e : Fin G.m // G.tail e = v}

def move (G : Game) (σ τ : Strategy G) (v : Fin G.n)
    (history : List (Fin G.m)) : Fin G.m :=
  if G.maxOwner v then (σ history v).val else (τ history v).val

def position (G : Game) (σ τ : Strategy G) (start : Fin G.n) :
    ℕ → Fin G.n × List (Fin G.m)
  | 0 => (start, [])
  | t + 1 =>
    let p := position G σ τ start t
    let e := move G σ τ p.1 p.2
    (G.head e, p.2 ++ [e])

def play (G : Game) (σ τ : Strategy G) (start : Fin G.n) (t : ℕ) : Fin G.m :=
  let p := position G σ τ start t
  move G σ τ p.1 p.2

noncomputable def meanPayoff (G : Game) (π : ℕ → Fin G.m) : ℝ :=
  Filter.liminf (fun T : ℕ =>
    (∑ j ∈ Finset.range T, (G.weight (π j) : ℝ)) / (T : ℝ)) Filter.atTop

def Winning (G : Game) (v : Fin G.n) : Prop :=
  ∃ σ : Strategy G, ∀ τ : Strategy G, 0 ≤ meanPayoff G (play G σ τ v)

def encodeNat (n : ℕ) : List Bool :=
  let bits := Nat.bits (n + 1)
  List.replicate bits.length true ++ [false] ++ bits

def encodeInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encodeNat z.natAbs

def input (G : Game) : List Bool :=
  encodeNat G.n ++ encodeNat G.m ++ List.ofFn G.maxOwner ++
    (List.ofFn (fun e : Fin G.m =>
      encodeNat ((G.tail e).val + 1) ++ encodeNat ((G.head e).val + 1) ++
        encodeInt (G.weight e))).flatten

abbrev Symbol := Option Bool

inductive Direction where
  | left | stay | right
  deriving DecidableEq

def Direction.offset : Direction → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure Action (q : ℕ) where
  next : Fin q
  write : Fin 3 → Symbol
  shift : Fin 3 → Direction

structure Machine where
  states : ℕ
  start : Fin states
  transition : Fin states → (Fin 3 → Symbol) → Bool → Option (Action states)

structure Configuration (M : Machine) where
  control : Option (Fin M.states)
  head : Fin 3 → ℤ
  tape : Fin 3 → ℤ → Symbol

def initial (M : Machine) (code : List Bool) : Configuration M where
  control := some M.start
  head := fun _ => 0
  tape := fun k j => if k = 0 ∧ 0 ≤ j then code[j.toNat]? else none

def step (M : Machine) (c : Configuration M) (bit : Bool) : Configuration M :=
  match c.control with
  | none => c
  | some s =>
    match M.transition s (fun k => c.tape k (c.head k)) bit with
    | none => { c with control := none }
    | some a =>
      { control := some a.next
        head := fun k => c.head k + (a.shift k).offset
        tape := fun k => Function.update (c.tape k) (c.head k) (a.write k) }

def run (M : Machine) (code : List Bool) (random : ℕ → Bool) : ℕ → Configuration M
  | 0 => initial M code
  | t + 1 => step M (run M code random t) (random t)

def padBits {T : ℕ} (bits : Fin T → Bool) (j : ℕ) : Bool :=
  if h : j < T then bits ⟨j, h⟩ else false

def result (M : Machine) (G : Game) (T : ℕ) (bits : Fin T → Bool) : Configuration M :=
  run M (input G) (padBits bits) T

def CorrectOutput (G : Game) {M : Machine} (c : Configuration M) : Prop :=
  c.control = none ∧
  (∀ v : Fin G.n, c.tape 2 (v.val : ℤ) = some true ↔ Winning G v) ∧
  (∀ v : Fin G.n, c.tape 2 (v.val : ℤ) = some false ↔ ¬ Winning G v) ∧
  ∀ j : ℤ, (j < 0 ∨ (G.n : ℤ) ≤ j) → c.tape 2 j = none

noncomputable def MainClaim : Prop := by
  classical
  exact ∃ M : Machine, ∃ C : ℝ, 0 < C ∧ ∀ G : Game, ∃ T : ℕ,
    (T : ℝ) ≤ (2 : ℝ) ^ (C * (Real.logb 2 ((input G).length + 2)) ^ 2) ∧
    (∀ bits : Fin T → Bool, (result M G T bits).control = none) ∧
    7 * 2 ^ T ≤ 8 * (Finset.univ.filter
      (fun bits : Fin T → Bool => CorrectOutput G (result M G T bits))).card

end MeanPayoff

theorem randomized_quasipolynomial_mean_payoff : MeanPayoff.MainClaim := by
  sorry

end OAI
