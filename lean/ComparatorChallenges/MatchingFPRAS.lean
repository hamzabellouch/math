import Mathlib

namespace OAI

namespace MatchingFPRAS

/-- Each unordered edge is represented once, by increasing endpoints. -/
structure GraphInput where
  n : ℕ
  edges : Finset (Fin n × Fin n)
  increasing : ∀ e ∈ edges, e.1 < e.2

/-- Exactly one selected edge is incident to every vertex. -/
def Perfect (G : GraphInput) (M : Finset (Fin G.n × Fin G.n)) : Prop :=
  M ⊆ G.edges ∧ ∀ v : Fin G.n, ∃! e, e ∈ M ∧ (e.1 = v ∨ e.2 = v)

noncomputable def perfectMatchings (G : GraphInput) : Finset (Finset (Fin G.n × Fin G.n)) :=
  by
    classical
    exact G.edges.powerset.filter (Perfect G)

/-- The exact unweighted count, including the empty graph. -/
noncomputable def Z (G : GraphInput) : ℕ := (perfectMatchings G).card

abbrev Symbol := Fin 8

/-- Binary numeral followed by a delimiter. Tape blank is 0; bits use 1 and 2. -/
def encodeNat (n : ℕ) : List Symbol :=
  (Nat.bits n).map (fun b => if b then 2 else 1) ++ [3]

def encodeInt (z : ℤ) : List Symbol :=
  (if z < 0 then [5] else [4]) ++ encodeNat z.natAbs

/-- A rational encoded by its reduced numerator and positive denominator. -/
def encodeRat (q : ℚ) : List Symbol := encodeInt q.num ++ encodeNat q.den

/-- Explicit sparse graph encoding, then the two rational parameters. -/
def encodeInput (G : GraphInput) (ε δ : ℚ) : List Symbol :=
  encodeNat G.n ++ encodeNat G.edges.card ++
    (((G.edges.map toLex.toEmbedding).sort (· ≤ ·)).flatMap fun e =>
      encodeNat (ofLex e).1.val ++ encodeNat (ofLex e).2.val) ++
    encodeRat ε ++ encodeRat δ

/-- A uniform randomized Post-Turing machine: a single finite transition table. -/
structure RandomMachine where
  states : ℕ
  transition : Fin (states + 1) → Symbol → Bool →
    Option (Fin (states + 1) × Turing.TM0.Stmt Symbol)

structure Configuration (A : RandomMachine) where
  state : Option (Fin (A.states + 1))
  tape : Turing.Tape Symbol

/-- A halted configuration is absorbing. Each nonhalting tick is exactly one
write or one move, or the detection of halt. -/
def tick (A : RandomMachine) (c : Configuration A) (bit : Bool) : Configuration A :=
  match c.state with
  | none => c
  | some s => match A.transition s c.tape.head bit with
    | none => ⟨none, c.tape⟩
    | some (s', action) =>
      ⟨some s', match action with
        | .move d => c.tape.move d
        | .write a => c.tape.write a⟩

def initial (A : RandomMachine) (input : List Symbol) : Configuration A :=
  ⟨some 0, Turing.Tape.mk₁ input⟩

/-- Bounded execution on a finite prefix of the random tape. -/
def run (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) : Configuration A :=
  (List.ofFn bits).foldl (tick A) (initial A input)

def Outputs (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) (q : ℚ) : Prop :=
  (run A input bits).state = none ∧
    (run A input bits).tape.right₀ = Turing.ListBlank.mk (encodeRat q)

/-- A fixed-degree polynomial in input bits, ε⁻¹, and log δ⁻¹.
Natural ceilings and binary ceiling-log change this bound only by constants. -/
def timeBound (C d : ℕ) (G : GraphInput) (ε δ : ℚ) : ℕ :=
  C * ((encodeInput G ε δ).length + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ d

noncomputable def goodTapes (A : RandomMachine) (G : GraphInput) (ε δ : ℚ)
    (t : ℕ) : Finset (Fin t → Bool) := by
  classical
  exact Finset.univ.filter fun bits => ∃ q : ℚ,
    Outputs A (encodeInput G ε δ) bits q ∧
    (1 - ε) * (Z G : ℚ) ≤ q ∧ q ≤ (1 + ε) * (Z G : ℚ)

/-- A uniform approximation scheme using independent fair bits. All tapes halt
within the fixed polynomial bound and return a nonnegative rational.
A zero count always produces encoded zero. -/
def MainStatement : Prop :=
  ∃ (A : RandomMachine) (C d : ℕ), 0 < C ∧
    ∀ (G : GraphInput) (ε δ : ℚ), 0 < ε → ε < 1 → 0 < δ → δ < 1 / 2 →
      let t := timeBound C d G ε δ
      (∀ bits : Fin t → Bool, ∃ q : ℚ, 0 ≤ q ∧ Outputs A (encodeInput G ε δ) bits q) ∧
      (Z G = 0 → ∀ bits : Fin t → Bool, Outputs A (encodeInput G ε δ) bits 0) ∧
      ((goodTapes A G ε δ t).card : ℚ) / (2 : ℚ) ^ t ≥ 1 - δ


/-- A fully polynomial randomized approximation scheme for perfect matchings
in every finite simple undirected graph. -/
theorem thm_main : MainStatement := by
  sorry

end MatchingFPRAS

end OAI
