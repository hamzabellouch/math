import Mathlib

namespace OAI

namespace DirectedFeedback

/-- Unary self-delimiting natural numbers. Outputs are explicit, not succinct. -/
def natBits (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- The explicit framing used for an input and its NP certificate. -/
def pairBits (p : List Bool × List Bool) : List Bool :=
  natBits p.1.length ++ p.1 ++ p.2

/-- Finitely many stacks and control states are already part of `FinTM2`.
This additionally excludes infinite stack alphabets. -/
def FiniteAlphabet (M : Turing.FinTM2) : Prop := ∀ k, Finite (M.Γ k)

/-- Polynomially bounded certificates checked by an actual deterministic
finite-alphabet machine, on the explicitly encoded input/certificate pair. -/
structure NPVerifier where
  witnessBound : Polynomial ℕ
  verify : (List Bool × List Bool) → Bool
  computation : Turing.TM2ComputableInPolyTime pairBits (fun b : Bool => [b]) verify
  finiteAlphabet : FiniteAlphabet computation.tm

def NPVerifier.Accepts (V : NPVerifier) (input : List Bool) : Prop :=
  ∃ witness : List Bool, witness.length ≤ V.witnessBound.eval input.length ∧
    V.verify (input, witness) = true

/-- NP is defined independently of SAT or any hardness assertion. -/
def InNP (language : List Bool → Prop) : Prop :=
  ∃ V : NPVerifier, ∀ input, language input ↔ V.Accepts input

/-- Finite loopless digraph. Opposite arcs are permitted. Every arc is listed
explicitly. No symmetric closure or undirected-cycle convention is used. -/
structure Digraph where
  n : ℕ
  arcs : List (Fin n × Fin n)
  loopless : ∀ e ∈ arcs, e.1 ≠ e.2
  nodup : arcs.Nodup

namespace Digraph

/-- An actual simple directed cycle of positive length. A cyclic enumeration
of `r + 1` distinct vertices supplies every successive arc, including the
closing arc. A 2-cycle is allowed; looplessness rules out length 1. -/
def IsCycle (G : Digraph) {r : ℕ} (c : Fin (r + 1) → Fin G.n) : Prop :=
  Function.Injective c ∧ ∀ i, (c i, c (i + 1)) ∈ G.arcs

/-- A feedback set intersects EVERY actual directed cycle. -/
def Feedback (G : Digraph) (F : Finset (Fin G.n)) : Prop :=
  ∀ (r : ℕ) (c : Fin (r + 1) → Fin G.n), G.IsCycle c → ∃ i, c i ∈ F

/-- Minimum number of vertices of a feedback set. No weights or auxiliary
cost oracle appear in this definition. -/
noncomputable def dfvs (G : Digraph) : ℕ := by
  classical
  exact Nat.find (show ∃ k : ℕ, ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card = k from
    ⟨G.n, Finset.univ, by
      intro r c _
      exact ⟨0, Finset.mem_univ _⟩, by simp⟩)

/-- Full explicit vertex and arc serialization, including isolated vertices. -/
def bits (G : Digraph) : List Bool :=
  ([G.n] ++ List.range G.n ++ [G.arcs.length] ++
    G.arcs.flatMap (fun e => [e.1.val, e.2.val])).flatMap natBits

end Digraph

/-- Output includes a strictly positive integer threshold. -/
structure GapInstance where
  graph : Digraph
  k : ℕ
  k_pos : 0 < k

def GapInstance.bits (I : GapInstance) : List Bool :=
  natBits I.k ++ I.graph.bits

/-- A strict YES/NO gap reduction implemented by a finite-alphabet machine
with polynomial runtime in the raw input bit length. -/
structure GapReduction (A : ℝ) (language : List Bool → Prop) where
  construct : List Bool → GapInstance
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    GapInstance.bits construct
  finiteAlphabet : FiniteAlphabet computation.tm
  completeness : ∀ input, language input →
    (construct input).graph.dfvs ≤ (construct input).k
  soundness : ∀ input, ¬ language input →
    A * ((construct input).k : ℝ) < ((construct input).graph.dfvs : ℝ)

/-- Constant-factor directed feedback vertex set hardness for all NP languages. -/
def MainStatement : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∀ language : List Bool → Prop,
    InNP language → Nonempty (GapReduction A language)

end DirectedFeedback

theorem DirectedFeedback.main : DirectedFeedback.MainStatement := by
  sorry

end OAI
