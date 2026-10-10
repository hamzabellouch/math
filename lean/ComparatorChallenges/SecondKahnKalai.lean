import Mathlib.Data.Fintype.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

noncomputable section

universe u

namespace LeanBlast.SecondKahnKalai

def bernoulliWeight {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (W : Finset X) : ℝ :=
  ∏ x, if x ∈ W then p else 1 - p

def bernoulliExpectation {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (f : Finset X → ℝ) : ℝ :=
  ∑ W, bernoulliWeight p W * f W

def bernoulliProbability {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (P : Finset X → Prop) : ℝ := by
  classical
  exact ∑ W, if P W then bernoulliWeight p W else 0

/-- The unordered non-loop edges of the complete graph on `n` vertices. -/
abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- A set of edges, interpreted as an ordinary graph on all `n` vertices. -/
def graphOfEdges {n : ℕ} (W : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Subtype.val '' (W : Set (Edge n)))

/-- The number of unordered edges, each counted once. -/
def edgeCount {V : Type u} (H : SimpleGraph V) : ℕ := Nat.card H.edgeSet

/-- Expected number of actual unlabelled non-induced copies in `G(n,p)`. -/
def expectedCopies {V : Type u} (n : ℕ) (p : ℝ) (H : SimpleGraph V) : ℝ :=
  bernoulliExpectation p (fun W : Finset (Edge n) =>
    ((graphOfEdges W).copyCount H : ℝ))

/-- Probability that `G(n,p)` contains at least one non-induced copy. -/
def containmentProbability {V : Type u} (n : ℕ) (p : ℝ)
    (H : SimpleGraph V) : ℝ :=
  bernoulliProbability p (fun W : Finset (Edge n) =>
    0 < (graphOfEdges W).copyCount H)

def criticalThreshold {V : Type u} (n : ℕ) (H : SimpleGraph V) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ (1 / 2 : ℝ) ≤ containmentProbability n p H}

def expectationThreshold {V : Type u} (n : ℕ) (H : SimpleGraph V) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧
    ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe}

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def SecondKahnKalaiBounds {V : Type u} (n : ℕ) (H : SimpleGraph V) : Prop :=
  criticalThreshold n H ≤
      min 1 (2048 * Real.exp 50 * expectationThreshold n H *
        (1 + logTwo (edgeCount H : ℝ))) ∧
    criticalThreshold n H ≤
      6144 * Real.exp 50 * expectationThreshold n H * logTwo (n : ℝ)

theorem secondKahnKalaiBounds (n : ℕ) (V : Type u) [Fintype V]
    (H : SimpleGraph V) (hn : 2 ≤ n) (hcard : Fintype.card V ≤ n)
    (hedge : 1 ≤ edgeCount H) : SecondKahnKalaiBounds n H := by
  sorry

end LeanBlast.SecondKahnKalai

end

end OAI
