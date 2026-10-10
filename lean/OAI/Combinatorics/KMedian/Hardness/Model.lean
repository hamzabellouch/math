import Mathlib
import OAI.Combinatorics.KMedian.Model

namespace OAI

namespace MetricKMedian
namespace Complexity
/-- Polynomial-time computation with every physical work alphabet finite. -/
def FinitePolyTime {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) : Prop :=
  ∃ p : Turing.TM2ComputableInPolyTime ea eb f,
    ∀ k : p.tm.K, Finite (p.tm.Γ k)

abbrev Word := List Bool
abbrev Language := Set Word

def encodeBit (b : Bool) : Word := [b]

def encodePair (x : Word × Word) : Word :=
  encodeNat x.1.length ++ x.1 ++ x.2

def P : Set Language := {L | ∃ decideL : Word → Bool,
  FinitePolyTime id encodeBit decideL ∧ ∀ x, decideL x = true ↔ x ∈ L}

def NP : Set Language := {L | ∃ (verify : Word × Word → Bool) (p : Polynomial ℕ),
  FinitePolyTime encodePair encodeBit verify ∧
  ∀ x, x ∈ L ↔ ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x, w) = true}

/-- Separation of deterministic polynomial time from finite-verifier nondeterministic polynomial time. -/
def PNeNP : Prop := P ≠ NP

end Complexity
/-- An actual nonempty feasible facility set, encoded by its membership mask. -/
def FactorCorrect (α : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ α * optimum I

/-- Deterministic polynomial-time approximation factors for arbitrary specified clients and facilities. -/
def approximationFactors : Set ℝ := {α | ∃ algorithm : Instance → List Bool,
  Complexity.FinitePolyTime encodeInstance id algorithm ∧
  ∀ I, FactorCorrect α I (algorithm I)}

end MetricKMedian

end OAI
