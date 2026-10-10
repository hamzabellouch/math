import Mathlib.Combinatorics.Matroid.Closure
import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet.CandidateSpecification

open Finset

/-- Strict rounded-weight priority, including the fixed label tie-breaking rule. -/
def higher {n : ℕ} (f : Fin n) (a : Option ℤ) (e : Fin n) (b : Option ℤ) : Prop :=
  match a, b with
  | some i, some j => j < i ∨ j = i ∧ f < e
  | some _, none => True
  | _, _ => False

/-- Source candidate set: positive, unobserved, and not spanned by higher-priority
observed labels. The full candidate set is analytical, not given to the algorithm. -/
noncomputable def candidates {n : ℕ} (M : Matroid (Fin n))
    (a : Fin n → Option ℤ) (H : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e => a e ≠ none ∧ e ∉ H ∧
    e ∉ M.closure {f | f ∈ H ∧ higher f (a f) e (a e)}

/-- Positive priority-greedy on the entire ground set, characterized by failure
of the strictly higher-priority labels to span the current label. -/
noncomputable def greedy {n : ℕ} (M : Matroid (Fin n))
    (a : Fin n → Option ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e => a e ≠ none ∧
    e ∉ M.closure {f | higher f (a f) e (a e)}

/-- The source comparison independent set after sacrificing the fair mask. -/
noncomputable def survivors {n : ℕ} (M : Matroid (Fin n))
    (a : Fin n → Option ℤ) (H : Finset (Fin n)) : Finset (Fin n) :=
  greedy M a \ H

/-- The complete mathematical assertion of Lemma `lem:filter`, stated solely
using the concrete source definitions and the finite independent fair-mask law. -/
def CandidateMass : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → ∀ w : Weights n,
    let a := fun e => roundedLevel weightBase (w e)
    let u := fun e => roundedWeight weightBase (w e)
    (∀ H, M.Indep (survivors M a H : Set (Fin n)) ∧
      survivors M a H ⊆ candidates M a H) ∧
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ survivors M a H, u e) = optimum M u / 2 ∧
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ candidates M a H, u e) ≤ optimum M u

end MatroidProphet.CandidateSpecification

end OAI
