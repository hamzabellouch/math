import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateApproximation
import OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting

namespace OAI

/-! Recursive use of the sampled gate polynomial. Errors in the child
polynomials are charged by a finite union bound, in addition to the new
gate's sampling error. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem exists_composed_and_approximation {n : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (k s d : ℕ)
    (b : Fin k → BooleanCube n → Bool) (P : Fin k → BooleanCube n → ℝ)
    (hP : ∀ i, WalshDegreeLE (P i) d) (δ : Fin k → ℝ)
    (hδ : ∀ i, ν.probability (fun y => P i y ≠ if b i y then 1 else 0) ≤ δ i) :
    ∃ Q : BooleanCube n → ℝ,
      WalshDegreeLE Q (d * s * (Nat.log 2 k + 3)) ∧
      ν.probability (fun y => Q y ≠ boolAndValue (fun i => b i y)) ≤
        (7 / 8 : ℝ) ^ s + ∑ i, δ i := by
  obtain ⟨x, hx⟩ := exists_and_gate_approximation ν k s (fun y i => b i y)
  let Q := fun y => sampledAndPolynomial x (fun i => P i y)
  refine ⟨Q, sampledAndPolynomial_degree x P d hP, ?_⟩
  let E : Option (Fin k) → BooleanCube n → Prop
    | none => fun y => sampledAndPolynomial x (fun i => if b i y then 1 else 0) ≠
        boolAndValue (fun i => b i y)
    | some i => fun y => P i y ≠ if b i y then 1 else 0
  have hcover : ∀ y, Q y ≠ boolAndValue (fun i => b i y) → ∃ i, E i y := by
    intro y hy
    by_cases hc : ∃ i, P i y ≠ if b i y then 1 else 0
    · obtain ⟨i, hi⟩ := hc
      exact ⟨some i, hi⟩
    · have heq : (fun i => P i y) = fun i => if b i y then 1 else 0 := by
        funext i
        by_contra hi
        exact hc ⟨i, hi⟩
      refine ⟨none, ?_⟩
      change sampledAndPolynomial x (fun i => if b i y then 1 else 0) ≠ _
      simpa only [Q, heq] using hy
  calc
    ν.probability (fun y => Q y ≠ boolAndValue (fun i => b i y)) ≤
        ν.probability (fun y => ∃ i, E i y) := ν.probability_mono hcover
    _ ≤ ∑ i : Option (Fin k), ν.probability (E i) := ν.probability_exists_le E
    _ = ν.probability (E none) + ∑ i : Fin k, ν.probability (E (some i)) := by
      simp only [Fintype.sum_option]
    _ ≤ (7 / 8 : ℝ) ^ s + ∑ i, δ i :=
      add_le_add hx (sum_le_sum (fun i _ => hδ i))

end TwoPointCorrelations

end OAI
