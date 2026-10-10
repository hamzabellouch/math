import OAI.NumberTheory.TwoPoint.Circuits.CircuitOrApproximation

namespace OAI

/-! The recursive polynomial approximation in Braverman's Lemma 8, with
an explicit degree and an error union bound over the circuit tree. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem AC0Circuit.exists_polynomial_approximation {n : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (c : AC0Circuit n) :
    ∃ P : BooleanCube n → ℝ, WalshDegreeLE P (c.approximationDegree s) ∧
      ν.probability (fun x => P x ≠ c.indicator x) ≤
        (c.size : ℝ) * (7 / 8 : ℝ) ^ s := by
  induction c with
  | literal i b =>
    refine ⟨(AC0Circuit.literal i b).indicator, literal_indicator_degree i b, ?_⟩
    simp only [ne_eq, not_true_eq_false, FiniteLaw.probability, FiniteLaw.average,
      ite_false, mul_zero, sum_const_zero]
    positivity
  | @andGate k children ih =>
    choose P hP he using ih
    let d := univ.sup (fun i => (children i).approximationDegree s)
    have hdeg i : WalshDegreeLE (P i) d :=
      (hP i).mono (le_sup (f := fun i => (children i).approximationDegree s) (mem_univ i))
    obtain ⟨Q, hQ, herror⟩ := exists_composed_and_approximation ν k s d
      (fun i => (children i).eval) P hdeg
      (fun i => ((children i).size : ℝ) * (7 / 8 : ℝ) ^ s) he
    refine ⟨Q, hQ, ?_⟩
    have hid (x : BooleanCube n) : (AC0Circuit.andGate children).indicator x =
        boolAndValue (fun i => (children i).eval x) := by
      simp only [AC0Circuit.indicator, AC0Circuit.eval, boolAndValue, decide_eq_true_eq]
    simp only [hid]
    convert herror using 1
    simp only [AC0Circuit.size, Nat.cast_add, Nat.cast_one, Nat.cast_sum, add_mul,
      one_mul, sum_mul]
  | @orGate k children ih =>
    choose P hP he using ih
    let d := univ.sup (fun i => (children i).approximationDegree s)
    have hdeg i : WalshDegreeLE (P i) d :=
      (hP i).mono (le_sup (f := fun i => (children i).approximationDegree s) (mem_univ i))
    obtain ⟨Q, hQ, herror⟩ := exists_composed_or_approximation ν k s d
      (fun i => (children i).eval) P hdeg
      (fun i => ((children i).size : ℝ) * (7 / 8 : ℝ) ^ s) he
    refine ⟨Q, hQ, ?_⟩
    have hid (x : BooleanCube n) : (AC0Circuit.orGate children).indicator x =
        boolOrValue (fun i => (children i).eval x) := by
      simp only [AC0Circuit.indicator, AC0Circuit.eval, boolOrValue, decide_eq_true_eq]
    simp only [hid]
    convert herror using 1
    simp only [AC0Circuit.size, Nat.cast_add, Nat.cast_one, Nat.cast_sum, add_mul,
      one_mul, sum_mul]

end TwoPointCorrelations

end OAI
