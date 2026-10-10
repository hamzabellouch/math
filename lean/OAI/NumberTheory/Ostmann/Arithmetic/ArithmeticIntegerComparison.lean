import OAI.NumberTheory.Ostmann.Characters.IntegerPolynomialBounds
import OAI.NumberTheory.Ostmann.Arithmetic.SymbolicLineComparison

namespace OAI

/-! # Signed arithmetic comparison for actual integer polynomial tests -/

namespace Ostmann

open scoped BigOperators

noncomputable def integerTestValue {A : Type*} {n : ℕ} (value : A → ℤ)
    (F : MvPolynomial (Fin n) ℤ) (x : Fin n → A) : ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun j => value (x j)) F

/-- The signed replacement estimate with all zero and divisor-count bridges
proved for the actual integer polynomial evaluations. -/
theorem integer_polynomial_symbolic_comparison_le {A I : Type*} [Fintype A] [Fintype I]
    {n : ℕ} (value : A → ℤ) (hinj : Function.Injective value)
    (F : I → MvPolynomial (Fin n) ℤ)
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ i a, μ i a ≤ α)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (ν : ℕ → ℝ) (hν : ∀ p ∈ P, 0 ≤ ν p) (hνmass : ∑ p ∈ P, ν p = 1)
    (β V H : ℝ) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hνmax : ∀ p ∈ P, ν p ≤ β) (hsize : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hvalue : ∀ i x, |(integerTestValue value (F i) x : ℝ)| ≤ H)
    (Ψ : (Fin n → A) → ℕ → (I → Bool) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hΨ : ∀ x p v, ‖Ψ x p v‖ ≤ B) :
    ‖∑ x, ∑ p ∈ P, ((productPrior μ x * ν p : ℝ) : ℂ) *
      (Ψ x p (fun i => arithmeticTestFlag (p ∣ (integerTestValue value (F i) x).natAbs)) -
        Ψ x p (fun i => arithmeticTestFlag (F i = 0)))‖ ≤
      2 * B * ∑ i, (((F i).totalDegree : ℝ) * α + (Real.log H / V) * β) := by
  classical
  let Q : I → MvPolynomial (Fin n) ℚ := fun i => MvPolynomial.map (Int.castRingHom ℚ) (F i)
  let N : I → (Fin n → A) → ℕ := fun i x => (integerTestValue value (F i) x).natAbs
  have hzero (i : I) (x : Fin n → A) : N i x = 0 ↔
      MvPolynomial.eval (fun j => (value (x j) : ℚ)) (Q i) = 0 := by
    dsimp only [N, Q, integerTestValue]
    rw [integerPolynomial_rational_eval]
    simp only [Int.natAbs_eq_zero, Int.cast_eq_zero]
  have hcard (i : I) (x : Fin n → A) (hx : N i x ≠ 0) :
      ((P.filter fun p => p ∣ N i x).card : ℝ) ≤ Real.log H / V := by
    have hz : integerTestValue value (F i) x ≠ 0 := by
      intro hz
      apply hx
      simp only [N, hz, Int.natAbs_zero]
    exact int_prime_divisor_card_le P _ hz hprime V H hV hsize (hvalue i x)
  have hk : 0 ≤ Real.log H / V := div_nonneg (Real.log_nonneg hH) hV.le
  have h := polynomial_symbolic_comparison_le (fun a => (value a : ℚ))
    (Int.cast_injective.comp hinj) Q μ hμ hmass α hα hmax P ν hν hνmass N hzero
    β (Real.log H / V) hβ hk hνmax hcard Ψ B hB hΨ
  have hflag (i : I) : arithmeticTestFlag (Q i = 0) = arithmeticTestFlag (F i = 0) :=
    congrArg arithmeticTestFlag (propext (integerPolynomial_rational_zero_iff (F i)))
  have hdegree (i : I) : (Q i).totalDegree = (F i).totalDegree :=
    integerPolynomial_rational_degree (F i)
  simpa only [hflag, hdegree, N] using h

end Ostmann

end OAI
