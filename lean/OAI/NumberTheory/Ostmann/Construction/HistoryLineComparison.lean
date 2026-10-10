import OAI.NumberTheory.Ostmann.Arithmetic.BoundedLineComparison

namespace OAI

/-! # Signed line comparison for the actual arithmetic histories

The nonzero rows, denominator conditions and polynomial degree/size budgets
are derived from the reversal data. The only pointwise inputs concern the
original frequency and slot polynomials and the bounded spectator amplitude.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem history_line_probability_comparison_le {A J : Type*} [Fintype A] [Fintype J]
    {n : ℕ} (value : A → ℤ) (hinj : Function.Injective value)
    (steps : J → List (PolynomialReversal (Fin n)))
    (v w : J → MvPolynomial (Fin n) ℤ) (i : J) (external : Bool)
    (k d : ℕ) (U : ℝ) (hU : 1 ≤ U) (hlen : ∀ j, (steps j).length ≤ k)
    (hdegree : ∀ j, ∀ s ∈ steps j,
      s.v.totalDegree ≤ d ∧ s.w.totalDegree ≤ d ∧ s.u.totalDegree ≤ d)
    (hcurdegree : ∀ j, (v j).totalDegree ≤ d ∧ (w j).totalDegree ≤ d)
    (hvalues : ∀ (x : Fin n → A) j, ∀ s ∈ steps j,
      let φ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun q => (value (x q) : ℝ));
      |φ s.v| ≤ U ∧ |φ s.w| ≤ U ∧ |φ s.u| ≤ U)
    (hcurvalues : ∀ (x : Fin n → A) j,
      let φ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun q => (value (x q) : ℝ));
      |φ (v j)| ≤ U ∧ |φ (w j)| ≤ U)
    (μ : Fin n → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ j a, μ j a ≤ α)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (ν : ℕ → ℝ) (hν : ∀ p ∈ P, 0 ≤ ν p) (hνmass : ∑ p ∈ P, ν p = 1)
    (β V : ℝ) (hβ : 0 ≤ β) (hV : 0 < V)
    (hνmax : ∀ p ∈ P, ν p ≤ β) (hsize : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hunit : ∀ (x : Fin n → A) (p : P) j, ∀ s ∈ steps j,
      integerLineReduction value x p s.v ≠ 0 ∧ integerLineReduction value x p s.w ≠ 0 ∧
        integerLineReduction value x p s.u ≠ 0)
    (hcurunit : ∀ (x : Fin n → A) (p : P) j,
      integerLineReduction value x p (v j) ≠ 0 ∧ integerLineReduction value x p (w j) ≠ 0)
    (F : (Fin n → A) → ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x p, ‖F x p‖ ≤ B) :
    let L := fun j => historyLine (steps j) (v j) (w j)
    ‖∑ x, ∑ p : P, ((productPrior μ x * ν p : ℝ) : ℂ) * F x p *
      ((sampledLineProbability value L external P hprime x p : ℂ) -
        (internalLineFlagWeight external p
          (fun s => arithmeticTestFlag (lineTestPolynomials L i s = 0)) : ℂ))‖ ≤
      2 * B * (Fintype.card J + 2 : ℝ) *
        (2 * ((k + 1) * d : ℕ) * α +
          (Real.log (2 * ((2 * U) ^ (k + 1)) ^ 2) / V) * β) := by
  let L := fun j => historyLine (steps j) (v j) (w j)
  have hdeg (j : J) : (L j).a.totalDegree ≤ (k + 1) * d ∧
      (L j).b.totalDegree ≤ (k + 1) * d :=
    historyLine_degree (steps j) (v j) (w j) k d (hlen j) (hdegree j)
      (hcurdegree j).1 (hcurdegree j).2
  have hcoeff (x : Fin n → A) (j : J) :
      |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun q => (value (x q) : ℝ)) (L j).a| ≤
        (2 * U) ^ (k + 1) ∧
      |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun q => (value (x q) : ℝ)) (L j).b| ≤
        (2 * U) ^ (k + 1) :=
    historyLine_value (steps j) (v j) (w j) _ k U hU (hlen j) (hvalues x j)
      (hcurvalues x j).1 (hcurvalues x j).2
  have hd (x : Fin n → A) (p : P) (j : J) :
      integerLineReduction value x p (L j).denominator ≠ 0 := by
    let _ : Fact p.val.Prime := ⟨hprime p p.property⟩
    exact historyLine_denominator_ne_zero (steps j) (v j) (w j)
      (integerLineReduction value x p) (fun s hs => (hunit x p j s hs).2.2)
  have hr (x : Fin n → A) (p : P) :
      integerLineReduction value x p (L i).a ≠ 0 ∨
        integerLineReduction value x p (L i).b ≠ 0 := by
    let _ : Fact p.val.Prime := ⟨hprime p p.property⟩
    exact historyLine_nonzero (steps i) (v i) (w i) (integerLineReduction value x p)
      (hunit x p i) (hcurunit x p i).1 (hcurunit x p i).2
  have hpower : 1 ≤ (2 * U) ^ (k + 1) := one_le_pow₀ (by linarith)
  exact bounded_line_probability_comparison_le value hinj L i external ((k + 1) * d)
    ((2 * U) ^ (k + 1)) hpower hdeg hcoeff μ hμ hmass α hα hmax P hprime
    ν hν hνmass β V hβ hV hνmax hsize hd hr F B hB hF

end Ostmann

end OAI
