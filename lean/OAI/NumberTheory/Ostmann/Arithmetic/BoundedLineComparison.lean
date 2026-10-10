import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLineComparison
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticHistoryLines

namespace OAI

/-! # The quantitative line comparison from coefficient size and degree -/

namespace Ostmann

open scoped BigOperators Classical

theorem bounded_line_probability_comparison_le {A J : Type*} [Fintype A] [Fintype J]
    {n : ℕ} (value : A → ℤ) (hinj : Function.Injective value)
    (L : J → PolynomialGiantLine (Fin n)) (i : J) (external : Bool)
    (D : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hdegree : ∀ j, (L j).a.totalDegree ≤ D ∧ (L j).b.totalDegree ≤ D)
    (hcoeff : ∀ (x : Fin n → A) j,
      |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun k => (value (x k) : ℝ)) (L j).a| ≤ U ∧
      |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun k => (value (x k) : ℝ)) (L j).b| ≤ U)
    (μ : Fin n → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ j a, μ j a ≤ α)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (ν : ℕ → ℝ) (hν : ∀ p ∈ P, 0 ≤ ν p) (hνmass : ∑ p ∈ P, ν p = 1)
    (β V : ℝ) (hβ : 0 ≤ β) (hV : 0 < V)
    (hνmax : ∀ p ∈ P, ν p ≤ β) (hsize : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hd : ∀ (x : Fin n → A) (p : P) j, integerLineReduction value x p (L j).denominator ≠ 0)
    (hrow : ∀ (x : Fin n → A) (p : P),
      integerLineReduction value x p (L i).a ≠ 0 ∨ integerLineReduction value x p (L i).b ≠ 0)
    (F : (Fin n → A) → ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x p, ‖F x p‖ ≤ B) :
    ‖∑ x, ∑ p : P, ((productPrior μ x * ν p : ℝ) : ℂ) * F x p *
      ((sampledLineProbability value L external P hprime x p : ℂ) -
        (internalLineFlagWeight external p
          (fun s => arithmeticTestFlag (lineTestPolynomials L i s = 0)) : ℂ))‖ ≤
      2 * B * (Fintype.card J + 2 : ℝ) *
        (2 * D * α + (Real.log (2 * U ^ 2) / V) * β) := by
  have hU' : 1 ≤ 2 * U ^ 2 := by nlinarith
  have hv (s : Bool ⊕ J) (x : Fin n → A) :
      |(integerTestValue value (lineTestPolynomials L i s) x : ℝ)| ≤ 2 * U ^ 2 := by
    rw [integerTestValue_real_cast]
    exact lineTestPolynomials_value_le L i _ U hU (hcoeff x) s
  have h := sampled_line_probability_comparison_le value hinj L i external μ hμ hmass
    α hα hmax P hprime ν hν hνmass β V (2 * U ^ 2) hβ hV hU' hνmax hsize hv hd hrow F B hB hF
  refine h.trans ?_
  have hsum : (∑ s : Bool ⊕ J,
      (((lineTestPolynomials L i s).totalDegree : ℝ) * α + Real.log (2 * U ^ 2) / V * β)) ≤
      (Fintype.card J + 2 : ℝ) * (2 * D * α + Real.log (2 * U ^ 2) / V * β) := by
    calc
      _ ≤ ∑ _s : Bool ⊕ J, (2 * D * α + Real.log (2 * U ^ 2) / V * β) := by
        apply Finset.sum_le_sum
        intro s _
        have hd' : ((lineTestPolynomials L i s).totalDegree : ℝ) ≤ 2 * D := by
          exact_mod_cast lineTestPolynomials_degree_le L i D hdegree s
        have hm := mul_le_mul_of_nonneg_right hd' hα
        linarith
      _ = _ := by simp [Fintype.card_sum, add_comm]; ring
  calc
    _ ≤ 2 * B * ((Fintype.card J + 2 : ℝ) *
        (2 * D * α + Real.log (2 * U ^ 2) / V * β)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
