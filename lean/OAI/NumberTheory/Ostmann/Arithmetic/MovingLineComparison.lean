import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantPolynomial
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLineComparison

namespace OAI

/-! # Original-prior comparison for the moving-giant occurrence lines -/

namespace Ostmann
open scoped BigOperators Classical

/-- No degree or height of an occurrence line is assumed: both are inherited
from its actual path of reversals. The same applies to its nonzero row. -/
theorem moving_line_probability_comparison {A J : Type*} [Fintype A] [Fintype J]
    {n : ℕ} (value : A → ℤ) (hinj : Function.Injective value)
    (steps : J → List (PolynomialReversal (Fin n)))
    (v w : J → MvPolynomial (Fin n) ℤ) (i : J) (external : Bool)
    (k d : ℕ) (hlen : ∀ j, (steps j).length ≤ k)
    (hdegree : ∀ j, (∀ s ∈ steps j,
      s.v.totalDegree ≤ d ∧ s.w.totalDegree ≤ d ∧ s.u.totalDegree ≤ d) ∧
      (v j).totalDegree ≤ d ∧ (w j).totalDegree ≤ d)
    (K : ℝ) (hK : 1 ≤ K)
    (hheight : ∀ (x : Fin n → A) j,
      let φ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun a => (value (x a) : ℝ))
      (∀ s ∈ steps j, |φ s.v| ≤ K ∧ |φ s.w| ≤ K ∧ |φ s.u| ≤ K) ∧
        |φ (v j)| ≤ K ∧ |φ (w j)| ≤ K)
    (μ : Fin n → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ j a, μ j a ≤ α)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (ν : ℕ → ℝ) (hν : ∀ p ∈ P, 0 ≤ ν p) (hνmass : ∑ p ∈ P, ν p = 1)
    (β V : ℝ) (hβ : 0 ≤ β) (hV : 0 < V)
    (hνmax : ∀ p ∈ P, ν p ≤ β) (hsize : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hunits : ∀ (x : Fin n → A) (p : P) j,
      let φ := integerLineReduction value x p
      (∀ s ∈ steps j, φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0) ∧
        φ (v j) ≠ 0 ∧ φ (w j) ≠ 0)
    (F : (Fin n → A) → ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x p, ‖F x p‖ ≤ B) :
    let L := fun j => movingHistoryLine (steps j) (v j) (w j)
    ‖∑ x, ∑ p : P, ((productPrior μ x * ν p : ℝ) : ℂ) * F x p *
      ((sampledLineProbability value L external P hprime x p : ℂ) -
        (internalLineFlagWeight external p
          (fun s => arithmeticTestFlag (lineTestPolynomials L i s = 0)) : ℂ))‖ ≤
      2 * B * (2 + Fintype.card J) *
        ((2 * ((k + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * K) ^ (k + 1)) ^ 2) / V) * β) := by
  let L := fun j => movingHistoryLine (steps j) (v j) (w j)
  let H := (2 * K) ^ (k + 1)
  have hK0 : 0 ≤ K := by linarith
  have hH : 1 ≤ H := one_le_pow₀ (by linarith)
  have hlineDegree (j : J) : (L j).a.totalDegree ≤ (k + 1) * d ∧
      (L j).b.totalDegree ≤ (k + 1) * d := by
    have hj := movingHistoryLine_degree (steps j) (v j) (w j) d
      (hdegree j).1 (hdegree j).2.1 (hdegree j).2.2
    have hb : ((steps j).length + 1) * d ≤ (k + 1) * d :=
      Nat.mul_le_mul_right d (Nat.add_le_add_right (hlen j) 1)
    exact ⟨hj.1.trans hb, hj.2.trans hb⟩
  have hlineHeight (x : Fin n → A) (j : J) :
      let φ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun a => (value (x a) : ℝ))
      |φ (L j).a| ≤ H ∧ |φ (L j).b| ≤ H := by
    have hj := movingHistoryLine_value (steps j) (v j) (w j) _ K hK0
      (hheight x j).1 (hheight x j).2.1 (hheight x j).2.2
    have hb : (2 * K) ^ ((steps j).length + 1) ≤ H := by
      apply pow_le_pow_right₀ (by linarith : 1 ≤ 2 * K)
      exact Nat.add_le_add_right (hlen j) 1
    exact ⟨hj.1.trans hb, hj.2.trans hb⟩
  have htestHeight (s : Bool ⊕ J) (x : Fin n → A) :
      |(integerTestValue value (lineTestPolynomials L i s) x : ℝ)| ≤ 2 * H ^ 2 := by
    rw [integerTestValue_real_cast]
    exact lineTestPolynomials_value_le L i _ H hH (hlineHeight x) s
  have hHfull : 1 ≤ 2 * H ^ 2 := by nlinarith [sq_nonneg H]
  have hden (x : Fin n → A) (p : P) (j : J) :
      integerLineReduction value x p (L j).denominator ≠ 0 := by
    let : Fact (p.val.Prime) := ⟨hprime _ p.property⟩
    exact movingPolynomialAncestors_denominator (steps j) _
      (fun s hs => ((hunits x p j).1 s hs).2.2)
  have hrow (x : Fin n → A) (p : P) :
      integerLineReduction value x p (L i).a ≠ 0 ∨
        integerLineReduction value x p (L i).b ≠ 0 := by
    let : Fact (p.val.Prime) := ⟨hprime _ p.property⟩
    exact movingHistoryLine_nonzero (steps i) (v i) (w i) _
      (hunits x p i).1 (hunits x p i).2.1 (hunits x p i).2.2
  have hcomp := sampled_line_probability_comparison_le value hinj L i external μ hμ hmass
    α hα hmax P hprime ν hν hνmass β V (2 * H ^ 2) hβ hV hHfull hνmax hsize
    htestHeight hden hrow F B hB hF
  apply hcomp.trans
  have hterm (s : Bool ⊕ J) :
      ((lineTestPolynomials L i s).totalDegree : ℝ) * α +
          (Real.log (2 * H ^ 2) / V) * β ≤
        ((2 * ((k + 1) * d) : ℕ) : ℝ) * α + (Real.log (2 * H ^ 2) / V) * β := by
    have hd : ((lineTestPolynomials L i s).totalDegree : ℝ) ≤
        ((2 * ((k + 1) * d) : ℕ) : ℝ) := by
      exact_mod_cast lineTestPolynomials_degree_le L i ((k + 1) * d) hlineDegree s
    exact add_le_add (mul_le_mul_of_nonneg_right hd hα) le_rfl
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hterm s)
  apply (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hB)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat, H]
  ring

end Ostmann

end OAI
