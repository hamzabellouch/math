import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialLargeValueSet
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialOperations

namespace OAI

/-! # Subexponential mass with a subexponential polynomial minor bound -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_large_polynomial_values
    (rem : RemezPolynomialInput) (n D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (p : ℝ → MvPolynomial (Fin n) ℝ) (hp : ∀ r, (p r).totalDegree ≤ D)
    (R c : ℝ → ℝ) (hR : ∀ r, 1 ≤ R r) (hc : ∀ r, 0 < c r)
    (hRupper : HasSubexponentialUpperBound R)
    (hclower : HasSubexponentialLowerBound c)
    (x₀ : ℝ → Fin n → ℝ) (hx₀ : ∀ r, x₀ r ∈ closedBall 0 (R r))
    (hvalue : ∀ r, c r ≤ |MvPolynomial.eval (x₀ r) (p r)|)
    (E : ℝ → Set (Fin n → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBound (fun r => (volume (E r)).toReal)) :
    ∃ (η : ℝ → ℝ) (K : ℝ → Set (Fin n → ℝ)),
      (∀ r, 0 < η r) ∧ HasSubexponentialLowerBound η ∧
      (∀ r, K r ⊆ E r) ∧ (∀ r, IsCompact (K r)) ∧
      (∀ r, 0 < (volume (K r)).toReal) ∧
      HasSubexponentialLowerBound (fun r => (volume (K r)).toReal) ∧
      ∀ r x, x ∈ K r → η r ≤ |MvPolynomial.eval x (p r)| := by
  classical
  obtain ⟨A, hA, hselect⟩ := exists_compact_large_polynomial_values rem n D hn hD
  let m := fun r => (volume (E r)).toReal
  let a := fun r => 2 * A * (1 + R r) ^ n / m r
  let η := fun r => (c r / 2) / a r ^ (n * D)
  have ha (r : ℝ) : 0 < a r := by
    have h := hR r
    have h' := hm r
    dsimp [a, m]
    positivity
  have hη (r : ℝ) : 0 < η r := div_pos (div_pos (hc r) (by norm_num)) (pow_pos (ha r) (n * D))
  have hs (r : ℝ) := hselect (p r) (hp r) (R r) (c r) (hR r) (hc r)
    (x₀ r) (hx₀ r) (hvalue r) (E r) (hE r) (hER r) (hm r)
  choose K hKE hK hmass hgood using hs
  have hR0 : ∀ᶠ r in atTop, 0 ≤ 1 + R r := Eventually.of_forall (fun r => by have := hR r; linarith)
  have haUpper : HasSubexponentialUpperBound a := by
    have hpowers := ((subexponential_upper_const 1).add hRupper).pow hR0 n
    have hnum := (subexponential_upper_const (2 * A)).mul hpowers
      (Eventually.of_forall (fun _ => by positivity))
    have hh := hnum.mul hmlower.inv (Eventually.of_forall (fun r => by
      have := hR r
      positivity))
    simpa only [a, m, div_eq_mul_inv] using hh
  have hηlower : HasSubexponentialLowerBound η :=
    (hclower.div (subexponential_upper_const 2) (Eventually.of_forall (by intro r; norm_num))).div
      (haUpper.pow (Eventually.of_forall (fun r => (ha r).le)) (n * D))
      (Eventually.of_forall (fun r => pow_pos (ha r) (n * D)))
  have hKlower : HasSubexponentialLowerBound (fun r => (volume (K r)).toReal) := by
    apply (hmlower.div (subexponential_upper_const 4) (Eventually.of_forall (by intro r; norm_num))).mono
    exact Eventually.of_forall (fun r => (hmass r).le)
  exact ⟨η, K, hη, hηlower, hKE, hK,
    fun r => (div_pos (hm r) (by norm_num : (0 : ℝ) < 4)).trans (hmass r),
    hKlower, hgood⟩

end PolycyclicRecognition

end

end OAI
