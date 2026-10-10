import OAI.NumberTheory.Ostmann.Arithmetic.SmoothPrimeComparison
import OAI.NumberTheory.Ostmann.Characters.LogCutoffPolynomial
import OAI.NumberTheory.Ostmann.Characters.PolynomialWeightPair

namespace OAI

/-! # Retaining the original prime-cell cutoff in weighted comparison -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators ComplexConjugate

/-- The extra factor is the original top-prime cell cutoff, evaluated in the
same positive real coordinate as the history polynomials. -/
noncomputable def primeCutoffFactors {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (φ : ℝ → ℝ) (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    Fin (n + 1) → ClippedPolynomialFactor :=
  Fin.cons (logCutoffPolynomialFactor Polynomial.X φ G B D hB hD hφ hlip) F

theorem primeCutoffFactors_value {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (φ : ℝ → ℝ) (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (y : ℝ) :
    smoothPolynomialWeight (primeCutoffFactors F φ G B D hB hD hφ hlip) (Real.exp y) =
      (φ (y - G) : ℂ) * smoothPolynomialWeight F (Real.exp y) := by
  rw [smoothPolynomialWeight, primeCutoffFactors, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [logCutoffPolynomialFactor_value _ φ G B D hB hD hφ hlip hout]
  simp only [Polynomial.eval_X, positiveLogCutoff, Real.exp_pos, ite_true, Real.log_exp]
  rfl

theorem primeCutoffFactors_budget {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (φ : ℝ → ℝ) (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (primeCutoffFactors F φ G B D hB hD hφ hlip) =
      (2 * B + D * (Real.exp 2 - 1)) * smoothPolynomialBudget F := by
  rw [smoothPolynomialBudget, primeCutoffFactors, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [logCutoffPolynomialFactor_budget]
  rfl

theorem primeCutoffFactors_roots {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (φ : ℝ → ℝ) (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (S : Finset ℝ) (hS : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S) :
    ∀ i r, r ∈ (primeCutoffFactors F φ G B D hB hD hφ hlip i).polynomial.derivative.roots → r ∈ S := by
  intro i
  refine Fin.cases ?_ ?_ i
  · intro r hr
    simp [primeCutoffFactors, logCutoffPolynomialFactor] at hr
  · intro j r hr
    exact hS j r (by simpa only [primeCutoffFactors, Fin.cons_succ] using hr)

/-- The original harmonic prior's smooth cutoff is retained in the actual
prime sum and in the Page integral. Its cost is independent of the cell center. -/
theorem PublishedProgressionInput.cutoff_smooth_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (hcode : rootCellCode S (Real.exp u) = rootCellCode S (Real.exp v))
    (φ : ℝ → ℝ) (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    ‖complexPrimeInterval q a u v (fun y => (φ (y - G) : ℂ) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc u v, ((φ (y - G) : ℂ) * smoothPolynomialWeight F (Real.exp y)) *
        (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ((2 * B + D * (Real.exp 2 - 1)) * smoothPolynomialBudget F) *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
          Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) := by
  have h := P.smooth_prime_comparison hQ hq hqQ ha u v hu huv hshort
    (primeCutoffFactors F φ G B D hB hD hφ hlip) S
    (primeCutoffFactors_roots F φ G B D hB hD hφ hlip S hroots) hcode
  simp_rw [primeCutoffFactors_value F φ G B D hB hD hφ hlip hout,
    primeCutoffFactors_budget] at h
  exact h

end Ostmann

end OAI
