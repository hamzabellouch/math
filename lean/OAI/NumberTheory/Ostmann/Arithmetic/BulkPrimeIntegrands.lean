import OAI.NumberTheory.Ostmann.Arithmetic.BulkIntegrands
import OAI.NumberTheory.Ostmann.Construction.PrimeLogCellMeasure

namespace OAI

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem BulkIntegrand.average_prime {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (q a : ℕ) (u v : ℝ) (i : σ) (x : σ → ℝ) :
    f.average (primeLogCellMeasure q a u v) i x =
      ∑ p ∈ primeLogCellSet q a u v,
        f (Function.update x i (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) := by
  change (∫ t, f (Function.update x i t) ∂primeLogCellMeasure q a u v) = _
  unfold primeLogCellMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul, mul_comm]
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  · intro p _
    exact f.slice_integrable _ i x

theorem BulkIntegrand.average_prime_eq_interval {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (q a : ℕ) (u v : ℝ) (i : σ) (x : σ → ℝ) (H : ℝ → ℂ)
    (hH : ∀ y, f (Function.update x i y) = H y) :
    f.average (primeLogCellMeasure q a u v) i x = complexPrimeInterval q a u v H := by
  rw [f.average_prime]
  unfold primeLogCellSet complexPrimeInterval
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime ∧ Nat.ModEq q p a
  · rw [ite_eq_left hp, ite_eq_left hp, hH]
  · rw [ite_eq_right hp, ite_eq_right hp]

theorem BulkIntegrand.average_page {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (P : PublishedProgressionInput) (Q q a : ℕ) (u v : ℝ) (hu : 0 < u)
    (i : σ) (x : σ → ℝ) :
    letI := finite_primeGiantMeasure P Q q a u v hu
    f.average (primeGiantMeasure P Q q a u v) i x =
      ∫ y in Set.Ioc u v, f (Function.update x i y) * (selectedPrimeLogDensity P Q q a y : ℂ) := by
  exact primeGiantMeasure_integral P Q q a u v hu.le _

end Ostmann

end OAI
