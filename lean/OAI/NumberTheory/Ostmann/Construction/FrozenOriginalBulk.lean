import OAI.NumberTheory.Ostmann.Construction.FrozenNonbulkPrior
import OAI.NumberTheory.Ostmann.Construction.OriginalBulkExpectation
import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogContinuity

namespace OAI

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem bulkLogValues_base_update {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (i : σ) (hi : i ∈ S) (a : ℝ) (y : σ → ℝ) :
    bulkLogValues (Function.update base i a) S y = bulkLogValues base S y := by
  funext j
  by_cases hj : j ∈ S
  · simp only [bulkLogValues, hj, ite_true]
  · have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
    simp only [bulkLogValues, hj, ite_false, Function.update_of_ne hji]

theorem bulkLogValues_prime_update {σ : Type*} {P : Finset ℕ} (x : σ → P) (S : Finset σ)
    (i : σ) (hi : i ∈ S) (a : P) (y : σ → ℝ) :
    bulkLogValues (fun j => ((Function.update x i a j : P) : ℕ)) S y =
      bulkLogValues (fun j => (x j : ℕ)) S y := by
  funext j
  by_cases hj : j ∈ S
  · simp only [bulkLogValues, hj, ite_true]
  · have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
    simp only [bulkLogValues, hj, ite_false, Function.update_of_ne hji]

/-- The full original mean is unchanged by bulk resampling even when the
real kernel is built from the original nonbulk sample. This is the form needed
for the sharp moving-history kernels. -/
theorem frozen_original_bulk_mean {σ : Type*} [Fintype σ]
    (P : Finset ℕ) (Q : σ → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (order : List σ) (F : (σ → ℝ) → ℂ) (f : (σ → P) → BulkIntegrand σ)
    (hf : ∀ x y, f x y = F (bulkLogValues (fun i => (x i : ℕ)) order.toFinset y)) :
    (∑ x : σ → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (f x).averages (fun i => primeSubsetLogMeasure (Q i) (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹)
        order (primeArrayLogs x)) =
    ∑ x : σ → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * f x (primeArrayLogs x) := by
  simp_rw [BulkIntegrand.averages_originalPrimePriors _ P Q hQP]
  apply finite_prior_frozen_mean _ (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i))
  intro i hi x a y
  rw [hf, hf, bulkLogValues_prime_update x order.toFinset i (List.mem_toFinset.mpr hi)]

theorem frozen_original_bulk_value {σ : Type*} [Fintype σ]
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (S : Finset σ)
    (F : (σ → ℝ) → ℂ) (f : (σ → P) → BulkIntegrand σ)
    (hf : ∀ x y, f x y = F (bulkLogValues (fun i => (x i : ℕ)) S y)) (x : σ → P) :
    f x (primeArrayLogs x) = F (fun i => (x i : ℕ)) := by
  rw [hf]
  change F (bulkLogValues (fun i => (x i : ℕ)) S (fun i => Real.log (x i : ℕ))) = _
  rw [bulkLogValues_nat (fun i => (x i : ℕ)) (fun i => (x i : ℕ)) S
    (fun i _ => hP (x i) (x i).property)]
  congr 1
  funext i
  split_ifs <;> rfl

end Ostmann

end OAI
