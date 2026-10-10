import OAI.NumberTheory.Ostmann.Construction.FiniteCoordinatePrior
import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetMass

namespace OAI

/-! # The iterated logarithmic integrals are the original product-prior means -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def primeArrayLogs {σ : Type*} {P : Finset ℕ} (x : σ → P) : σ → ℝ :=
  fun i => Real.log (x i : ℕ)

theorem primeArrayLogs_update {σ : Type*} {P : Finset ℕ} (x : σ → P) (i : σ) (p : P) :
    primeArrayLogs (Function.update x i p) = Function.update (primeArrayLogs x) i (Real.log (p : ℕ)) := by
  funext j
  by_cases hji : j = i
  · subst j; simp [primeArrayLogs]
  · simp [primeArrayLogs, Function.update_of_ne hji]

theorem BulkIntegrand.averages_originalPrimePriors {σ : Type*} [Fintype σ]
    (f : BulkIntegrand σ) (P : Finset ℕ) (Q : σ → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (l : List σ) (x : σ → P) :
    f.averages (fun i => primeSubsetLogMeasure (Q i) (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹)
      l (primeArrayLogs x) =
      finiteCoordinatePriors (fun i => primeSubsetPrior P (Q i)) l (fun x => f (primeArrayLogs x)) x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    change (f.averages _ l).average _ i (primeArrayLogs x) = _
    rw [(f.averages _ l).average_originalPrimePrior P (Q i) (hQP i) i (primeArrayLogs x)]
    unfold finiteCoordinatePriors finiteCoordinatePrior
    apply Finset.sum_congr rfl
    intro p _
    rw [← primeArrayLogs_update, ih]

/-- With every original bulk coordinate present, the log integral is
exactly the finite product expectation used by the scheduled amplitude. -/
theorem BulkIntegrand.averages_all_originalPrimePriors {σ : Type*} [Fintype σ]
    (f : BulkIntegrand σ) (P : Finset ℕ) (Q : σ → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (l : List σ) (hl : ∀ i, i ∈ l) (x : σ → P) :
    f.averages (fun i => primeSubsetLogMeasure (Q i) (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹)
      l (primeArrayLogs x) =
      ∑ y : σ → P, ((∏ i, primeSubsetPrior P (Q i) (y i) : ℝ) : ℂ) * f (primeArrayLogs y) := by
  rw [f.averages_originalPrimePriors P Q hQP]
  exact finiteCoordinatePriors_all _ (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i))
    l hl _ x

end Ostmann

end OAI
