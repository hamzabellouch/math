import OAI.NumberTheory.Ostmann.Arithmetic.RestoredHarmonicCells
import OAI.NumberTheory.Ostmann.Construction.OriginalPrimeCellExpectation

namespace OAI

/-! # Restoring the exceptional atoms inside the original prime expectation -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem BulkIntegrand.originalPrimePriors_mean {σ : Type*} [Fintype σ]
    (f : BulkIntegrand σ) (P : Finset ℕ) (S : σ → Finset ℕ)
    (hSP : ∀ i, S i ⊆ P) (hS : ∀ i, (∑ p ∈ S i, (p : ℝ)⁻¹) ≠ 0)
    (order : List σ) :
    (∑ x : σ → P, ((∏ i, primeSubsetPrior P (S i) (x i) : ℝ) : ℂ) *
      f.averages (fun i => primeSubsetLogMeasure (S i) (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹)
        order (primeArrayLogs x)) =
    ∑ x : σ → P, ((∏ i, primeSubsetPrior P (S i) (x i) : ℝ) : ℂ) * f (primeArrayLogs x) := by
  simp_rw [f.averages_originalPrimePriors P S hSP]
  exact finiteCoordinatePriors_preserves _
    (fun i => primeSubsetPrior_mass P (S i) (hSP i) (hS i)) order _

/-- The original normalization is unchanged when the omitted atoms are
restored. Only their harmonic mass enters the simultaneous error. -/
theorem BulkIntegrand.averages_primeRestoration {σ : Type*} [Fintype σ]
    (f : BulkIntegrand σ) (S D : σ → Finset ℕ)
    (hS : ∀ i, (∑ p ∈ S i \ D i, (p : ℝ)⁻¹) ≠ 0)
    (order : List σ) (horder : order.Nodup)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C)
    (hsmall : ∀ i ∈ order,
      (∑ p ∈ S i \ D i, (p : ℝ)⁻¹)⁻¹ * ∑ p ∈ S i ∩ D i, (p : ℝ)⁻¹ ≤ 1) :
    let Z := fun i => (∑ p ∈ S i \ D i, (p : ℝ)⁻¹)⁻¹
    ∀ x, ‖f.averages (fun i => primeSubsetLogMeasure (S i \ D i) (Z i)) order x -
      f.averages (fun i => primeSubsetLogMeasure (S i) (Z i)) order x‖ ≤
      2 ^ order.length * (order.map (fun i => Z i * C * ∑ p ∈ S i ∩ D i, (p : ℝ)⁻¹)).sum := by
  let Z := fun i => (∑ p ∈ S i \ D i, (p : ℝ)⁻¹)⁻¹
  have hZ (i : σ) : 0 ≤ Z i := by positivity
  apply f.averages_comparison _ _ order horder
  · intro i _
    rw [primeSubsetLogMeasure_normalized _ (hS i)]
    norm_num
  · intro i hi
    rw [primeSubsetLogMeasure_restored_mass _ _ (hS i)]
    linarith [hsmall i hi]
  · intro i _
    exact mul_nonneg (mul_nonneg (hZ i) hC) (Finset.sum_nonneg fun p _ => by positivity)
  · intro i _ x
    rw [norm_sub_rev]
    exact f.primeSubset_deletion_bound (S i) (D i) (Z i) C (hZ i) hf i x

/-- Apply the exceptional-atom restoration under the full original law,
including every nonbulk coordinate. -/
theorem BulkIntegrand.originalPrimePriors_restoration {σ : Type*} [Fintype σ]
    (f : BulkIntegrand σ) (P : Finset ℕ) (S D : σ → Finset ℕ)
    (hSP : ∀ i, S i \ D i ⊆ P)
    (hS : ∀ i, (∑ p ∈ S i \ D i, (p : ℝ)⁻¹) ≠ 0)
    (order : List σ) (horder : order.Nodup)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C)
    (hsmall : ∀ i ∈ order,
      (∑ p ∈ S i \ D i, (p : ℝ)⁻¹)⁻¹ * ∑ p ∈ S i ∩ D i, (p : ℝ)⁻¹ ≤ 1) :
    let Z := fun i => (∑ p ∈ S i \ D i, (p : ℝ)⁻¹)⁻¹
    ‖(∑ x : σ → P, ((∏ i, primeSubsetPrior P (S i \ D i) (x i) : ℝ) : ℂ) * f (primeArrayLogs x)) -
      ∑ x : σ → P, ((∏ i, primeSubsetPrior P (S i \ D i) (x i) : ℝ) : ℂ) *
        f.averages (fun i => primeSubsetLogMeasure (S i) (Z i)) order (primeArrayLogs x)‖ ≤
      2 ^ order.length * (order.map (fun i => Z i * C * ∑ p ∈ S i ∩ D i, (p : ℝ)⁻¹)).sum := by
  dsimp only
  rw [← f.originalPrimePriors_mean P (fun i => S i \ D i) hSP hS order]
  exact originalPrimePrior_mean_comparison P _ hSP hS _ _ _
    (fun x => f.averages_primeRestoration S D hS order horder C hC hf hsmall (primeArrayLogs x))

end Ostmann

end OAI
