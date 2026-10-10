import OAI.NumberTheory.Ostmann.Construction.OriginalBulkExpectation

namespace OAI

/-! # Reassembly of the bulk comparison under the original prime law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem BulkIntegrand.averages_originalPrimeCells {σ C : Type*} [Fintype σ] [Fintype C]
    (f : BulkIntegrand σ) (P : Finset ℕ) (q : σ → ℕ) (a : σ → C → ℕ)
    (u v : σ → C → ℝ)
    (hSP : ∀ i, primeCellSupport (q i) (a i) (u i) (v i) ⊆ P)
    (hsep : ∀ i c d, c ≠ d →
      ¬Nat.ModEq (q i) (a i c) (a i d) ∨ v i c ≤ u i d ∨ v i d ≤ u i c)
    (l : List σ) (x : σ → P) :
    f.averages (fun i => bulkCellMixture
      (∑ p ∈ primeCellSupport (q i) (a i) (u i) (v i), (p : ℝ)⁻¹)⁻¹
      (fun c => primeLogCellMeasure (q i) (a i c) (u i c) (v i c))) l (primeArrayLogs x) =
      finiteCoordinatePriors
        (fun i => primeSubsetPrior P (primeCellSupport (q i) (a i) (u i) (v i)))
        l (fun x => f (primeArrayLogs x)) x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    change (f.averages _ l).average _ i (primeArrayLogs x) = _
    rw [(f.averages _ l).average_originalPrimeCells P (q i) (a i) (u i) (v i)
      (hSP i) (hsep i) i (primeArrayLogs x)]
    unfold finiteCoordinatePriors finiteCoordinatePrior
    apply Finset.sum_congr rfl
    intro p _
    rw [← primeArrayLogs_update, ih]

/-- Replacing any selected bulk coordinates by their original cell mixtures
preserves the full original product expectation, including all other roles. -/
theorem BulkIntegrand.originalPrimeCells_mean {σ C : Type*} [Fintype σ] [Fintype C]
    (f : BulkIntegrand σ) (P : Finset ℕ) (q : σ → ℕ) (a : σ → C → ℕ)
    (u v : σ → C → ℝ)
    (hSP : ∀ i, primeCellSupport (q i) (a i) (u i) (v i) ⊆ P)
    (hsep : ∀ i c d, c ≠ d →
      ¬Nat.ModEq (q i) (a i c) (a i d) ∨ v i c ≤ u i d ∨ v i d ≤ u i c)
    (hS : ∀ i, (∑ p ∈ primeCellSupport (q i) (a i) (u i) (v i), (p : ℝ)⁻¹) ≠ 0)
    (l : List σ) :
    let S := fun i => primeCellSupport (q i) (a i) (u i) (v i)
    (∑ x : σ → P, ((∏ i, primeSubsetPrior P (S i) (x i) : ℝ) : ℂ) *
      f.averages (fun i => bulkCellMixture (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹
        (fun c => primeLogCellMeasure (q i) (a i c) (u i c) (v i c))) l (primeArrayLogs x)) =
    ∑ x : σ → P, ((∏ i, primeSubsetPrior P (S i) (x i) : ℝ) : ℂ) * f (primeArrayLogs x) := by
  dsimp only
  simp_rw [f.averages_originalPrimeCells P q a u v hSP hsep]
  exact finiteCoordinatePriors_preserves _
    (fun i => primeSubsetPrior_mass P _ (hSP i) (hS i)) l _

/-- A pointwise joint replacement estimate survives the original normalized
prime expectation with its error unchanged. -/
theorem originalPrimePrior_mean_comparison {σ : Type*} [Fintype σ]
    (P : Finset ℕ) (Q : σ → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (F G : (σ → P) → ℂ) (ε : ℝ) (herr : ∀ x, ‖F x - G x‖ ≤ ε) :
    ‖(∑ x : σ → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * F x) -
      ∑ x : σ → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * G x‖ ≤ ε := by
  let μ := fun x : σ → P => ∏ i, primeSubsetPrior P (Q i) (x i)
  have hμ (x : σ → P) : 0 ≤ μ x :=
    Finset.prod_nonneg fun i _ => primeSubsetPrior_nonneg P (Q i) (x i)
  have hmass : ∑ x, μ x = 1 := by
    rw [show (∑ x, μ x) = ∏ i, ∑ p : P, primeSubsetPrior P (Q i) p by
      exact (Fintype.prod_sum _).symm]
    simp only [fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i), Finset.prod_const_one]
  change ‖(∑ x, (μ x : ℂ) * F x) - ∑ x, (μ x : ℂ) * G x‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ x, ‖(μ x : ℂ) * (F x - G x)‖ := norm_sum_le _ _
    _ = ∑ x, μ x * ‖F x - G x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ _)]
    _ ≤ ∑ x, μ x * ε := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (herr x) (hμ x)
    _ = ε := by rw [← Finset.sum_mul, hmass, one_mul]

/-- The joint cell comparison can be integrated against the original product
law without introducing another normalization or a count of prime samples. -/
theorem BulkIntegrand.originalPrimeCells_mean_comparison {σ C : Type*}
    [Fintype σ] [Fintype C] (f : BulkIntegrand σ) (P : Finset ℕ)
    (q : σ → ℕ) (a : σ → C → ℕ) (u v : σ → C → ℝ)
    (hSP : ∀ i, primeCellSupport (q i) (a i) (u i) (v i) ⊆ P)
    (hsep : ∀ i c d, c ≠ d →
      ¬Nat.ModEq (q i) (a i c) (a i d) ∨ v i c ≤ u i d ∨ v i d ≤ u i c)
    (hS : ∀ i, (∑ p ∈ primeCellSupport (q i) (a i) (u i) (v i), (p : ℝ)⁻¹) ≠ 0)
    (l : List σ) (ν : σ → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)] (ε : ℝ)
    (herr : ∀ x, ‖f.averages (fun i => bulkCellMixture
        (∑ p ∈ primeCellSupport (q i) (a i) (u i) (v i), (p : ℝ)⁻¹)⁻¹
        (fun c => primeLogCellMeasure (q i) (a i c) (u i c) (v i c))) l x -
      f.averages ν l x‖ ≤ ε) :
    let S := fun i => primeCellSupport (q i) (a i) (u i) (v i)
    ‖(∑ x : σ → P, ((∏ i, primeSubsetPrior P (S i) (x i) : ℝ) : ℂ) * f (primeArrayLogs x)) -
      ∑ x : σ → P, ((∏ i, primeSubsetPrior P (S i) (x i) : ℝ) : ℂ) *
        f.averages ν l (primeArrayLogs x)‖ ≤ ε := by
  dsimp only
  rw [← f.originalPrimeCells_mean P q a u v hSP hsep hS l]
  exact originalPrimePrior_mean_comparison P _ hSP hS _ _ ε
    (fun x => herr (primeArrayLogs x))

end Ostmann

end OAI
