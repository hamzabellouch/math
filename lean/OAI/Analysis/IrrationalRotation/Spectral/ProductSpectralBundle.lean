import OAI.Analysis.IrrationalRotation.Spectral.ProductBlockQuasinilpotent
import OAI.Analysis.IrrationalRotation.Spectral.ProductDeterminant

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

theorem spectral_bundle_of_block_bounds
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, K j ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθsum : Summable θ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hθ : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i => C (e i).1)) ∧
      weightedOperator θ (fun i => C (e i).1) ∈ factor θ ∧
      weightedOperator θ (fun i => C (e i).1) ≠ 0 ∧
      NormQuasinilpotent (weightedOperator θ (fun i => C (e i).1)) ∧
      vectorFugledeKadisonDeterminant traceVector
        (weightedOperator θ (fun i => C (e i).1)) = 0 ∧
      spectrum ℂ (weightedOperator θ (fun i => C (e i).1)) = {0} := by
  have hc (i : ℕ) : 0 ≤ C (e i).1 := (sq_nonneg _).trans (hC _)
  have hθ0 (i : ℕ) : 0 ≤ θ i := (hθ01 i).1
  have hdiv := tsum_block_coordinate_cost_eq_top m hm K C hK hC e θ hθ
  exact ⟨hasNegInfiniteLogIntegral_of_block_bounds m hm K C hK hC e θ hθ01 hθ,
    weightedOperator_mem_factor θ _,
    weightedOperator_ne_zero θ _ hθ0 hc hθsum,
    weightedOperator_normQuasinilpotent θ _ hθ0 hc hθsum hdiv,
    weightedOperator_vectorDeterminant_zero_of_cost_divergence θ _ hθ01 hc hθsum hdiv,
    weightedOperator_spectrum_eq_singleton_zero θ _ hθ0 hc hθsum hdiv⟩

theorem exists_admissible_block_spectral_bundle
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, K j ^ 2 ≤ C j)
    (hscale : ∀ j, 2 < (m j : ℝ) * K j)
    (hsum : Summable (fun j => 1 / K j)) :
    ∃ (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ),
      (∀ i : Σ j, Fin (m j), e.symm i = (∑ r ∈ Finset.range i.1, m r) + i.2.val) ∧
      (∀ i, θ i ∈ Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1))) ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      AdmissibleAnglesAndCosts θ (fun i => C (e i).1) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i => C (e i).1)) ∧
      (∀ᵐ x ∂baseMeasure, 0 < weight θ (fun i => C (e i).1) x ∧
        weight θ (fun i => C (e i).1) x ≤ 1) ∧
      weightedOperator θ (fun i => C (e i).1) ∈ factor θ ∧
      weightedOperator θ (fun i => C (e i).1) ≠ 0 ∧
      NormQuasinilpotent (weightedOperator θ (fun i => C (e i).1)) ∧
      vectorFugledeKadisonDeterminant traceVector
        (weightedOperator θ (fun i => C (e i).1)) = 0 ∧
      spectrum ℂ (weightedOperator θ (fun i => C (e i).1)) = {0} := by
  obtain ⟨e, θ, he, hbounds, hsumBound, hadm, hlog, hpos, hmem, hne, hqn, hspec⟩ :=
    exists_admissible_block_quasinilpotent m hm K C hK hC hscale hsum
  exact ⟨e, θ, he, hbounds, hsumBound, hadm, hlog, hpos, hmem, hne, hqn,
    weightedOperator_vectorDeterminant_zero θ _ (fun i => (hadm.1 i).1.le)
      (fun i => (hadm.1 i).2.2.le) hadm.2.1 hlog, hspec⟩

end Invariant233.ProductModel

end

end OAI
