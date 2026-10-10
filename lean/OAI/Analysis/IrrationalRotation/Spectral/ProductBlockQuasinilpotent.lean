import OAI.Analysis.IrrationalRotation.Product.ProductBlockCost
import OAI.Analysis.IrrationalRotation.Spectral.ProductQuasinilpotent

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

theorem weightedOperator_normQuasinilpotent_of_block_bounds
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ) (hθsum : Summable θ)
    (hθ : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    NormQuasinilpotent (weightedOperator θ (fun i => C (e i).1)) := by
  apply weightedOperator_normQuasinilpotent θ (fun i => C (e i).1) _ _ hθsum
    (tsum_block_coordinate_cost_eq_top m hm K C hK hC e θ hθ)
  · intro i
    have hm0 : (0 : ℝ) < m (e i).1 := Nat.cast_pos.mpr (hm _)
    exact (one_div_pos.mpr (mul_pos hm0 (lt_of_lt_of_le zero_lt_one (hK _)))).le.trans
      (hθ i)
  · intro i
    exact (sq_nonneg _).trans (hC _)

theorem exists_admissible_block_quasinilpotent
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, (K j) ^ 2 ≤ C j)
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
      spectrum ℂ (weightedOperator θ (fun i => C (e i).1)) = {0} := by
  obtain ⟨e, θ, he, hbounds, hsumBound, hadm, hlog, hpos⟩ :=
    exists_admissible_block_weight m hm K C hK hC hscale hsum
  have hθ0 (i : ℕ) : 0 ≤ θ i := (hadm.1 i).1.le
  have hc0 (i : ℕ) : 0 ≤ C (e i).1 := (hadm.1 i).2.2.le
  have hdiv := tsum_block_coordinate_cost_eq_top m hm K C hK hC e θ
    (fun i => (hbounds i).1)
  exact ⟨e, θ, he, hbounds, hsumBound, hadm, hlog, hpos,
    weightedOperator_mem_factor θ _, weightedOperator_ne_zero θ _ hθ0 hc0 hadm.2.1,
    weightedOperator_normQuasinilpotent θ _ hθ0 hc0 hadm.2.1 hdiv,
    weightedOperator_spectrum_eq_singleton_zero θ _ hθ0 hc0 hadm.2.1 hdiv⟩

end Invariant233.ProductModel

end OAI
