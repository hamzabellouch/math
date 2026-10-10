import OAI.Analysis.IrrationalRotation.Sampling.PhaseBlockWeight
import OAI.Analysis.IrrationalRotation.Spectral.ProductBlockQuasinilpotent

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Invariant233.ProductModel

open ProductPhases

theorem exists_admissible_phase_block_quasinilpotent
    (m : ℕ → ℕ) (hgrowth : ∀ j, 2 ^ j ≤ m j)
    (K G C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hG : ∀ j, 0 < G j)
    (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (hscale : ∀ j, 2 < (m j : ℝ) * K j)
    (hsum : Summable (fun j => 1 / K j)) :
    ∃ (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ),
      (∀ a : Σ j, Fin (m j),
        e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val) ∧
      (∀ j, ∀ i ∈ consecutiveBlock m j,
        θ i ∈ Icc (1 / ((m j : ℝ) * K j)) (2 / ((m j : ℝ) * K j))) ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      AdmissibleAnglesAndCosts θ (fun i => C (e i).1) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i => C (e i).1)) ∧
      (∀ᵐ x ∂baseMeasure,
        0 < weight θ (fun i => C (e i).1) x ∧ weight θ (fun i => C (e i).1) x ≤ 1) ∧
      (∀ j, smallPhaseCondition (consecutiveBlock m j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock m j) ((m j : ℝ) * K j) θ) ∧
      weightedOperator θ (fun i => C (e i).1) ∈ factor θ ∧
      weightedOperator θ (fun i => C (e i).1) ≠ 0 ∧
      NormQuasinilpotent (weightedOperator θ (fun i => C (e i).1)) ∧
      spectrum ℂ (weightedOperator θ (fun i => C (e i).1)) = {0} := by
  obtain ⟨e, θ, he, hθ, hsumθ, hadm, hlog, hpos, hsmall, hlarge⟩ :=
    exists_admissible_phase_block_weight m hgrowth K G C hK hG hC hscale hsum
  have hθ0 (i : ℕ) : 0 ≤ θ i := (hadm.1 i).1.le
  have hθ01 (i : ℕ) : θ i ∈ Ico (0 : ℝ) 1 :=
    ⟨hθ0 i, (hadm.1 i).2.1⟩
  have hc0 (i : ℕ) : 0 ≤ C (e i).1 := (hadm.1 i).2.2.le
  have hdiv := (hasNegInfiniteLogIntegral_iff_tsum θ _ hθ01 hc0).mp hlog
  exact ⟨e, θ, he, hθ, hsumθ, hadm, hlog, hpos, hsmall, hlarge,
    weightedOperator_mem_factor θ _,
    weightedOperator_ne_zero θ _ hθ0 hc0 hadm.2.1,
    weightedOperator_normQuasinilpotent θ _ hθ0 hc0 hadm.2.1 hdiv,
    weightedOperator_spectrum_eq_singleton_zero θ _ hθ0 hc0 hadm.2.1 hdiv⟩

end Invariant233.ProductModel

end

end OAI
