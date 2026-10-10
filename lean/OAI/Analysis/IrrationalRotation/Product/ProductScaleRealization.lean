import OAI.Analysis.IrrationalRotation.Product.ProductScaleConstruction
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import OAI.Analysis.IrrationalRotation.Spectral.PhaseBlockQuasinilpotent

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Invariant233.ProductModel

open ProductPhases

theorem exists_product_scales_phase_quasinilpotent :
    ∃ p : ProductScaleData, ProductScaleLaws p ∧
      ∃ (e : ℕ ≃ Σ j, Fin (p.m j)) (θ : ℕ → ℝ),
      (∀ a : Σ j, Fin (p.m j),
        e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val) ∧
      (∀ j, ∀ i ∈ consecutiveBlock p.m j,
        θ i ∈ Icc (1 / p.N j) (2 / p.N j)) ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / (p.K j : ℝ)) ∧
      (∑' i, θ i) ≤ 1 / 25 ∧
      AdmissibleAnglesAndCosts θ (fun i => p.C (e i).1) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i => p.C (e i).1)) ∧
      (∀ᵐ x ∂baseMeasure,
        0 < weight θ (fun i => p.C (e i).1) x ∧
          weight θ (fun i => p.C (e i).1) x ≤ 1) ∧
      (∀ j, smallPhaseCondition (consecutiveBlock p.m j) (p.K j) (p.G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock p.m j) (p.N j) θ) ∧
      weightedOperator θ (fun i => p.C (e i).1) ∈ factor θ ∧
      weightedOperator θ (fun i => p.C (e i).1) ≠ 0 ∧
      NormQuasinilpotent (weightedOperator θ (fun i => p.C (e i).1)) ∧
      spectrum ℂ (weightedOperator θ (fun i => p.C (e i).1)) = {0} := by
  obtain ⟨p, hp⟩ := ProductScaleConstruction.exists_product_scales
  have hK (j : ℕ) : (1 : ℝ) ≤ p.K j := by exact_mod_cast hp.K_pos j
  have hG (j : ℕ) : (0 : ℝ) < p.G j := by exact_mod_cast hp.G_pos j
  have hC (j : ℕ) : (p.K j : ℝ) ^ 2 ≤ p.C j := by
    rw [hp.C_eq j]
    exact le_max_right _ _
  have hscale (j : ℕ) : (2 : ℝ) < (p.m j : ℝ) * p.K j := by
    have hm : (100 : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_100 j
    have hk := hK j
    nlinarith
  obtain ⟨e, θ, he, hθ, hsumθ, hadm, hlog, hpos, hsmall, hlarge,
      hmem, hne, hqn, hspec⟩ :=
    exists_admissible_phase_block_quasinilpotent p.m hp.m_ge_pow_self
      (fun j => (p.K j : ℝ)) (fun j => (p.G j : ℝ)) p.C hK hG hC hscale
      hp.summable_reciprocal
  have hsumθ' : (∑' i, θ i) ≤ 1 / 25 := by
    have hsumK := hp.reciprocal_sum_le
    linarith
  exact ⟨p, hp, e, θ, he, hθ, hsumθ, hsumθ', hadm, hlog, hpos,
    hsmall, hlarge, hmem, hne, hqn, hspec⟩

end Invariant233.ProductModel

end

end OAI
