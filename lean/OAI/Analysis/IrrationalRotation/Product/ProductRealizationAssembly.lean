import OAI.Analysis.IrrationalRotation.Product.ProductInvariantProjectionObstruction
import OAI.Analysis.IrrationalRotation.Spectral.ProductBrownMeasure
import OAI.Analysis.IrrationalRotation.Product.ProductFactorComplete
import OAI.Analysis.IrrationalRotation.Spectral.ProductPolarComplete

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Invariant233.ProductModel

theorem product_realization_of_ae_sampling
    (hsampling : ∀ (p : ProductScaleData) (_hp : ProductScaleLaws p)
      (S : ℕ → ℝ) (_hS : ∀ i, 0 < S i)
      (_hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
        S i = (p.m j : ℝ) * p.K j),
      ∀ᵐ θ ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
        HasAllFiniteCoordinateSampling θ) :
    ∃ θ c : ℕ → ℝ, AdmissibleAnglesAndCosts θ c ∧
      HasAllFiniteCoordinateSampling θ ∧
      (∀ᵐ x ∂baseMeasure, 0 < weight θ c x) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ c) ∧
      IsTypeII1FactorWithVector (factor θ) traceVector ∧
      HasSeparablePredual (factor θ) ∧
      weightedOperator θ c ∈ factor θ ∧ weightedOperator θ c ≠ 0 ∧
      NormQuasinilpotent (weightedOperator θ c) ∧
      vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 ∧
      spectrum ℂ (weightedOperator θ c) = {0} ∧
      IsVectorBrownMeasure traceVector (weightedOperator θ c) (Measure.dirac 0) ∧
      HasOnlyTrivialInvariantProjections (factor θ) (weightedOperator θ c) ∧
      ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  obtain ⟨p, hp⟩ := ProductScaleConstruction.exists_product_scales
  have hm (j : ℕ) : 0 < p.m j := lt_of_lt_of_le (by norm_num) (hp.m_ge_100 j)
  obtain ⟨e, he⟩ := InvariantProjection.IndependentAngles.exists_consecutiveBlocks_equiv p.m hm
  have hK (j : ℕ) : (1 : ℝ) ≤ p.K j := by exact_mod_cast hp.K_pos j
  have hG (j : ℕ) : (0 : ℝ) < p.G j := by exact_mod_cast hp.G_pos j
  have hC (j : ℕ) : (p.K j : ℝ) ^ 2 ≤ p.C j := by
    rw [hp.C_eq j]
    exact le_max_right _ _
  have hscale (j : ℕ) : (2 : ℝ) < (p.m j : ℝ) * p.K j := by
    have hm100 : (100 : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_100 j
    have hk := hK j
    nlinarith
  have hS (i : ℕ) : 0 < (p.m (e i).1 : ℝ) * p.K (e i).1 :=
    mul_pos (Nat.cast_pos.mpr (hm _)) (Nat.cast_pos.mpr (hp.K_pos _))
  have hsamp := hsampling p hp
    (fun i => (p.m (e i).1 : ℝ) * p.K (e i).1) hS
    (by
      intro j i hi
      rw [ProductPhases.enumeration_block_of_mem p.m e he hi])
  obtain ⟨θ, hθ, _hsum, hadm, hlog, hpos, hsmall, hlarge, hs⟩ :=
    exists_admissible_phase_block_weight_and p.m hp.m_ge_pow_self
      (fun j => (p.K j : ℝ)) (fun j => (p.G j : ℝ)) p.C
      hK hG hC hscale hp.summable_reciprocal e he hsamp
  have hθ0 (i : ℕ) : 0 ≤ θ i := (hadm.1 i).1.le
  have hθ01 (i : ℕ) : θ i ∈ Ico (0 : ℝ) 1 := ⟨hθ0 i, (hadm.1 i).2.1⟩
  have hc (i : ℕ) : 0 ≤ p.C (e i).1 := (hadm.1 i).2.2.le
  have hdiv := (hasNegInfiniteLogIntegral_iff_tsum θ _ hθ01 hc).mp hlog
  obtain ⟨hfactor, hpredual, _hfields, _htrace⟩ := factor_complete θ hadm.2.2
  refine ⟨θ, (fun i => p.C (e i).1), hadm, hs,
    hpos.mono (fun _ hx => hx.1), hlog, hfactor, hpredual,
    weightedOperator_mem_factor θ _,
    weightedOperator_ne_zero θ _ hθ0 hc hadm.2.1,
    weightedOperator_normQuasinilpotent θ _ hθ0 hc hadm.2.1 hdiv,
    weightedOperator_vectorDeterminant_zero θ _ hθ0 hc hadm.2.1 hlog,
    weightedOperator_spectrum_eq_singleton_zero θ _ hθ0 hc hadm.2.1 hdiv,
    weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral
      θ _ hθ01 hc hadm.2.1 hlog,
    ?_, productPolarStructure_of_admissible θ _ hadm⟩
  exact hasOnlyTrivialInvariantProjections_of_sampling_and_phases hp e he θ hadm
    hθ hsmall hlarge hs

end Invariant233.ProductModel

end

end OAI
