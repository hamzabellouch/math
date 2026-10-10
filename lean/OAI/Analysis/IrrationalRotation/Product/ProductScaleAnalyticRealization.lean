import OAI.Analysis.IrrationalRotation.Product.ProductScaleRealization
import OAI.Analysis.IrrationalRotation.Spectral.ProductSpectralBundle
import OAI.Analysis.IrrationalRotation.Product.ProductScalarity
import OAI.Analysis.IrrationalRotation.Product.ProductTracialVector
import OAI.Analysis.IrrationalRotation.Product.ProductBaseDynamics

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Invariant233.ProductModel

open ProductPhases

theorem exists_product_scales_phase_analytic_realization :
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
      (∀ k : ℤ, k ≠ 0 → Ergodic (rotationIterate θ k) baseMeasure) ∧
      (∀ k : ℤ, k ≠ 0 → ∀ x : Base, rotationIterate θ k x ≠ x) ∧
      IsFactor (factor θ) ∧ IsFaithfulTracialVector (factor θ) traceVector ∧
      weightedOperator θ (fun i => p.C (e i).1) ∈ factor θ ∧
      weightedOperator θ (fun i => p.C (e i).1) ≠ 0 ∧
      NormQuasinilpotent (weightedOperator θ (fun i => p.C (e i).1)) ∧
      vectorFugledeKadisonDeterminant traceVector
        (weightedOperator θ (fun i => p.C (e i).1)) = 0 ∧
      spectrum ℂ (weightedOperator θ (fun i => p.C (e i).1)) = {0} ∧
      ∀ (I : Finset ℕ) (n : ℕ),
        ‖weightedOperator θ (fun i => p.C (e i).1) ^ n‖ ≤
          Real.exp ((∑ i ∈ I, p.C (e i).1) -
            (n : ℝ) * (∑ i ∈ I, p.C (e i).1 * θ i)) := by
  obtain ⟨p, hp, e, θ, he, hθ, hsumθ, hsumθ', hadm, hlog, hpos,
      hsmall, hlarge, hmem, hne, hqn, hspec⟩ :=
    exists_product_scales_phase_quasinilpotent
  refine ⟨p, hp, e, θ, he, hθ, hsumθ, hsumθ', hadm, hlog, hpos,
    hsmall, hlarge, ?_, ?_, factor_isFactor θ hadm.2.2,
    traceVector_faithfulTracial θ, hmem, hne, hqn, ?_, hspec, ?_⟩
  · intro k hk
    exact rotationIterate_ergodic hadm.2.2 hk
  · intro k hk x
    exact rotationIterate_ne_self hadm.2.2 hk x
  · exact weightedOperator_vectorDeterminant_zero_of_ae_pos θ _
      (hpos.mono (fun _ hx => hx.1)) hlog
  · intro I n
    exact norm_weightedOperator_pow_le_finite_cost θ _
      (fun i => (hadm.1 i).1.le) (fun i => (hadm.1 i).2.2.le) hadm.2.1 I n

end Invariant233.ProductModel

end

end OAI
