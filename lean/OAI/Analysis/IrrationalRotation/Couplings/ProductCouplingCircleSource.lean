import OAI.Analysis.IrrationalRotation.Couplings.ProductCouplingCircle
import OAI.Analysis.IrrationalRotation.Couplings.BlockProductCoupling
import OAI.Analysis.IrrationalRotation.Analysis.L2UniformAbsoluteContinuity
import OAI.Analysis.IrrationalRotation.Analysis.RealDensityLp
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingAbsoluteContinuity

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

theorem exists_source_circle_hybrid_density
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) (ε : ℕ → Bool) :
    ∃ H : ProductModel.Base → ℝ, MemLp H 2 ProductModel.baseMeasure ∧
      (0 ≤ᵐ[ProductModel.baseMeasure] H) ∧
      (∫ x, H x ∂ProductModel.baseMeasure) = 1 ∧
      eLpNorm H 2 ProductModel.baseMeasure ≤ ENNReal.ofReal (blockDensityBound sourceKappa) ∧
      (law (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
        ha ha' hb hb' e tag)).map (circleHybridEndpoint ε) =
        ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨hs, htotal⟩ := ofBlocks_energy_sum m sourceKappa a b
    sourceKappa_nonneg sourceKappa_le hm ha ha' hb hb' e tag summable_sourceKappa_sq
  have hbound : Real.exp ((20 * (2 * (∑' s, sourceKappa s ^ 2) + 1)) / 2) =
      blockDensityBound sourceKappa := by
    unfold blockDensityBound
    congr 1
    ring
  simpa only [hbound] using exists_circle_hybrid_density
    (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
      ha ha' hb hb' e tag) ε hs htotal.le

section UniformSourceMarginals
variable (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s))

theorem exists_source_circle_hybrid_Lp_density (tag : ℕ) (ε : ℕ → Bool) :
    ∃ f : Lp ℝ 2 ProductModel.baseMeasure,
      (0 ≤ᵐ[ProductModel.baseMeasure] (f : ProductModel.Base → ℝ)) ∧
      (law (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
        ha ha' hb hb' e tag)).map (circleHybridEndpoint ε) =
        ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ‖f‖ ≤ blockDensityBound sourceKappa := by
  obtain ⟨g, hg, hn, _hmass, hbound, heq⟩ :=
    exists_source_circle_hybrid_density m a b hm ha ha' hb hb' e tag ε
  exact DensityTransport.exists_Lp_density_of_memLp _ _ hg hn heq
    (blockDensityBound_pos sourceKappa).le hbound

theorem source_hybrid_pairs_hasUniformL2Marginals
    (tag : ℕ → ℕ) (ε₁ ε₂ : ℕ → ℕ → Bool) :
    ProductModel.HasUniformL2Marginals (fun n =>
      (law (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
        ha ha' hb hb' e (tag n))).map
        (fun ω => (circleHybridEndpoint (ε₁ n) ω, circleHybridEndpoint (ε₂ n) ω))) := by
  refine ⟨blockDensityBound sourceKappa, (blockDensityBound_pos sourceKappa).le, ?_⟩
  intro n
  obtain ⟨f, hfn, hfm, hfb⟩ :=
    exists_source_circle_hybrid_Lp_density m a b hm ha ha' hb hb' e (tag n) (ε₁ n)
  obtain ⟨g, hgn, hgm, hgb⟩ :=
    exists_source_circle_hybrid_Lp_density m a b hm ha ha' hb hb' e (tag n) (ε₂ n)
  refine ⟨f, g, hfn, hgn, ?_, ?_, hfb, hgb⟩
  · rw [Measure.map_map measurable_fst
      ((circleHybridEndpoint_measurable (ε₁ n)).prodMk (circleHybridEndpoint_measurable (ε₂ n)))]
    exact hfm
  · rw [Measure.map_map measurable_snd
      ((circleHybridEndpoint_measurable (ε₁ n)).prodMk (circleHybridEndpoint_measurable (ε₂ n)))]
    exact hgm

theorem source_hybrid_pairs_uniformlyAbsolutelyContinuous
    (tag : ℕ → ℕ) (ε₁ ε₂ : ℕ → ℕ → Bool) :
    let η := fun n =>
      (law (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
        ha ha' hb hb' e (tag n))).map
        (fun ω => (circleHybridEndpoint (ε₁ n) ω, circleHybridEndpoint (ε₂ n) ω))
    UniformlyAbsolutelyContinuous ProductModel.baseMeasure (fun n => (η n).map Prod.fst) ∧
      UniformlyAbsolutelyContinuous ProductModel.baseMeasure (fun n => (η n).map Prod.snd) :=
  (source_hybrid_pairs_hasUniformL2Marginals m a b hm ha ha' hb hb' e tag ε₁ ε₂).uniformlyAbsolutelyContinuous

theorem source_circle_hybrid_measureReal_le_sqrt (tag : ℕ) (ε : ℕ → Bool)
    (A : Set ProductModel.Base) (hA : MeasurableSet A) :
    ((law (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
      ha ha' hb hb' e tag)).map (circleHybridEndpoint ε)).real A ≤
      blockDensityBound sourceKappa * Real.sqrt (ProductModel.baseMeasure.real A) := by
  obtain ⟨g, hg, hn, _hmass, hbound, heq⟩ :=
    exists_source_circle_hybrid_density m a b hm ha ha' hb hb' e tag ε
  have hbnd : (eLpNorm g 2 ProductModel.baseMeasure).toReal ≤ blockDensityBound sourceKappa := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
      (ENNReal.toReal_ofReal (blockDensityBound_pos sourceKappa).le)
  rw [heq]
  refine (EndpointLoss.withDensity_measureReal_le_sqrt ProductModel.baseMeasure hg hn hA).trans ?_
  rw [EndpointLoss.sqrt_integral_sq_eq_toReal_eLpNorm hg]
  exact mul_le_mul_of_nonneg_right hbnd (Real.sqrt_nonneg _)

end UniformSourceMarginals

end Invariant233.OrderedProductCoupling

end OAI
