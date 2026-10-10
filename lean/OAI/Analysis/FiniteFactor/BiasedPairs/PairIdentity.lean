import OAI.Analysis.FiniteFactor.BiasedPairs.PrefixDomination
import OAI.Analysis.FiniteFactor.CrossedProduct.UncappedPairIdentity

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

theorem sourceProjection_biased_prefix_pairs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j n : ℕ) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n) : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ p := by
  apply (sourceBiasedPrefix_domination j n).ae_le
  change ∀ᵐ z ∂(∑ I ∈ (CouplingParameters.blockPrefix sourceBlockSize n).powerset,
    (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus)), z ∈ sourceCappedPairZeroSet θ p
  rw [ae_iff,Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro I hI
  exact ae_iff.mp (sourceProjection_lambda_pairs θ hθ hs hp hproj hinv I)

/-- Weak transfer to the actual full biased law. Uniform absolute continuity
and the common compact zero sets have all been proved for these actual laws. -/
theorem sourceProjection_biased_pairs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j (fun _ => true) : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ p := by
  apply finiteMeasure_ae_of_compact_approximation _ _ (sourceBiasedPrefix_weak j) _
    (sourceCappedPairZeroSet_measurable θ p)
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁,hδ₁,h₁⟩ := sourceBiasedPrefix_uniformAC j false (ε / 2) hhalf
  obtain ⟨δ₂,hδ₂,h₂⟩ := sourceBiasedPrefix_uniformAC j true (ε / 2) hhalf
  obtain ⟨Q,_,hQ,hμQ,hK⟩ := exists_source_capped_compact θ p
    MeasurableSet.univ (Eventually.of_forall (fun _ => Set.mem_univ _))
    (ne_of_gt (lt_min hδ₁ hδ₂))
  refine ⟨(Q ×ˢ Q) ∩ sourceCappedPairZeroSet θ p,hK,Set.inter_subset_right,?_⟩
  intro n
  have hb₁ := h₁ Qᶜ hQ.isClosed.measurableSet.compl
    (hμQ.trans_le (min_le_left _ _)) n
  have hb₂ := h₂ Qᶜ hQ.isClosed.measurableSet.compl
    (hμQ.trans_le (min_le_right _ _)) n
  have hb := add_le_add hb₁ hb₂
  have he : (↑(ε / 2) : ℝ≥0∞) + ↑(ε / 2) = ε := by
    rw [← ENNReal.coe_add,add_halves]
  rw [he] at hb
  exact (measure_pair_compact_loss _ Q hQ.isClosed.measurableSet _
    (sourceProjection_biased_prefix_pairs θ hθ hs hp hproj hinv j n)).trans hb

/-- Both endpoints of every actual biased law have finite floor support. -/
theorem sourceBiased_endpoints_finiteFloor (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j (fun _ => true) : Measure SourceSamplingTorus),
      finiteFloorSupport θ (sourceTorusRepresentative z.1) ∧
      finiteFloorSupport θ (sourceTorusRepresentative z.2) := by
  have hf := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (ae_finiteFloorSupport θ hθ.summable)
  exact sourceBiasedTorusMeasure_endpoints_conull j (fun _ => true) _ hf

/-- The full uncapped invariant-projection identity under the constructed nu_j.
The bounded diagonal acts by the original cocycle ratio on every l2 vector. -/
theorem sourceProjection_biased_ratio_identity (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j (fun _ => true) : Measure SourceSamplingTorus),
      ∃ D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert,
        ‖D‖ ≤ 1 ∧
        (∀ (v : SourceFiberHilbert) (k : ℤ), D v k =
          (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.2) /
            sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.1) : ℂ) * v k) ∧
        (1-sourceTorusOperatorField p z.2)*D*sourceTorusOperatorField p z.1 = 0 := by
  filter_upwards [sourceProjection_biased_pairs θ hθ hs hp hproj hinv j,
    sourceBiased_endpoints_finiteFloor θ hθ j,sourceBiasedTorusMeasure_ordered j (fun _ => true)]
    with z hz hf hord
  refine ⟨fiberDiagonal (sourceCappedRatio θ z) (sourceCappedRatio_norm θ z),
    fiberDiagonal_norm _ _,?_,hz⟩
  intro v k
  rw [fiberDiagonal_apply,sourceCappedRatio_eq_ratio θ z hf.1 hf.2 hord k,Complex.ofReal_div]

end
end FiniteFactor

end OAI
