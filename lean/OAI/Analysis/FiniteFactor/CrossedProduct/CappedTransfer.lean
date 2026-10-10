import OAI.Analysis.FiniteFactor.CrossedProduct.CappedPair
import OAI.Analysis.FiniteFactor.CompactZeroTransfer
import OAI.Analysis.FiniteFactor.L2UniformAbsoluteContinuity
import OAI.Analysis.FiniteFactor.CrossedProduct.OrderedTorusSampling
import OAI.Analysis.FiniteFactor.OrbitSampling.TorusLimitMarginals

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

/-- Uniform absolute continuity of both actual ordered sampling marginals,
derived from the previously proved L2 density bounds. -/
theorem SourceOrderedTorusSampling.uniformAC {θ : SourceCoordinate → ℝ}
    (hθ : SourceOrderedTorusSampling θ) (I : Finset SourceCoordinate) (r : Bool)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ A, MeasurableSet A → sourceTorusHaar A < δ → ∀ n,
      ((sourceSamplingTrimmedTorus I n θ : Measure SourceSamplingTorus).map
        (sourceTorusEndpoint r)) A ≤ ε := by
  obtain ⟨C,hC⟩ := hθ.marginals I r
  apply uniformAC_of_L2_densities sourceTorusHaar _ C _ ε hε
  intro n
  obtain ⟨g,hg,hg0,he,hglp,hgC⟩ := hC n
  exact ⟨g,hglp,hg0,he,hgC⟩

/-- The actual capped projection equation passes to lambda_I on the original
sampling torus. The approximant equations are the remaining orbit obligation;
no continuity or measurable-selection premise is assumed. -/
theorem sourceCappedPair_limit_transfer {θ : SourceCoordinate → ℝ}
    (hθ : SourceOrderedTorusSampling θ) (I : Finset SourceCoordinate)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (hpair : ∀ n, ∀ᵐ z ∂(sourceSamplingTrimmedTorus I n θ : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ H) :
    ∀ᵐ z ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ H := by
  have hlim : Tendsto (fun n => sourceSamplingTrimmedTorus I n θ) atTop
      (𝓝 (sourceSamplingLambdaTorus I)) := by
    apply FiniteMeasure.tendsto_of_forall_integral_tendsto
    intro f
    exact hθ.weak I f.toContinuousMap
  apply finiteMeasure_ae_of_compact_approximation _ _ hlim _
    (sourceCappedPairZeroSet_measurable θ H)
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁,hδ₁,h₁⟩ := hθ.uniformAC I false (ε / 2) hhalf
  obtain ⟨δ₂,hδ₂,h₂⟩ := hθ.uniformAC I true (ε / 2) hhalf
  obtain ⟨Q,_,hQ,hμQ,hK⟩ := exists_source_capped_compact θ H
    MeasurableSet.univ (Eventually.of_forall (fun _ => Set.mem_univ _))
    (ne_of_gt (lt_min hδ₁ hδ₂))
  refine ⟨(Q ×ˢ Q) ∩ sourceCappedPairZeroSet θ H,hK,Set.inter_subset_right,?_⟩
  intro n
  have hb₁ := h₁ Qᶜ hQ.isClosed.measurableSet.compl
    (hμQ.trans_le (min_le_left _ _)) n
  have hb₂ := h₂ Qᶜ hQ.isClosed.measurableSet.compl
    (hμQ.trans_le (min_le_right _ _)) n
  have hb := add_le_add hb₁ hb₂
  have he : (↑(ε / 2) : ℝ≥0∞) + ↑(ε / 2) = ε := by
    rw [← ENNReal.coe_add, add_halves]
  rw [he] at hb
  exact (measure_pair_compact_loss _ Q hQ.isClosed.measurableSet _ (hpair n)).trans hb

end
end FiniteFactor

end OAI
