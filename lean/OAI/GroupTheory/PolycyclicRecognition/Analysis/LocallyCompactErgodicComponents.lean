import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarOrbitAverages
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantFactorComponents
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantFactorObservables
import OAI.GroupTheory.PolycyclicRecognition.Analysis.OrbitAverageErgodicity

namespace OAI

/-! # Ergodic components for a locally compact group on a compact metric space -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] [Nonempty X] [MulAction G X] [ContinuousSMul G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

theorem invariantConditionalKernel_testAverages (I : Finset ℕ) :
    ∀ᵐ z ∂μ.map (invariantFactorMap G X),
      ∃ (A : ℕ → FiniteOrbitAverage G) (c : ℝ),
      ∀ᵐ y ∂invariantConditionalKernel (G := G) μ z, Tendsto
        (fun n => (A n).apply ((finiteMeasureTest X I).indicator (fun _ => (1 : ℝ))) y)
        atTop (𝓝 c) := by
  let f := (finiteMeasureTest X I).indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator (measurableSet_finiteMeasureTest X I)
  have hL : MemLp f 2 μ := (memLp_const (1 : ℝ)).indicator
    (measurableSet_finiteMeasureTest X I)
  obtain ⟨A, F, hF, hFi, hlim⟩ := exists_pointwise_haarOrbitAverages (G := G) μ f hL
  have ht := factorConditionalKernel_ae μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X)
    (measurableSet_tendsto_fun (fun n => (A n).measurable_apply f hf) hF) hlim
  have hc := factorConditionalKernel_fiber μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X) (fun z => F z.val)
    (measurable_invariantFactor_lift F hF hFi)
  filter_upwards [ht, hc] with z hz hcz
  refine ⟨A, F z.val, ?_⟩
  filter_upwards [hz, hcz] with y hy hcy
  change F y = F z.val at hcy
  simpa only [hcy] using hy

theorem invariantConditionalKernel_ergodic_ae :
    ∀ᵐ z ∂μ.map (invariantFactorMap G X),
      ErgodicSMul G X (invariantConditionalKernel (G := G) μ z) := by
  have ht := ae_all_iff.2 (invariantConditionalKernel_testAverages (G := G) μ)
  have hi := factorConditionalKernel_invariant_ae_dense μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X) invariantFactor_membership_smul
  filter_upwards [ht, hi] with z hz hzi
  have : IsProbabilityMeasure (invariantConditionalKernel (G := G) μ z) := inferInstance
  have : SMulInvariantMeasure G X (invariantConditionalKernel (G := G) μ z) := hzi
  exact ergodicSMul_of_orbitAverages (invariantConditionalKernel (G := G) μ z) hz

theorem invariantConditionalMeasures_ergodic_ae_locallyCompact :
    ∀ᵐ x ∂μ, ErgodicSMul G X (invariantConditionalMeasures (G := G) μ x) := by
  exact ae_of_ae_map (measurable_invariantFactorMap G X).aemeasurable
    (invariantConditionalKernel_ergodic_ae (G := G) μ)

end PolycyclicRecognition

end

end OAI
