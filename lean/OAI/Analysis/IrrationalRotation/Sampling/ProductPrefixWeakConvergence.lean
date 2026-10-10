import OAI.Analysis.IrrationalRotation.Sampling.ProductPrefixApproximation
import OAI.Analysis.IrrationalRotation.Analysis.FiniteMeasureApproximation

namespace OAI

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace Invariant233.ProductPrefixApproximation.Endpoint
open ProductModel

theorem weaklyConverges_of_finitePrefix_tests
    (μ : ℕ → Measure EndpointPair) (ν : Measure EndpointPair)
    [∀ l, IsFiniteMeasure (μ l)] [IsFiniteMeasure ν]
    (M : ℝ) (hM : 0 ≤ M) (hmass : ∀ l, (μ l).real univ ≤ M)
    (hfinite : ∀ n (f : C(FinitePair n, ℝ)),
      Tendsto (fun l => ∫ xy, f (restrict n xy) ∂μ l) atTop
        (𝓝 (∫ xy, f (restrict n xy) ∂ν))) :
    WeaklyConverges μ ν := by
  intro f
  let a : EndpointPair := (0, 0)
  let g : ℕ → C(EndpointPair, ℝ) := fun n =>
    f.comp ⟨freeze a n, continuous_freeze a n⟩
  apply FiniteMeasureApproximation.tendsto_integral_of_uniform_approximation
    μ ν M hM hmass f g
  · exact continuous_freeze_tendstoUniformly a f
  · intro n
    simpa only [finiteTest_restrict, g, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using hfinite n (finiteTest a n f)

end Invariant233.ProductPrefixApproximation.Endpoint

end

end OAI
