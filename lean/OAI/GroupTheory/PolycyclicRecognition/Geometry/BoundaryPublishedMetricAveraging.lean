import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryAveragedTrace
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieModelMetric

namespace OAI

/-! # The published proper chain metric discharges the averaging metric -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped Manifold ENNReal

variable {P G N T D ES : Type*} {S : Type} [Group G] [Group N] [Group S]
  [TopologicalSpace S] [T2Space S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [ChartedSpace ES S] [LieGroup (𝓘(ℝ, ES)) ⊤ S] [SimplyConnectedSpace S]
  [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]

/-- Only the existing proper chain metric input is needed on this connected
nilpotent quotient; its topology is preserved before applying averaging. -/
theorem boundary_averaged_trace_of_published_metric
    (metricInput : GeodesicMetricExistenceInput)
    (dynkin : NilpotentDynkinExpansionInput ES S)
    (haar : NilpotentExponentialHaarInput ES S)
    (Exp : GroupLieAlgebra (𝓘(ℝ, ES)) S → S) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, ES)) S))
    (μS : Measure S) [μS.IsHaarMeasure] (μT : Measure T) [SFinite μT]
    (act : G →* Equiv.Perm S) (hcont : ∀ x, Continuous (act x))
    (ι : N →* G) (π : N →* S) (hπ : Function.Surjective π)
    (hact : ∀ n x, act (ι n) x = π n * x)
    (B : P → S ≃ₜ T) (f : P → G → G) (height : G → ℝ)
    (d : D → G) (source : D → ℝ) (U : Set S) (hU : IsCompact U)
    {c K C : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hsource : ∀ j, μS (act (d j) '' U) = ENNReal.ofReal (c * Real.exp (source j)))
    (hmass : ∀ p x,
      ENNReal.ofReal (Real.exp (height (f p x))) ≤
        ENNReal.ofReal K * μT (B p '' (act x '' U)) ∧
      μT (B p '' (act x '' U)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x))))
    (hleaf : ∀ p n j, |height (f p (ι n * d j)) - height (f p (d j))| ≤ C) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ p j j₀,
      |(height (f p (d j)) - height (f p (d j₀))) - (source j - source j₀)| ≤ bound := by
  let : IsTopologicalGroup S := topologicalGroup_of_lieGroup (𝓘(ℝ, ES)) ⊤
  let : LocallyCompactSpace S := Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, ES))
  let dS : ProperChainMetric S := Classical.choice
    (metricInput S (exists_compact_generating_set S))
  let : MetricSpace S := dS.compatibleMetric
  let : ProperSpace S := dS.proper_compatibleMetric
  let : IsIsometricSMul S S := dS.isometric_compatibleMetric
  exact boundary_averaged_transversal_trace dS.chains_compatibleMetric dynkin haar Exp hExp hnil
    μS μT act hcont ι π hπ hact B f height d source U hU hc hK hsource hmass hleaf

end PolycyclicRecognition

end

end OAI
