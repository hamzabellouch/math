import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryTranslateMass
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentBoundaryAveraging

namespace OAI

/-! # The transversal trace bound from actual boundary maps and leaf bounds -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped Manifold ENNReal

variable {P G N S T D ES : Type*} [Group G] [Group N] [Group S]
  [MetricSpace S] [IsIsometricSMul S S] [ProperSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [ChartedSpace ES S] [LieGroup (𝓘(ℝ, ES)) ⊤ S] [SimplyConnectedSpace S]
  [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]

/-- Boundary image masses and the leaf-height estimate imply a uniform
transversal trace comparison. The actual homeomorphisms supply the measures;
the nilpotent exponential inputs discharge all metric-volume obligations. -/
theorem boundary_averaged_transversal_trace
    (chains : LinearMetricChains S)
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
  obtain ⟨K', hK', hmass'⟩ := boundary_translated_mass_bounds act ι π hπ hact
    B μT f height d U hK hmass hleaf
  exact trace_bound_of_nilpotent_boundary_masses chains dynkin haar Exp hExp hnil
    μS (fun p => Measure.map (B p).symm μT) (fun j => act (d j) '' U)
    source (fun p j => height (f p (d j))) (fun j => hU.image (hcont (d j))) hc hK'
    hsource (fun p j z => (hmass' p j z).1) (fun p j z => (hmass' p j z).2)

end PolycyclicRecognition

end

end OAI
