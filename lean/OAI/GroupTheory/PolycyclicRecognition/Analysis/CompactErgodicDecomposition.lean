import OAI.GroupTheory.PolycyclicRecognition.Analysis.LocallyCompactErgodicComponents
import OAI.GroupTheory.PolycyclicRecognition.Algebra.KernelConullRepair
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ErgodicDecompositionInput

namespace OAI

/-! # Ergodic decomposition on compact metrizable action spaces

Conditioning on the invariant sigma algebra gives ergodic components almost
everywhere. Repairing the null exceptional set on the factor preserves exact
orbit invariance of the component map.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] [MulAction G X] [ContinuousSMul G X]

theorem ergodicDecompositionInput_of_compactMetric : ErgodicDecompositionInput G X := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  intro μ hμ hi
  have : IsProbabilityMeasure μ := hμ
  have : SMulInvariantMeasure G X μ := hi
  have : Nonempty X := nonempty_of_isProbabilityMeasure μ
  obtain ⟨k, hk, hgood, he⟩ := exists_kernel_conull_repair
    (μ.map (invariantFactorMap G X)) (invariantConditionalKernel (G := G) μ)
    (fun ν => ErgodicSMul G X ν) (invariantConditionalKernel_ergodic_ae (G := G) μ)
  let κ : X → Measure X := fun x => k (invariantFactorMap G X x)
  have hκ : Measurable κ := hk.comp (measurable_invariantFactorMap G X)
  have heκ : κ =ᵐ[μ] invariantConditionalMeasures (G := G) μ :=
    ae_of_ae_map (measurable_invariantFactorMap G X).aemeasurable he
  refine ⟨κ, fun x => hgood _, ?_, ?_⟩
  · intro g x
    ext s hs
    exact invariantFactor_observable (fun z => k z s)
      ((Measure.measurable_coe hs).comp hk) g x
  · intro s hs
    refine ⟨(Measure.measurable_coe hs).comp hκ, ?_⟩
    rw [invariantConditionalMeasures_barycenter (G := G) μ s hs]
    exact lintegral_congr_ae (heκ.mono (fun x hx => congrArg (fun ν : Measure X => ν s) hx.symm))

end PolycyclicRecognition

end

end OAI
