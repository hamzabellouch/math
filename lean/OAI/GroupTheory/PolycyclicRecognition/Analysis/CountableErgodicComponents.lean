import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantFactorObservables
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PointwiseOrbitAverages
import OAI.GroupTheory.PolycyclicRecognition.Analysis.OrbitAverageErgodicity

namespace OAI

/-! # Ergodicity of conditioning on the invariant sigma algebra

For a countable action, choose convergent finite convex orbit averages for
each member of a countable determining family. Their invariant limits are
constant on almost every conditional measure. The averaging zero-one
criterion then proves that these conditional measures are ergodic.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {G X : Type*} [Group G] [Countable G] [MeasurableSpace X]
  [StandardBorelSpace X] [Nonempty X] [MulAction G X] [MeasurableConstSMul G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

theorem invariantConditionalMeasures_testAverages (I : Finset ℕ) :
    ∀ᵐ x ∂μ, ∃ (A : ℕ → FiniteOrbitAverage G) (c : ℝ),
      ∀ᵐ y ∂invariantConditionalMeasures (G := G) μ x, Tendsto
        (fun n => (A n).apply ((finiteMeasureTest X I).indicator (fun _ => (1 : ℝ))) y)
        atTop (𝓝 c) := by
  let f := (finiteMeasureTest X I).indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator (measurableSet_finiteMeasureTest X I)
  have hL : MemLp f 2 μ := (memLp_const (1 : ℝ)).indicator
    (measurableSet_finiteMeasureTest X I)
  obtain ⟨A, F, hF, hFi, hlim⟩ := exists_pointwise_orbitAverages (G := G) μ f hL
  have ht := invariantConditionalMeasures_ae (G := G) μ
    (measurableSet_tendsto_fun (fun n => (A n).measurable_apply f hf) hF) hlim
  have hc := invariantConditionalMeasures_observable (G := G) μ F hF hFi
  filter_upwards [ht, hc] with x hx hcx
  refine ⟨A, F x, ?_⟩
  filter_upwards [hx, hcx] with y hy hcy
  simpa only [hcy] using hy

theorem invariantConditionalMeasures_ergodic_ae :
    ∀ᵐ x ∂μ, ErgodicSMul G X (invariantConditionalMeasures (G := G) μ x) := by
  have ht := ae_all_iff.2 (invariantConditionalMeasures_testAverages (G := G) μ)
  filter_upwards [ht, invariantConditionalMeasures_invariant_ae_countable (G := G) μ]
    with x hx hi
  have := invariantConditionalMeasures_probability (G := G) μ x
  have := hi
  exact ergodicSMul_of_orbitAverages (invariantConditionalMeasures (G := G) μ x) hx

end PolycyclicRecognition

end

end OAI
