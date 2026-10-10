import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSemidirectCover
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectProductHaar
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConstructChainMetric
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConstructedNilpotentPublishedInputs
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentChartCountability
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHaarInvariance
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarSymmetry
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularRealization

namespace OAI

/-! # Proper metrics and invariant product measure on the Cartan cover -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Module LieAlgebra
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

attribute [local instance] semidirectProductTopology semidirectProductMeasurableSpace
  semidirectProduct_borelSpace

include T in
omit [SimplyConnectedSpace G] in
theorem CartanFactorModel.nonempty_semidirect_properChainMetric :
    Nonempty (ProperChainMetric (F.N.carrier ⋊[F.action] F.D.carrier)) := by
  have nilp := nilpotentPublishedInputs
  obtain ⟨⟨chartN, _⟩, _⟩ := (nilp.haar _ F.N).2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, _⟩, _⟩ := (nilp.haar _ F.D).2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let : SecondCountableTopology F.N.carrier := F.N.secondCountable_of_chart chartN
  let : SecondCountableTopology F.D.carrier := F.D.secondCountable_of_chart chartD
  let : LocallyCompactSpace F.N.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.N.modelSpace))
  let : LocallyCompactSpace F.D.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.D.modelSpace))
  let : IsTopologicalGroup (F.N.carrier ⋊[F.action] F.D.carrier) :=
    F.semidirect_topologicalGroup
  exact geodesicMetricExistenceInput _ (exists_compact_generating_set _)

include T in
theorem CartanFactorModel.semidirect_product_haar
    (M : CartanWordModel H) (hExp : IsGroupExponential Exp)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0) :
    ∃ μ : Measure (F.N.carrier ⋊[F.action] F.D.carrier),
      μ.IsHaarMeasure ∧ μ.IsInvInvariant := by
  have nilp := nilpotentPublishedInputs
  have hN := F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)
  have hD := F.D.tangent_nilpotent inferInstance
  obtain ⟨⟨chartN, _⟩, _⟩ := (nilp.haar _ F.N).2 F.ExpN F.isExpN hN
  obtain ⟨⟨chartD, _⟩, _⟩ := (nilp.haar _ F.D).2 F.ExpD F.isExpD hD
  let : SecondCountableTopology F.N.carrier := F.N.secondCountable_of_chart chartN
  let : SecondCountableTopology F.D.carrier := F.D.secondCountable_of_chart chartD
  let : LocallyCompactSpace F.N.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.N.modelSpace))
  let : LocallyCompactSpace F.D.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.D.modelSpace))
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup F.D.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤
  let μN : Measure F.N.carrier := haar
  let μD : Measure F.D.carrier := haar
  let : μN.IsInvInvariant := nilpotent_haar_isInvInvariant
    (nilp.haar _ F.N) F.ExpN F.isExpN hN μN
  let : μD.IsInvInvariant := nilpotent_haar_isInvInvariant
    (nilp.haar _ F.D) F.ExpD F.isExpD hD μD
  have hp := F.action_preserves_haar T M hExp exponentialLinearRealizationInput_intrinsic
    (nilp.haar _ F.N) (nilp.haar _ F.D) (nilp.dynkin _ F.N) hunimod μN
  exact ⟨semidirectProductMeasure F.action μN μD,
    semidirectProductMeasure_isHaarMeasure F.action μN μD F.continuous_action hp,
    semidirectProductMeasure_isInvInvariant F.action μN μD F.continuous_action hp⟩

end PolycyclicRecognition

end

end OAI
