import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanControlledFolner
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CocyclePullbackSublinear

namespace OAI

/-! # Reduced unitary cohomology of the actual unimodular Cartan group

Root contraction proves sublinearity. Concrete controlled Følner pairs in the
semidirect cover supply the averaging vectors, and compact lifts descend the
uniform approximation to the original group.
-/

noncomputable section
namespace PolycyclicRecognition

universe v

open Module LieAlgebra LieModule MeasureTheory MeasureTheory.Measure Set
open scoped Manifold

attribute [local instance] semidirectProductTopology semidirectProductMeasurableSpace
  semidirectProduct_borelSpace

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (M : CartanWordModel H) (hExp : IsGroupExponential Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (hπcont : Continuous (fun g => (π g).toAdd))

include T F M hExp hunimod hπExp hπcont in
theorem cartan_unitary_reduced_vanishing : UnitaryReducedVanishing.{0, v} G := by
  intro E _ _ _ ρ hfix hρ b hbc hb Q hQ ε hε
  have nilp := nilpotentPublishedInputs
  have haarN := nilp.haar _ F.N
  have haarD := nilp.haar _ F.D
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
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
  obtain ⟨dD⟩ := geodesicMetricExistenceInput F.D.carrier (exists_compact_generating_set _)
  obtain ⟨dS⟩ := F.nonempty_semidirect_properChainMetric T
  let := dS.compatibleMetric
  let : IsTopologicalGroup (F.N.carrier ⋊[F.action] F.D.carrier) := F.semidirect_topologicalGroup
  let : IsIsometricSMul (F.N.carrier ⋊[F.action] F.D.carrier)
      (F.N.carrier ⋊[F.action] F.D.carrier) := dS.isometric_compatibleMetric
  let : ProperSpace (F.N.carrier ⋊[F.action] F.D.carrier) := dS.proper_compatibleMetric
  let μN : Measure F.N.carrier := haar
  let μD : Measure F.D.carrier := haar
  let μ := semidirectProductMeasure F.action μN μD
  have hpres := F.action_preserves_haar T M hExp exponentialLinearRealizationInput_intrinsic
    haarN haarD (nilp.dynkin _ F.N) hunimod μN
  let : μ.IsHaarMeasure := semidirectProductMeasure_isHaarMeasure F.action μN μD
    F.continuous_action hpres
  let : μN.IsInvInvariant := nilpotent_haar_isInvInvariant haarN F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)) μN
  let : μD.IsInvInvariant := nilpotent_haar_isInvInvariant haarD F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance) μD
  let : μ.IsInvInvariant := semidirectProductMeasure_isInvInvariant F.action μN μD
    F.continuous_action hpres
  obtain ⟨pairs⟩ := cartan_cover_controlled_pairs T F M hExp hunimod eW π hπExp hπcont
    dS dD μN μD
  let f := F.semidirectProjection
  have hf : Continuous f := F.continuous_semidirectProjection
  have hbp : IsUnitaryCocycle (ρ.comp f) (b ∘ f) := by
    intro g h
    change b (f (g * h)) = _
    rw [map_mul]
    exact hb _ _
  have hsub := sublinear_comp_of_compact_word_estimates f hf b dS.chains_compatibleMetric
    (fun K hK => cartan_cocycle_compact_words T F M hExp exponentialLinearRealizationInput_intrinsic
      haarN (nilp.dynkin _ F.N) chartN hchartN chartD hchartD (nilp.dynkin _ F.D)
      hunimod eW π hπExp hπcont ρ hρ hfix b hbc hb hK)
  obtain ⟨K, hK, hlift⟩ := F.compact_lifts_semidirectProjection Q hQ
  obtain ⟨φ, hφ⟩ := (pairs.toReiter μ).almost_coboundary μ (hbc.comp hf) hbp hsub K hK hε
  refine ⟨φ, fun q hq => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hlift hq
  exact hφ x hx

end PolycyclicRecognition

end

end OAI
