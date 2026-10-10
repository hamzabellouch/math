import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHaarConjugation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarMeasureTransfer
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeSourcePacking

namespace OAI

/-! # The actual Cartan factor action preserves the chosen Haar measure -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold NNReal

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T M

/-- Trace zero and the published realization imply that the original
factor action preserves every Haar normalization, including the measure
constructed in ideal/quotient section coordinates. -/
theorem action_preserves_haar
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure] (d : F.D.carrier) :
    MeasurePreserving (F.action d) μ μ := by
  classical
  let _ : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let b := (finBasis ℝ (cartanRootIdeal H)).map F.N.equiv.toLinearEquiv
  let coordinates := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chartN
  let _ : LocallyCompactSpace F.N.carrier := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let _ : SecondCountableTopology F.N.carrier := coordinates.symm.secondCountableTopology
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨ν, hν, hinv, _⟩ := M.exists_haar_adjoint_invariant_weighted_boxes T hunimod
    F.N.equiv F.ExpN F.isExpN hbijN dynkinN haarN (finBasis ℝ (cartanRootIdeal H))
  let _ : ν.IsHaarMeasure := hν
  apply measurePreserving_of_haarMeasure ν μ (F.action d)
  rw [cartan_action_eq_adjoint_of_published_realization T M F hExp realize hbijN hbijD dynkinN d]
  exact hinv _

/-- The actual Lie-model action supplies the invariance needed by the
fixed-pivot source count. No action or fixed-slice volume assumption remains. -/
theorem exists_probe_source_packing_constant
    [IsIsometricSMul G G] [ProperSpace G]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure] {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : NormalizedPair G Λ) (x a : G) (d : F.D.carrier)
      (S : Set F.N.carrier), IsCompact S →
      ∃ t : Finset G,
        (↑t : Set G) ⊆
          (fun n => basedImage p.val.1 a (x * F.inclusionN n * F.inclusionD d)) '' S ∧
        (∀ u ∈ t, ∀ v ∈ t, u ≠ v → 1 ≤ dist u v) ∧
        c * (μ S).toReal ≤ (t.card : ℝ) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let _ : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  exact exists_fixedSlice_image_net_constant F.inclusionN F.inclusionD F.action μ F.closedN
    (F.action_preserves_haar T M hExp realize haarN haarD dynkinN hunimod μ) F.conjugation hΛ

end PolycyclicRecognition.CartanFactorModel

end

end OAI
