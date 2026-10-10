import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredCone
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHaarInvariance
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeightHaar

namespace OAI

/-! # Haar measure for the actual section used by the probe chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ)) (D : M.MeasuredCone F C)

/-- The intrinsic ideal Haar measure transported to the exact kernel. -/
def MeasuredCone.kernelMeasure : Measure D.maps.quotient.ker :=
  Measure.map
    (kernelRealization D.maps.quotient D.maps.inclusion D.maps.inclusion_closed D.maps.inclusion_range) D.measures.measureI

/-- The original product measure for any prescribed continuous section. -/
def MeasuredCone.sectionMeasure
    (σ : ContinuousMap D.Q.carrier F.N.carrier) (hσ : ∀ q, D.maps.quotient (σ q) = q) :
    Measure F.N.carrier := by
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup D.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.Q.modelSpace)) ⊤
  exact Measure.map (quotientSectionHomeomorph D.maps.quotient D.maps.quotient_continuous σ hσ).symm
    (D.measures.measureQ.prod (D.kernelMeasure M F C))

/-- The pure-word section chosen by the tile construction can replace the
initial quotient section without changing the Haar property. -/
theorem MeasuredCone.sectionMeasure_isHaar
    (σ : ContinuousMap D.Q.carrier F.N.carrier) (hσ : ∀ q, D.maps.quotient (σ q) = q) :
    (D.sectionMeasure M F C σ hσ).IsHaarMeasure := by
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup D.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.Q.modelSpace)) ⊤
  let bQ := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)).map D.Q.equiv.toLinearEquiv
  let qcoord := bQ.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartQ
  let : SecondCountableTopology D.Q.carrier := qcoord.symm.secondCountableTopology
  let : LocallyCompactSpace D.Q.carrier := qcoord.symm.isOpenEmbedding.locallyCompactSpace
  let bI := (finBasis ℝ (M.coneWordIdeal C)).map D.I.equiv.toLinearEquiv
  let icoord := bI.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartI
  let : SecondCountableTopology D.I.carrier := icoord.symm.secondCountableTopology
  let ke := kernelRealization D.maps.quotient D.maps.inclusion D.maps.inclusion_closed D.maps.inclusion_range
  let : SecondCountableTopology D.maps.quotient.ker := ke.symm.toHomeomorph.secondCountableTopology
  let : LocallyCompactSpace D.I.carrier := icoord.symm.isOpenEmbedding.locallyCompactSpace
  let : LocallyCompactSpace D.maps.quotient.ker := ke.symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : D.measures.measureQ.IsHaarMeasure := D.measures.haarQ
  let : (D.kernelMeasure M F C).IsHaarMeasure := D.measures.haarKernel
  let : (D.kernelMeasure M F C).IsMulRightInvariant := D.measures.kernel_rightInvariant
  exact quotientSection_product_isHaarMeasure D.maps.quotient D.maps.quotient_continuous σ hσ
    D.measures.measureQ (D.kernelMeasure M F C) D.measures.conjugation_invariant

variable [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)

include T hunimod

/-- The actual Cartan factor preserves the product measure of the chosen
source section. This is the same measure used by source packing. -/
theorem MeasuredCone.action_preserves_sectionMeasure
    (hExp : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (σ : ContinuousMap D.Q.carrier F.N.carrier) (hσ : ∀ q, D.maps.quotient (σ q) = q)
    (d : F.D.carrier) :
    MeasurePreserving (F.action d) (D.sectionMeasure M F C σ hσ) (D.sectionMeasure M F C σ hσ) := by
  let : (D.sectionMeasure M F C σ hσ).IsHaarMeasure :=
    D.sectionMeasure_isHaar M F C σ hσ
  exact F.action_preserves_haar T M hExp realize haarN haarD dynkinN hunimod _ d

omit [SimplyConnectedSpace G] in
/-- The sampler's prescribed scalar dilation preserves this same source
measure; no comparison of arbitrary Haar normalizations is required later. -/
theorem MeasuredCone.dilation_preserves_sectionMeasure
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hbijN : Function.Bijective F.ExpN)
    (σ : ContinuousMap D.Q.carrier F.N.carrier) (hσ : ∀ q, D.maps.quotient (σ q) = q)
    (h : H) (S : F.N.carrier → F.N.carrier)
    (hS : ∀ v, S (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v))) :
    MeasurePreserving S (D.sectionMeasure M F C σ hσ) (D.sectionMeasure M F C σ hσ) := by
  let : (D.sectionMeasure M F C σ hσ).IsHaarMeasure :=
    D.sectionMeasure_isHaar M F C σ hσ
  exact M.weightDilation_preserves_haar_of_exp_action T hunimod F.N.equiv F.ExpN
    F.isExpN hbijN dynkinN haarN _ h S hS

end PolycyclicRecognition.CartanWordModel

end

end OAI
