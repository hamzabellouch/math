import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarSourceCells
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredConeCells
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProbeLift

namespace OAI

/-! # The actual polar source probability used by concentration -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory TopologicalSpace
open scoped Manifold Pointwise

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))

local notation "C" => heightConePreimage T eW K

/-- The measured cone and counted sampler supply the original probability
cell, its positive exponential volume, and all regularity needed for
concentration. No probability law or volume bound is added as an input. -/
theorem PolarTiledSamplerData.source_probability_data
    (D : M.MeasuredCone F C)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {ε : ℝ} (hε : 0 ≤ ε) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    (R : ℝ) (scale : ℕ → ℝ) (φ : ℕ → D.I.carrier ≃ₜ* D.I.carrier)
    (P : M.PolarTiledSamplerData T F hunimod eW K
      (D.maps.expI ∘ D.I.equiv) D.maps.inclusion bN ε β R scale φ) :
    let Z := TiledProbeChainData.sourceQuotientCell
      (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
      (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
      (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
      (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
      (scale := scale) (φ := φ) (ι := D.maps.inclusion)
      (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
      (Q := D.Q) (chartQ := D.maps.chartQ)
    let J := fun n => TiledProbeChainData.sourceKernelCell
      (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
      (ExpI := D.maps.expI ∘ D.I.equiv) (E := normalizedPolarTemplates K ε)
      (β := fun _ => β) (scale := scale) (ι := D.maps.inclusion)
      (Q := D.Q) (πQ := D.maps.quotient) (hι := D.maps.inclusion_closed)
      (hrange := D.maps.inclusion_range) n
    let μQ := D.measures.measureQ
    let μK := D.kernelMeasure M F C
    ∃ (hZm : MeasurableSet Z) (hJm : ∀ n, MeasurableSet (J n))
      (_hZ0 : μQ Z ≠ 0) (_hZt : μQ Z ≠ ⊤)
      (_hJ0 : ∀ n, μK (J n) ≠ 0) (_hJt : ∀ n, μK (J n) ≠ ⊤)
      (h0 : ∀ n, (μQ.prod μK) (Z ×ˢ J n) ≠ 0)
      (ht : ∀ n, (μQ.prod μK) (Z ×ˢ J n) ≠ ⊤),
      IsCompact Z ∧ (∀ n, IsCompact (J n)) ∧
      (∀ n, Nonempty (Z ×ˢ J n)) ∧
      (∀ n, (cellSubtypeProbability (μQ.prod μK) (Z ×ˢ J n)
        (hZm.prod (hJm n)) (h0 n) (ht n) : Measure (Z ×ˢ J n)).InnerRegular) ∧
      ∃ v : ℝ, 0 < v ∧ ∀ n,
        (μK (J n)).toReal = v * Real.exp (scale n *
          (M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0)) := by
  dsimp only
  let eQ := D.maps.chartQ
  let bQ := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)).map D.Q.equiv.toLinearEquiv
  let coordQ := bQ.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans eQ
  let bI' := (finBasis ℝ (M.coneWordIdeal C)).map D.I.equiv.toLinearEquiv
  let coordI := bI'.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartI
  let ke := kernelRealization D.maps.quotient D.maps.inclusion
    D.maps.inclusion_closed D.maps.inclusion_range
  let : SecondCountableTopology D.Q.carrier := coordQ.symm.secondCountableTopology
  let : SecondCountableTopology D.I.carrier := coordI.symm.secondCountableTopology
  let : SecondCountableTopology D.maps.quotient.ker := ke.symm.toHomeomorph.secondCountableTopology
  let : LocallyCompactSpace D.Q.carrier := coordQ.symm.isOpenEmbedding.locallyCompactSpace
  let : LocallyCompactSpace D.I.carrier := coordI.symm.isOpenEmbedding.locallyCompactSpace
  let : LocallyCompactSpace D.maps.quotient.ker :=
    (coordI.trans ke.toHomeomorph).symm.isOpenEmbedding.locallyCompactSpace
  let : PseudoMetrizableSpace D.Q.carrier := coordQ.symm.isEmbedding.pseudoMetrizableSpace
  let : PseudoMetrizableSpace D.maps.quotient.ker :=
    (coordI.trans ke.toHomeomorph).symm.isEmbedding.pseudoMetrizableSpace
  let : IsTopologicalGroup D.I.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.I.modelSpace)) ⊤
  let : D.measures.measureI.IsHaarMeasure := D.measures.haarI
  let : D.measures.measureQ.IsHaarMeasure := D.measures.haarQ
  let : (D.kernelMeasure M F C).IsHaarMeasure := D.measures.haarKernel
  let Z := TiledProbeChainData.sourceQuotientCell
      (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
      (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
      (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
      (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
      (scale := scale) (φ := φ) (ι := D.maps.inclusion)
      (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
      (Q := D.Q) (chartQ := D.maps.chartQ)
  let J := fun n => TiledProbeChainData.sourceKernelCell
      (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
      (ExpI := D.maps.expI ∘ D.I.equiv) (E := normalizedPolarTemplates K ε)
      (β := fun _ => β) (scale := scale) (ι := D.maps.inclusion)
      (Q := D.Q) (πQ := D.maps.quotient) (hι := D.maps.inclusion_closed)
      (hrange := D.maps.inclusion_range) n
  have volumes : IsCompact Z ∧ D.measures.measureQ Z ≠ 0 ∧
      D.measures.measureQ Z ≠ ⊤ ∧ ∃ v : ℝ, 0 < v ∧ ∀ n,
        IsCompact (J n) ∧ (D.kernelMeasure M F C) (J n) ≠ 0 ∧
        (D.kernelMeasure M F C) (J n) ≠ ⊤ ∧
        ((D.kernelMeasure M F C) (J n)).toReal = v * Real.exp (scale n *
          (M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0)) ∧
        IsCompact (Z ×ˢ J n) := by
    exact PolarTiledSamplerData.source_cell_volumes
      (EG := EG) (G := G) (W := W) (EI := D.I.modelSpace) (I := D.I.carrier)
      T M F hunimod eW K D.I.equiv D.maps.expI D.maps.isExpI
      haarI D.maps.chartI D.maps.chartI_eq D.Q D.maps.quotient D.maps.inclusion
      D.maps.inclusion_closed D.maps.inclusion_range bN bI hε β hβ R scale φ P
      D.maps.chartQ D.measures.measureI D.measures.measureQ
  obtain ⟨hZ, hZ0, hZt, v, hv, hj⟩ := volumes
  have hJ n : IsCompact (J n) := (hj n).1
  have hJ0 n : (D.kernelMeasure M F C) (J n) ≠ 0 := (hj n).2.1
  have hJt n : (D.kernelMeasure M F C) (J n) ≠ ⊤ := (hj n).2.2.1
  have hc n := compact_product_cell_probability_data D.measures.measureQ
    (D.kernelMeasure M F C) Z (J n) hZ (hJ n) hZ0 hZt (hJ0 n) (hJt n)
  refine ⟨hZ.isClosed.measurableSet, (fun n => (hJ n).isClosed.measurableSet),
    hZ0, hZt, hJ0, hJt, (fun n => (hc n).1), (fun n => (hc n).2.1),
    hZ, hJ, (fun n => (hc n).2.2.1), ?_, v, hv, ?_⟩
  · intro n
    exact (hc n).2.2.2 _
  · intro n
    exact (hj n).2.2.2.1

end PolycyclicRecognition.CartanWordModel

end

end OAI
