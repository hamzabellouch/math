import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarSourceCells
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledOffsetRates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledSourceCell

namespace OAI

/-! # The source count and source volume with one common exponent -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


local notation "C" => heightConePreimage T eW K


variable {EI : Type*} [NormedAddCommGroup EI] [NormedSpace ℝ EI]
  [FiniteDimensional ℝ EI] [ChartedSpace EI I] [LieGroup (𝓘(ℝ, EI)) ⊤ I]
  [SimplyConnectedSpace I] [T2Space I]

omit [IsTopologicalGroup I] [SecondCountableTopology I] in
/-- The actual source cell volume and counted partition use precisely the
source-minus-target exponent required by the offset comparison. -/
theorem PolarTiledSamplerData.source_count_volume_bounds
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput EI I)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (πQ : F.N.carrier →* Q.carrier) (ι : I →* F.N.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    (R : ℝ) (scale : ℕ → ℝ) (φ : ℕ → I ≃ₜ* I)
    (D : M.PolarTiledSamplerData T F hunimod eW K (ExpI ∘ eI) ι bN ε β R scale φ)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (μI : Measure I) [μI.IsHaarMeasure]
    (μQ : Measure Q.carrier) [μQ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μQ]
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (bI' : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    (β' : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
    (hβ' : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bI'
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' normalizedPolarTemplates K ε 2)) β') :
    let Z := TiledProbeChainData.sourceQuotientCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
      (ExpI := ExpI ∘ eI) (bN := bN) (E := normalizedPolarTemplates K ε)
      (β := fun _ => β) (ambient := D.ambient)
      (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
      (scale := scale) (φ := φ) (ι := ι) (tiles := D.tiles) (anchor := D.anchor)
      (D := D.chain) (Q := Q) (chartQ := chartQ)
    let J := fun n => TiledProbeChainData.sourceKernelCell (T := T) (M := M) (F := F)
      (hunimod := hunimod) (eW := eW) («C» := C) (ExpI := ExpI ∘ eI)
      (E := normalizedPolarTemplates K ε) (β := fun _ => β) (scale := scale)
      (ι := ι) (Q := Q) (πQ := πQ) (hι := hι) (hrange := hrange) n
    let μK := Measure.map (kernelRealization πQ ι hι hrange) μI
    IsCompact Z ∧ μQ Z ≠ 0 ∧ μQ Z ≠ ⊤ ∧
      ∃ v : ℝ, 0 < v ∧ ∀ n,
        IsCompact (J n) ∧ μK (J n) ≠ 0 ∧ μK (J n) ≠ ⊤ ∧
        (μK (J n)).toReal = v * Real.exp (scale n *
          (M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0)) ∧
        IsCompact (Z ×ˢ J n) ∧
        (D.tiles n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) * Real.exp (scale n *
          ((M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0) -
            ∑ j, M.coneIdealWordCost
              (heightConePreimage T eW (transformedPolarCone K A.val))
              ((M.supportIn T hunimod eW).weightSupport
                (A.val '' normalizedPolarTemplates K ε 2)) (β'.val j))) := by
  obtain ⟨hZ, hZ0, hZt, v, hv, hj⟩ :=
    PolarTiledSamplerData.source_cell_volumes T M F hunimod eW K eI ExpI hExpI haarI chartI hchartI
      Q πQ ι hι hrange bN bI hε.le β hβ R scale φ D chartQ μI μQ
  refine ⟨hZ, hZ0, hZt, v, hv, ?_⟩
  intro n
  obtain ⟨hJ, hJ0, hJt, hvol, hprod⟩ := hj n
  exact ⟨hJ, hJ0, hJt, hvol, hprod,
    PolarTiledSamplerData.count_le_offset_rate T M F hunimod eW K (ExpI ∘ eI) ι bN bI hε β hβ
      R scale φ D A bI' β' hβ' n⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
