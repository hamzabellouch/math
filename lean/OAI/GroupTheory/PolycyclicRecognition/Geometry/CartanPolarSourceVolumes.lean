import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledOffsetRates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeSourceCellVolumes

namespace OAI

/-! # Source volume and tile count with the same actual exponent -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set Metric
open scoped Manifold BigOperators

variable {EG G W EI I Q : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (K : ProperCone ℝ (StrongDual ℝ W))
  [NormedAddCommGroup EI] [NormedSpace ℝ EI] [FiniteDimensional ℝ EI]
  [Group I] [TopologicalSpace I] [ChartedSpace EI I] [LieGroup (𝓘(ℝ, EI)) ⊤ I]
  [SimplyConnectedSpace I] [T2Space I] [MeasurableSpace I] [BorelSpace I]
  [Group Q] [TopologicalSpace Q] [MeasurableSpace Q]

local notation "C" => heightConePreimage T eW K

omit F in
/-- The source ideal exponent equals the ambient template exponent at the
actual first radius. This is the equality needed for volume cancellation. -/
theorem polar_source_kernel_exponent
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ j, M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0))
      (β.val j)) = (M.supportIn T hunimod eW).templateSupport
        (normalizedPolarTemplates K ε 0) := by
  change (∑ j, M.coneIdealWordCost C
    ((M.supportIn T hunimod eW).weightSupport
      ((fun x : W => (2 * ε / 3) • x) '' conePolarTemplate K)) (β.val j)) = _
  rw [M.sum_polar_ideal_cost_smul T hunimod eW K β (by positivity)]
  exact (M.polar_templateSupport_eq T hunimod eW K bN bI β hβ (by positivity)).symm

/-- The positive source coefficient and the exact source exponential rate
are derived for the kernel measure actually used in the source count. -/
theorem polar_source_cell_volumes
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput EI I)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (π : F.N.carrier →* Q) (ι : I →* F.N.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (π.ker : Set F.N.carrier))
    (μI : Measure I) [μI.IsHaarMeasure]
    (μQ : Measure Q) [μQ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μQ]
    {d : ℕ} (eQ : (Fin d → ℝ) ≃ₜ Q)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    {ε : ℝ} (hε : 0 ≤ ε) (scale : ℕ → ℝ) :
    let ZQ := eQ '' closedBall (0 : Fin d → ℝ) 1
    let J := fun n => kernelRealization π ι hι hrange '' M.coneIdealBox C
      (ExpI ∘ eI) ((M.supportIn T hunimod eW).weightSupport
        (normalizedPolarTemplates K ε 0)) β (scale n) 1
    let μK := Measure.map (kernelRealization π ι hι hrange) μI
    IsCompact ZQ ∧ μQ ZQ ≠ 0 ∧ μQ ZQ ≠ ⊤ ∧
      ∃ v : ℝ, 0 < v ∧ ∀ n,
        IsCompact (J n) ∧ μK (J n) ≠ 0 ∧ μK (J n) ≠ ⊤ ∧
        (μK (J n)).toReal = v * Real.exp (scale n *
          (M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0)) ∧
        IsCompact (ZQ ×ˢ J n) := by
  dsimp only
  obtain ⟨hZ, hz, ht, v, hv, hJ⟩ := M.cone_source_cell_volumes C
    eI ExpI hExpI haarI chartI hchartI π ι hι hrange μI μQ eQ
    ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0)) β scale
  refine ⟨hZ, hz, ht, v, hv, ?_⟩
  intro n
  obtain ⟨hc, h0, htop, he, hp⟩ := hJ n
  refine ⟨hc, h0, htop, ?_, hp⟩
  rw [M.polar_source_kernel_exponent T hunimod eW K bN bI β hβ hε] at he
  exact he

end PolycyclicRecognition.CartanWordModel

end

end OAI
