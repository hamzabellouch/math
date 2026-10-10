import OAI.Geometry.SurfaceImmersion.Correction.GlobalOscillatoryModes
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateQuadraticExpansion
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation

namespace OAI

/-! Every global mode sum has the expected local oscillatory germ on an
active atlas chart. No equality of cutoffs outside that locus is assumed. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma jetChartMap_euclidean (i : A.centers) (X : M → RealModes.RVec 4) :
    A.jetChartMap i (spaceCoordinates.symm ∘ X) = A.vectorChartRead i X := by
  funext x
  change spaceCoordinates (localize (i : M) (A.outer i) (spaceCoordinates.symm ∘ X) x) = _
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [localize,indicator_of_mem hx,Function.comp_apply,map_smul,
      ContinuousLinearEquiv.apply_symm_apply,vectorChartRead]
  · simp only [localize,indicator_of_notMem hx,map_zero,vectorChartRead]

lemma jetChartMap_modes_germ {ι : Type*} [Fintype ι]
    (i : A.centers) (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    {x : Base} (hx : A.chartWeight i x ≠ 0) :
    A.jetChartMap i (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) =ᶠ[𝓝 x]
      (QuadraticMean.sumDisplacement τ
        (fun j => coordinatePhase (A.vectorChartRead i (φ j)))
        (fun j => coordinateAmplitude (A.vectorChartRead i (Z j))) ∘ planeCoordinateIsometry) := by
  have hopen := (A.chartWeight_smooth i).continuous.isOpen_support
  rw [A.jetChartMap_euclidean]
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hys : y ∈ (A.chartWeightCompact i : Set Base) := by
    rw [← A.chartWeight_tsupport i]
    exact subset_tsupport (A.chartWeight i) hy
  change localize (i : M) (A.outer i) (∑ j, surfaceMode τ (φ j) (Z j)) y = _
  rw [localize_sum]
  simp only [Function.comp_apply,QuadraticMean.sumDisplacement,
    QuadraticMean.displacement,coordinatePhase,coordinateAmplitude,
    planeCoordinateIsometry.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact A.vectorChartRead_mode_on_support i τ (φ j) (Z j) hys

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
