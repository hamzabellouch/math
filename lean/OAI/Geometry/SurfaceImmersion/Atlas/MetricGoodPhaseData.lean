import OAI.Geometry.SurfaceImmersion.Correction.MetricGoodSmoothingAtlas
import OAI.Geometry.SurfaceImmersion.Atlas.GoodQuadraticAtlasPhases

namespace OAI

/-! Actual metric-adapted phase geometry, including all cross-chart
quadratic phases needed by the small-increment construction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation

local instance metricPhaseDataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricPhaseDataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance metricPhaseDataDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricPhaseDataDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricPhaseDataSectionNormed (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricPhaseDataSectionSpace (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

structure MetricGoodPhaseData (g : SmoothMetric M) (F : M → Space) where
  A : SmoothingAtlas M
  Q : A.centers → PhaseBasis
  w : A.centers → Fin 3 → ℝ
  weight_pos : ∀ i j, 0 < w i j
  outer_locally_one : ∀ i x, x ∈ tsupport (A.weight i) →
    A.outer i =ᶠ[𝓝 x] (fun _ => 1)
  immersion : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
    Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
  pure_good : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
    Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j)
  metric_positive : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
    0 < (Q i).Q j (A.tensorPlaneRead i g.inner x)
  quadratic_good : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
    Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
      (phaseDerivative (coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l)) x)

namespace MetricGoodPhaseData
variable [T2Space M]

/-- A metric and an immersion with nonzero coordinate second form
produce all the fixed phase geometry required by the analytic step. -/
theorem nonempty (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (hB : ∀ p, ∃ v w : SmallModes.Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0) :
    Nonempty (MetricGoodPhaseData g F) := by
  obtain ⟨A,P,_,houter,hgeometry⟩ := exists_metric_good_smoothingAtlas g hF hImm hB
  let Q : A.centers → PhaseBasis := fun i => (P (i : M)).phaseBasis
  have hi : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) :=
    fun i x hx => (hgeometry i x hx).1
  have hp : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j) :=
    fun i j x hx => (hgeometry i x hx).2.2.1 j
  obtain ⟨w,hw,hquad⟩ := A.exists_good_quadratic_atlas_phases hF Q houter hi hp
  exact ⟨{
    A := A
    Q := Q
    w := w
    weight_pos := hw
    outer_locally_one := houter
    immersion := hi
    pure_good := hp
    metric_positive := fun i j x hx => (hgeometry i x hx).2.1 j
    quadratic_good := hquad
  }⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
