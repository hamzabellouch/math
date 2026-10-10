import OAI.Geometry.SurfaceImmersion.Correction.GoodSmoothingAtlas
import OAI.Geometry.SurfaceImmersion.Atlas.MetricAtlasReference

namespace OAI

/-! A smooth metric supplies the positive reference coefficients of an
actual subordinate good-phase smoothing atlas. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial.Perturbation (modeSupport)

local instance metricGoodFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricGoodFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

local instance metricGoodDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricGoodDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricGoodSectionNormed (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricGoodSectionSpace (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

/-- The actual metric, local immersion and nonzero second fundamental
form determine an atlas with positive coefficients and good pure and
same-chart mixed directions on every compact weight support. -/
theorem exists_metric_good_smoothingAtlas (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (hB : ∀ p, ∃ v w : SmallModes.Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0) :
    ∃ (A : SmoothingAtlas M)
      (P : ∀ p, PhasePatch F (coordinateMetric g p) p),
      (∀ i : A.centers, tsupport (A.weight i) ⊆ (P (i : M)).V) ∧
      (∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1)) ∧
      ∀ (i : A.centers) (x : SmallModes.Base),
        x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ∧
        (∀ j, 0 < (P (i : M)).phaseBasis.Q j (A.tensorPlaneRead i g.inner x)) ∧
        (∀ j, Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          ((P (i : M)).phaseBasis.ξ j)) ∧
        (∀ j k, j ≠ k →
          Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
            ((P (i : M)).phaseBasis.ξ j + (P (i : M)).phaseBasis.ξ k) ∧
          Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
            ((P (i : M)).phaseBasis.ξ j - (P (i : M)).phaseBasis.ξ k)) := by
  obtain ⟨A,P,hsub,houter,hgood⟩ := exists_good_smoothingAtlas hF hImm hB
    (coordinateMetric g) (coordinateMetric_continuousAt_center g)
    (fun p => (coordinateMetric_positive_center g p).1)
    (fun p => (coordinateMetric_positive_center g p).2)
  refine ⟨A,P,hsub,houter,?_⟩
  intro i x hx
  obtain ⟨hi,hpos,hpure,hmixed⟩ := hgood i x hx
  refine ⟨hi,?_,hpure,hmixed⟩
  intro j
  rw [A.tensorPlaneRead_metric g i hx]
  exact hpos j

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
