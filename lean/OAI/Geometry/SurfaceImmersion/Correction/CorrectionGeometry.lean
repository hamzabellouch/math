import OAI.Geometry.SurfaceImmersion.Atlas.MetricGoodPhaseData

namespace OAI

/-! The fixed atlas data used when taking the smooth correction limit. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation

local instance correctionGeometryFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance correctionGeometryFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance correctionGeometryDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance correctionGeometryDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance correctionGeometrySectionNormed (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance correctionGeometrySectionSpace (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

structure CorrectionGeometry (_g : SmoothMetric M) (_F : M → Space) where
  A : SmoothingAtlas M
  outer_locally_one : ∀ i x, x ∈ tsupport (A.weight i) →
    A.outer i =ᶠ[𝓝 x] (fun _ => 1)

namespace MetricGoodPhaseData

abbrev toCorrectionGeometry {g : SmoothMetric M} {F : M → Space}
    (d : MetricGoodPhaseData g F) : CorrectionGeometry g F :=
  ⟨d.A,d.outer_locally_one⟩

instance {g : SmoothMetric M} {F : M → Space} :
    Coe (MetricGoodPhaseData g F) (CorrectionGeometry g F) := ⟨toCorrectionGeometry⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
