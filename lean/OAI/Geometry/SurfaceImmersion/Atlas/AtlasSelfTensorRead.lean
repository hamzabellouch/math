import OAI.Geometry.SurfaceImmersion.Correction.AtlasMetricLocalModel
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasTensorTransition

namespace OAI

/-! A tensor restored in a chart reads back exactly where its outer cutoff is one. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
local instance selfReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance selfReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance selfReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance selfReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance selfReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance selfReadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorChartRead_restore_self (i : A.centers) (f : Base → PhaseMean.Tensor)
    {x : Base} (hx : x ∈ (chart (i : M)).target)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    A.tensorChartRead i (A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (f y))) x = f x := by
  have hb := A.tensorTriv_domain i ((chart (i : M)).map_target hx)
  change fiberToThree (localize (i : M) (A.outer i)
    (A.bundleComponent A.tensorTriv i (A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (f y)))) x) = _
  rw [localize,indicator_of_mem hx]
  simp only [ho,one_pow,one_smul,bundleComponent,bundleRestore,
    (chart (i : M)).right_inv hx]
  rw [(A.tensorTriv i).continuousLinearMapAt_symmL hb,fiberToThree_fromThree]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
