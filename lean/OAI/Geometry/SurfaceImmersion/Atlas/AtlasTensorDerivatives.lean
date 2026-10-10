import OAI.Geometry.SurfaceImmersion.Geometry.TensorRestoreFinite
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! Differentiation in a real parameter commutes with the actual finite
atlas restoration and chart reading. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base planeCoordinateIsometry)
open PhaseMean
local instance tensorDerivativeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorDerivativeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance tensorDerivativeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance tensorDerivativeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance tensorDerivativeSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorDerivativeSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorPlaneRestore_hasDerivAt
    {f : ℝ → A.centers → SmallModes.Base → Tensor}
    {f' : A.centers → SmallModes.Base → Tensor} {s : ℝ} (p : M)
    (hf : ∀ i, HasDerivAt (fun r => f r i (planeCoordinateIsometry (chart (i : M) p)))
      (f' i (planeCoordinateIsometry (chart (i : M) p))) s) :
    HasDerivAt (fun r => A.tensorPlaneRestore (f r) p) (A.tensorPlaneRestore f' p) s := by
  have hi (i : A.centers) :=
    (((A.tensorTriv i).symmL ℝ p).hasFDerivAt.comp_hasDerivAt s
      (fiberFromThree.hasFDerivAt.comp_hasDerivAt s (hf i))).const_smul (A.outer i p)
  exact HasDerivAt.fun_sum (fun i _ => hi i)

lemma tensorChartRead_hasDerivAt
    {f : ℝ → ∀ p : M, CovariantTwoTensor p}
    {f' : ∀ p : M, CovariantTwoTensor p} {s : ℝ} (i : A.centers) (x : Base)
    (hf : HasDerivAt (fun r => f r ((chart (i : M)).symm x))
      (f' ((chart (i : M)).symm x)) s) :
    HasDerivAt (fun r => A.tensorChartRead i (f r) x) (A.tensorChartRead i f' x) s := by
  by_cases hx : x ∈ (chart (i : M)).target
  · have hc := (((A.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm x)).hasFDerivAt).comp_hasDerivAt s hf
    have h := fiberToThree.hasFDerivAt.comp_hasDerivAt s
      (hc.const_smul ((A.outer i ((chart (i : M)).symm x))^2))
    simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_mem hx,bundleComponent]
    convert h using 1
    funext r
    rfl
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_notMem hx,map_zero]
    exact hasDerivAt_const s 0

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
