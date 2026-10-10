import OAI.Geometry.SurfaceImmersion.Geometry.TensorPlaneReconstruction

namespace OAI

/-! The actual chart cutoff whose square converts an unweighted tensor
reading into its atlas coordinate component. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates
open JetPolynomial (Base planeCoordinateIsometry)

local instance weightPlaneFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance weightPlaneFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance weightPlaneDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance weightPlaneDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance weightPlaneSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance weightPlaneSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def chartWeight (i : A.centers) : Base → ℝ :=
  (chart (i : M)).target.indicator (fun x => A.weight i ((chart (i : M)).symm x))

def planeWeight (i : A.centers) : SmallModes.Base → ℝ :=
  A.chartWeight i ∘ planeCoordinateIsometry.symm

lemma tensorPlaneEncode_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    (y : SmallModes.Base) :
    A.tensorPlaneEncode u i y = (A.planeWeight i y)^2 • A.tensorPlaneRead i u y := by
  let x := planeCoordinateIsometry.symm y
  change fiberToThree (A.tensorEncode u x i) = (A.chartWeight i x)^2 • A.tensorChartRead i u x
  by_cases hx : x ∈ (chart (i : M)).target
  · have hp := (chart (i : M)).map_target hx
    have hh := A.tensorEncode_read i u hp
    rw [(chart (i : M)).right_inv hx] at hh
    simpa only [chartWeight, indicator_of_mem hx] using hh
  · simp only [tensorEncode, bundleLocalize, localize, indicator_of_notMem hx, map_zero,
      chartWeight, zero_pow (by decide : 2 ≠ 0), zero_smul]

variable [CompactSpace M]

lemma chartWeight_smooth (i : A.centers) : ContDiff ℝ ∞ (A.chartWeight i) := by
  let K : Set Base := (chart (i : M)) '' tsupport (A.weight i)
  have hK : IsCompact K := (isClosed_tsupport (A.weight i)).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (A.weight_support i))
  have hKU : K ⊆ (chart (i : M)).target := by
    rintro x ⟨p,hp,rfl⟩
    exact (chart (i : M)).map_source (A.weight_support i hp)
  apply contDiff_indicator_of_support (chart (i : M)).open_target hK.isClosed hKU
    ((A.weight_smooth i).comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  intro x hx hnot
  by_contra hz
  exact hnot ⟨(chart (i : M)).symm x,subset_tsupport (A.weight i) hz,(chart (i : M)).right_inv hx⟩

lemma planeWeight_smooth (i : A.centers) : ContDiff ℝ ∞ (A.planeWeight i) :=
  (A.chartWeight_smooth i).comp planeCoordinateIsometry.symm.contDiff

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
