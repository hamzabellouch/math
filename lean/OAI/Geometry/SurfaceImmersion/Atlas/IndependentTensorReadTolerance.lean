import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasTensorBounds
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteScalarBounds

namespace OAI

/-! Small background-atlas norm gives small tensor readings in each
fixed primitive chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance readToleranceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance readToleranceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance readToleranceDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance readToleranceDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance readToleranceSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance readToleranceSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem tensor_read_tolerance {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ u : ∀ p : M, CovariantTwoTensor p,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      A.TensorWeightedBound 1 0 eps u →
      ∀ (i : B.centers) (y : JetPolynomial.Base), ‖B.tensorChartRead i u y‖ < eta := by
  obtain ⟨D,hD,hchange⟩ := A.tensorWeightedBound_change_atlas B 0
  choose E hE hread using fun i : B.centers => B.tensorChartRead_bound i 0
  obtain ⟨eps,heps,hle⟩ := finite_positive_lower (fun i : B.centers =>
    (show 0 < eta/(2*(E i*D+1)) by have := hE i; positivity))
  refine ⟨eps,heps,?_⟩
  intro u hu hb i y
  have hB := hchange u 1 eps zero_lt_one le_rfl heps.le hu hb
  have hh := (hread i u 1 (D*eps) zero_lt_one le_rfl (mul_nonneg hD heps.le) hu hB).norm_le
    (mem_univ y)
  have hEi := hE i
  have hd := (le_div_iff₀ (show 0 < 2*(E i*D+1) by positivity)).mp (hle i)
  have he : 0 ≤ E i*D := mul_nonneg (hE i) hD
  have hstrict : E i*(D*eps) < eta := by nlinarith
  exact hh.trans_lt hstrict

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
