import OAI.Geometry.SurfaceImmersion.Geometry.UniformMetricPathBounds
import OAI.Geometry.SurfaceImmersion.Geometry.UniformInitialScale
import OAI.Geometry.SurfaceImmersion.Geometry.UniformStartingFamily

namespace OAI

/-! The initial spherical scale can be fixed before all finite modifications
so that the entire family of induced metrics is small in C1. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance smallStartFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance smallStartFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance smallStartDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance smallStartDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance smallStartSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance smallStartSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_small_scaled_metric (g : SmoothMetric M) {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ F : M → Space, ContMDiff planeModel spaceModel ∞ F →
        A.WeightedBound 1 2 C F →
        A.TensorWeightedBound 1 1 ε (inducedTensor (r • F)) ∧
        ∀ p v, inducedForm (r • F) p v v ≤ (1/2 : ℝ)*g.inner p v v := by
  obtain ⟨E,hE,hbound⟩ := A.uniform_induced_tensor_bound hC 1
  obtain ⟨D,hD,hupper⟩ := A.uniform_induced_metric_upper_bound g hC
  let a := min 1 (min (ε/(E+1)) (1/(2*(D+1))))
  have ha : 0 < a := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  let r := Real.sqrt a
  have hr : 0 < r := Real.sqrt_pos.mpr ha
  have hr2 : r^2 = a := Real.sq_sqrt ha.le
  have hr1 : r ≤ 1 := by
    have : r^2 ≤ 1 := hr2 ▸ min_le_left _ _
    nlinarith
  have hsmall : r^2*E ≤ ε := by
    have hs : r^2 ≤ ε/(E+1) := hr2 ▸ (min_le_right _ _).trans (min_le_left _ _)
    have hh := (le_div_iff₀ (by positivity : 0 < E+1)).mp hs
    nlinarith [sq_nonneg r]
  have hshort : r^2*D ≤ (1/2 : ℝ) := by
    have hs : r^2 ≤ 1/(2*(D+1)) := hr2 ▸ (min_le_right _ _).trans (min_le_right _ _)
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(D+1))).mp hs
    nlinarith [sq_nonneg r]
  refine ⟨r,hr,hr1,?_⟩
  intro F hF hb
  constructor
  · rw [inducedTensor_const_smul hF]
    have hs := A.tensorWeightedBound_const_smul (A.inducedTensor_smooth hF)
      (hbound F hF hb) (r^2)
    intro i
    apply (hs i).mono_const
    simpa only [abs_of_nonneg (sq_nonneg r)] using hsmall
  · intro p v
    have he := congrArg (fun T : ∀ p : M, CovariantTwoTensor p => T p v v)
      (inducedTensor_const_smul hF r)
    change inducedForm (r • F) p v v = r^2*inducedForm F p v v at he
    rw [he]
    have hu := hupper F hF (fun i => (hb i).mono_order (by omega)) p v
    have hg : 0 ≤ g.inner p v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (g.pos p v hv).le
    exact (mul_le_mul_of_nonneg_left hu (sq_nonneg r)).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hshort hg)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
