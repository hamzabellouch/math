import OAI.Geometry.SurfaceImmersion.Geometry.UniformMetricPathBounds
import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasTensorBounds
import OAI.Geometry.SurfaceImmersion.Geometry.InitialInputBounds

namespace OAI

/-! A fixed C2 budget for starting maps gives one C1 remainder bound in
any fixed primitive atlas, before choosing finite modifications. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance remainderBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance remainderBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance remainderBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance remainderBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance remainderBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance remainderBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem uniform_remainder_C1_bound (g : SmoothMetric M) (r : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 2 D G → B.TensorWeightedBound 1 1 U (g.inner-inducedTensor (r • G)) := by
  obtain ⟨U,hU,hinduced⟩ := A.uniform_induced_tensor_bound (mul_nonneg (abs_nonneg r) hD) 1
  obtain ⟨E,hE,hmetric⟩ := A.exists_tensorWeighted_bound 1 g.contMDiff
  obtain ⟨T,hT,hchange⟩ := A.tensorWeightedBound_change_atlas B 1
  refine ⟨T*(E+U),mul_nonneg hT (add_nonneg hE hU),?_⟩
  intro G hG hbound
  have hscaled := space_smul_contMDiff hG r
  have hmap := A.weightedBound_const_smul hG hbound r
  have hi := hinduced (r • G) hscaled hmap
  have hsmooth := A.inducedTensor_smooth hscaled
  have hneg : A.TensorWeightedBound 1 1 U (-inducedTensor (r • G)) := by
    simpa only [neg_one_smul,abs_neg,abs_one,one_mul] using
      A.tensorWeightedBound_const_smul hsmooth hi (-1)
  have hsum := A.tensorWeightedBound_add g.contMDiff hsmooth.neg_section zero_le_one hmetric hneg
  apply hchange (g.inner-inducedTensor (r • G)) 1 (E+U) zero_lt_one le_rfl
    (add_nonneg hE hU) (g.contMDiff.sub_section hsmooth)
  simpa only [sub_eq_add_neg] using hsum

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
