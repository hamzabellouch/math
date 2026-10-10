import OAI.Geometry.SurfaceImmersion.Geometry.UniformMetricPathBounds
import OAI.Geometry.SurfaceImmersion.Geometry.InitialInputBounds

namespace OAI

/-! The actual straight metric path has one budget for the whole fixed
scaled starting family, before choosing any finite crossing set. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_scaled_path_bound (g : SmoothMetric M) (r : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 2 D G →
      (∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p)) →
      (∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      A.TensorWeightedBound 1 1 C
        (inducedTensor (r • G)+s • (g.inner-inducedTensor (r • G))) := by
  obtain ⟨C,hC,hbound⟩ := A.uniform_short_path_tensor_bound g (mul_nonneg (abs_nonneg r) hD) 1
  refine ⟨C,hC,?_⟩
  intro G hG hb hI hshort s hs hs1
  have hscaled := space_smul_contMDiff hG r
  have hgb := A.weightedBound_const_smul hG hb r
  have hh := hbound (r • G) hscaled hI hshort hgb s hs hs1
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
