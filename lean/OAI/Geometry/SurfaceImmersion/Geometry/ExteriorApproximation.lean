import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitiveGeometry
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds

namespace OAI

/-! The comparison map retained by the exact primitive theorem gives
actual exterior C2 proximity to the original immersion. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_read_C2_bound (j : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight j), A.outer j =ᶠ[𝓝 x] (fun _ => 1)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → ContMDiff planeModel spaceModel ∞ W →
      ∀ b c : ℝ, 0 ≤ b → 0 ≤ c →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ p ∈ tsupport (A.weight j), V =ᶠ[𝓝 p] G →
      ∀ m ≤ 2,
      ‖iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead j (W-F))
        (planeCoordinateIsometry (chart (j : M) p))‖ ≤ D*(b+c) := by
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) j 2
  refine ⟨‖spaceCoordinates.toContinuousLinearMap‖*D,
    mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F G V W hF hG hV hW b c hb hc hGF hWV p hp he m hm
  let H := (G-F)+(W-V)
  have hH : ContMDiff planeModel spaceModel ∞ H := (hG.sub hF).add (hW.sub hV)
  have hbound : A.WeightedBound 1 2 (b+c) H := by
    intro i
    change WeightedEstimates.WeightedBound univ 1 2 (b+c)
      (localize (i : M) (A.weight i) ((G-F)+(W-V)))
    rw [localize_add]
    exact WeightedEstimates.WeightedBound.add uniqueDiffOn_univ zero_le_one
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (hG.sub hF)).contDiffOn
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (hW.sub hV)).contDiffOn
      (hGF i) (hWV i)
  have hread := hd H 1 (b+c) zero_lt_one le_rfl (add_nonneg hb hc) hH hbound
  have hlinear := hread.linear uniqueDiffOn_univ zero_le_one
    (A.vectorPlaneRead_smooth j hH).contDiffOn spaceCoordinates.toContinuousLinearMap
  change WeightedEstimates.WeightedBound univ 1 2 _
    (spaceCoordinates ∘ A.vectorPlaneRead j H) at hlinear
  have he' : W-F =ᶠ[𝓝 p] H := by
    filter_upwards [he] with x hx
    dsimp [H]
    rw [hx]
    abel
  have hjet := (A.planeRead_eventuallyEq_on_weight he' j hp houter).iteratedFDeriv ℝ m
  rw [hjet.eq_of_nhds]
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,mul_assoc] using
    hlinear m hm (planeCoordinateIsometry (chart (j : M) p)) (mem_univ _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
