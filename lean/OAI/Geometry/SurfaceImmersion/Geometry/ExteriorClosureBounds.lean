import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorClosureJets
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds

namespace OAI

/-! Extend the actual exterior C2 estimate through the boundary by continuity
of every coordinate jet. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_read_C2_bound_closure (j : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → ContMDiff planeModel spaceModel ∞ W →
      ∀ b c : ℝ, 0 ≤ b → 0 ≤ c →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ q ∈ O, V =ᶠ[𝓝 q] G) →
      ∀ p ∈ closure O, p ∈ tsupport (A.weight j) →
      ∀ m ≤ 2,
      ‖iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead j (W-F))
        (planeCoordinateIsometry (chart (j : M) p))‖ ≤ D*(b+c) := by
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) j 2
  refine ⟨‖spaceCoordinates.toContinuousLinearMap‖*D,
    mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F G V W hF hG hV hW b c hb hc hGF hWV O hext p hpO hp m hm
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
  have he' : ∀ q ∈ O, W-F =ᶠ[𝓝 q] H := by
    intro q hq
    filter_upwards [hext q hq] with x hx
    dsimp [H]
    rw [hx]
    abel
  have hjet := A.planeRead_jets_eq_on_exterior_closure (hW.sub hF) hH he' j m
    p hpO (A.weight_support j hp)
  change iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead j (W-F))
    (planeCoordinateIsometry (chart (j : M) p)) = _ at hjet
  rw [hjet]
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,mul_assoc] using
    hlinear m hm (planeCoordinateIsometry (chart (j : M) p)) (mem_univ _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
