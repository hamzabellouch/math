import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceQuadraticDoubleChart
import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticDoubleTransverse
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceRegularPairLocus

namespace OAI

/-! All distinct coincident points in a sufficiently small prepared
crosscap neighborhood have transverse image tangent planes. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem crosscap_transverse_neighborhood (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, ∀ y ∈ U, x ≠ y → (x,y) ∈ regularSurfacePairs F := by
  obtain ⟨r,hr,hrT,hform,_,hdouble⟩ := surface_quadratic_crosscap_chart F p q hp hφ he b t hz hreg
  let U := (chart q).source ∩ (chart q) ⁻¹' ball (chart q p) r
  have hU : IsOpen U := (chart q).isOpen_inter_preimage isOpen_ball
  have hformula : EqOn F ((centeredSurfaceTaylor φ (chart q p)) ∘ chart q) U := by
    intro x hx
    have h := hform (chart q x) hx.2
    simpa only [Function.comp_apply,(chart q).left_inv hx.1] using h
  refine ⟨U,hU,⟨hp,mem_ball_self hr⟩,?_⟩
  intro x hx y hy hxy
  by_cases hne : F x ≠ F y
  · exact Or.inl hne
  right
  have heq : F x = F y := not_not.mp hne
  have hcne : chart q x ≠ chart q y := fun h => hxy ((chart q).injOn hx.1 hy.1 h)
  have hc : F ((chart q).symm (chart q x)) = F ((chart q).symm (chart q y)) := by
    simpa only [(chart q).left_inv hx.1,(chart q).left_inv hy.1] using heq
  obtain ⟨s,hs,hxs,hys⟩ := (hdouble (chart q x) hx.2 (chart q y) hy.2 hcne).mp hc
  apply (surface_pair_coordinate_regular_iff q q hx.1 hy.1
    (centeredSurfaceTaylor_smooth φ (chart q p)) (centeredSurfaceTaylor_smooth φ (chart q p))
    (hformula.eventuallyEq_of_mem (hU.mem_nhds hx))
    (hformula.eventuallyEq_of_mem (hU.mem_nhds hy))).mpr
  change Function.Surjective (fderiv ℝ (quadraticDoubleDifference φ (chart q p)) _)
  rw [hxs,hys]
  exact quadratic_crosscap_double_transverse hφ (chart q p) b t hreg.surjective hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
