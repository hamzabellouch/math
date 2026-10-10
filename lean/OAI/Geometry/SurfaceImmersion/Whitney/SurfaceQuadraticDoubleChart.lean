import OAI.Geometry.SurfaceImmersion.Whitney.FiniteQuadraticCrosscaps
import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticCrosscapIsolation

namespace OAI

/-! The local double curve is realized in the original surface chart,
including the exact singular point and actual image equalities. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_quadratic_crosscap_chart (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ r : ℝ, 0 < r ∧ closedBall (chart q p) r ⊆ (chart q).target ∧
      (∀ y ∈ ball (chart q p) r,
        F ((chart q).symm y) = centeredSurfaceTaylor φ (chart q p) y) ∧
      (∀ y ∈ ball (chart q p) r,
        (¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F ((chart q).symm y))
          ↔ y = chart q p)) ∧
      (∀ x ∈ ball (chart q p) r, ∀ y ∈ ball (chart q p) r, x ≠ y →
        (F ((chart q).symm x) = F ((chart q).symm y) ↔
          ∃ s : ℝ, s ≠ 0 ∧ x = chart q p+s • tangentRay b t ∧
            y = chart q p-s • tangentRay b t)) := by
  let a := chart q p
  let Q := centeredSurfaceTaylor φ a
  have haT : a ∈ (chart q).target := (chart q).map_source hp
  have ht : Tendsto (chart q).symm (𝓝 a) (𝓝 p) := by
    have hc := (chart q).symm.continuousAt haT
    simpa only [a,(chart q).left_inv hp] using hc.tendsto
  have hfml : ∀ᶠ y in 𝓝 a, y ∈ (chart q).target ∧ F ((chart q).symm y) = Q y := by
    filter_upwards [he.comp_tendsto ht,(chart q).open_target.mem_nhds haT] with y hy hyT
    exact ⟨hyT,by simpa only [Function.comp_apply,(chart q).right_inv hyT] using hy⟩
  obtain ⟨s,hs,hsub⟩ := nhds_basis_closedBall.mem_iff.mp hfml
  obtain ⟨r₀,hr₀,hiso⟩ := centeredSurfaceTaylor_isolated_crosscap hφ a b t hz hreg
  obtain ⟨r₁,hr₁,hdouble⟩ := quadratic_crosscap_double_points hφ a b t hz hreg
  let r := min s (min r₀ r₁)
  have hr : 0 < r := lt_min hs (lt_min hr₀ hr₁)
  have hrs : r ≤ s := min_le_left _ _
  have hrr₀ : r ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₁ : r ≤ r₁ := (min_le_right _ _).trans (min_le_right _ _)
  have hformula (y : Base) (hy : y ∈ ball a r) : F ((chart q).symm y) = Q y :=
    (hsub (closedBall_subset_closedBall hrs (ball_subset_closedBall hy))).2
  refine ⟨r,hr,fun y hy => (hsub (closedBall_subset_closedBall hrs hy)).1,hformula,?_,?_⟩
  · intro y hy
    have hyT := (hsub (closedBall_subset_closedBall hrs (ball_subset_closedBall hy))).1
    have hsource := (chart q).map_target hyT
    have hmodel : F =ᶠ[𝓝 ((chart q).symm y)] Q ∘ chart q := by
      have ho := (chart q).isOpen_inter_preimage (isOpen_ball : IsOpen (ball a r))
      have hm : (chart q).symm y ∈ (chart q).source ∩ (chart q) ⁻¹' ball a r := by
        exact ⟨hsource,by simpa only [mem_preimage,(chart q).right_inv hyT] using hy⟩
      filter_upwards [ho.mem_nhds hm] with z hz'
      have hh := hformula (chart q z) hz'.2
      simpa only [Function.comp_apply,(chart q).left_inv hz'.1] using hh
    have hi := chart_germ_immersion_iff q hsource (centeredSurfaceTaylor_smooth φ a) hmodel
    rw [(chart q).right_inv hyT] at hi
    exact hi.not.trans (hiso y (ball_subset_ball hrr₀ hy))
  · intro x hx y hy hne
    rw [hformula x hx,hformula y hy]
    exact hdouble x (ball_subset_ball hrr₁ hx) y (ball_subset_ball hrr₁ hy) hne

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
