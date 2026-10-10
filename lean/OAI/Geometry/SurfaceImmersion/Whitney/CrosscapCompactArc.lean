import OAI.Geometry.SurfaceImmersion.Whitney.PreparedDoubleCurve
import OAI.Geometry.SurfaceImmersion.Geometry.UnorderedPairMap

namespace OAI

/-! An embedded compact half-arc in the actual unordered double curve,
with its endpoint at the prepared crosscap. -/
noncomputable section
open Set Filter Metric Manifold Topology
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem crosscap_compact_half_arc (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ γ : Icc (0 : ℝ) δ → UnorderedSurfacePairs M,
      IsClosedEmbedding γ ∧
      (∀ s, γ s = unorderedPair
        ((chart q).symm (chart q p+(s:ℝ) • tangentRay b t),
          (chart q).symm (chart q p-(s:ℝ) • tangentRay b t))) ∧
      γ ⟨0,le_rfl,hδ.le⟩ = unorderedPair (p,p) ∧
      ∀ s, γ s ∈ compactifiedDoubleCurve F := by
  obtain ⟨r,hr,hball,hformula,_hsing,_hdouble⟩ :=
    surface_quadratic_crosscap_chart F p q hp hφ he b t hz hreg
  let a := chart q p
  let w := tangentRay b t
  let δ := r/(2*(‖w‖+1))
  have hden : 0 < 2*(‖w‖+1) := by positivity
  have hδ : 0 < δ := div_pos hr hden
  have hδr : δ*‖w‖ < r := by
    have heq : δ*(2*(‖w‖+1)) = r := div_mul_cancel₀ r hden.ne'
    have hlt : ‖w‖ < 2*(‖w‖+1) := by linarith [norm_nonneg w]
    exact (mul_lt_mul_of_pos_left hlt hδ).trans_eq heq
  have hcoords (s : Icc (0 : ℝ) δ) : a+(s:ℝ) • w ∈ ball a r ∧ a-(s:ℝ) • w ∈ ball a r := by
    have hn : ‖(s:ℝ) • w‖ < r := by
      rw [norm_smul,Real.norm_of_nonneg s.property.1]
      exact (mul_le_mul_of_nonneg_right s.property.2 (norm_nonneg w)).trans_lt hδr
    constructor
    · simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hn
    · simpa only [mem_ball,dist_eq_norm,sub_sub_cancel_left,norm_neg] using hn
  let γ : Icc (0 : ℝ) δ → UnorderedSurfacePairs M := fun s =>
    unorderedPair ((chart q).symm (a+(s:ℝ) • w),(chart q).symm (a-(s:ℝ) • w))
  have hγcont : Continuous γ := by
    apply unorderedPair_continuous.comp
    apply Continuous.prodMk
    · apply continuous_iff_continuousAt.mpr
      intro s
      have hc : ContinuousAt (fun u : Icc (0 : ℝ) δ => a+(u:ℝ) • w) s := by fun_prop
      exact ContinuousAt.comp (f := fun u : Icc (0 : ℝ) δ => a+(u:ℝ) • w)
        ((chart q).symm.continuousAt (hball (ball_subset_closedBall (hcoords s).1))) hc
    · apply continuous_iff_continuousAt.mpr
      intro s
      have hc : ContinuousAt (fun u : Icc (0 : ℝ) δ => a-(u:ℝ) • w) s := by fun_prop
      exact ContinuousAt.comp (f := fun u : Icc (0 : ℝ) δ => a-(u:ℝ) • w)
        ((chart q).symm.continuousAt (hball (ball_subset_closedBall (hcoords s).2))) hc
  have hchart (s : Icc (0 : ℝ) δ) :
      unorderedPairMap (chart q) (γ s) = unorderedLinePair a w s := by
    change unorderedPair (chart q ((chart q).symm (a+(s:ℝ) • w)),
      chart q ((chart q).symm (a-(s:ℝ) • w))) = _
    rw [(chart q).right_inv (hball (ball_subset_closedBall (hcoords s).1)),
      (chart q).right_inv (hball (ball_subset_closedBall (hcoords s).2))]
    rfl
  have hγinj : Function.Injective γ := by
    intro s u hsu
    apply Subtype.ext
    apply unorderedLinePair_injOn_nonneg a w (tangentRay_ne_zero b t) s.property.1 u.property.1
    rw [← hchart s,← hchart u,hsu]
  refine ⟨δ,hδ,γ,hγcont.isClosedEmbedding hγinj,(fun _ => rfl),?_,?_⟩
  · simp [γ,a,(chart q).left_inv hp]
  · intro s
    by_cases hs : (s:ℝ) = 0
    · have hγs : γ s = unorderedPair (p,p) := by simp [γ,hs,a,(chart q).left_inv hp]
      rw [hγs,compactifiedDoubleCurve_diagonal]
      exact crosscap_diagonal_mem_closure F p q hp hφ he b t hz hreg
    · have hsp := (hcoords s).1
      have hsm := (hcoords s).2
      have hneq : (chart q).symm (a+(s:ℝ) • w) ≠ (chart q).symm (a-(s:ℝ) • w) := by
        intro hsame
        have hcoord := (chart q).symm.injOn (hball (ball_subset_closedBall hsp))
          (hball (ball_subset_closedBall hsm)) hsame
        have htwo : (2 : ℝ) • ((s:ℝ) • w) = 0 := by
          calc
            _ = (a+(s:ℝ) • w)-(a-(s:ℝ) • w) := by module
            _ = 0 := sub_eq_zero.mpr hcoord
        have hsw : (s:ℝ) • w = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
        exact hs ((smul_eq_zero.mp hsw).resolve_right (tangentRay_ne_zero b t))
      have hEq : F ((chart q).symm (a+(s:ℝ) • w)) = F ((chart q).symm (a-(s:ℝ) • w)) := by
        rw [hformula _ hsp,hformula _ hsm]
        apply (centeredSurfaceTaylor_reflected_eq_iff hφ a _).mpr
        rw [map_smul]
        change (s:ℝ) • surfaceDirection φ b (a,t) = 0
        rw [hz,smul_zero]
      exact ⟨_,subset_closure ⟨hneq,hEq⟩,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
