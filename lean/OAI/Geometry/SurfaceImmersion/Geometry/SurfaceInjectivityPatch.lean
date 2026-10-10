import OAI.Geometry.SurfaceImmersion.Geometry.ConvexDerivativeInjectivity
import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartTranslationBound

namespace OAI

/-! Fixed coordinate balls with quantitative local injectivity margins. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

structure SurfaceInjectivityPatch (f : M → ProjectionTarget 3) (p : M) where
  radius : ℝ
  radius_pos : 0 < radius
  target : closedBall (chart p p) radius ⊆ (chart p).target
  K : NNReal
  K_pos : 0 < K
  anti : AntilipschitzWith K (fderiv ℝ (f ∘ (chart p).symm) (chart p p))
  bound : ∀ y ∈ closedBall (chart p p) radius,
    ‖fderiv ℝ (f ∘ (chart p).symm) y-fderiv ℝ (f ∘ (chart p).symm) (chart p p)‖ < 1/(4*(K:ℝ))

def SurfaceInjectivityPatch.region {f : M → ProjectionTarget 3} {p : M}
    (P : SurfaceInjectivityPatch f p) : Set M :=
  (chart p).source ∩ (chart p) ⁻¹' ball (chart p p) P.radius

omit [IsManifold planeModel ∞ M] in
lemma SurfaceInjectivityPatch.region_open {f : M → ProjectionTarget 3} {p : M}
    (P : SurfaceInjectivityPatch f p) : IsOpen P.region :=
  (chart p).isOpen_inter_preimage isOpen_ball

omit [IsManifold planeModel ∞ M] in
lemma SurfaceInjectivityPatch.mem_region {f : M → ProjectionTarget 3} {p : M}
    (P : SurfaceInjectivityPatch f p) : p ∈ P.region := by
  exact ⟨by simpa only [chart_source] using mem_chart_source Plane p,
    mem_ball_self P.radius_pos⟩

theorem exists_surface_injectivity_patch {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (p : M) (hi : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    Nonempty (SurfaceInjectivityPatch f p) := by
  have hp : p ∈ (chart p).source := by simpa only [chart_source] using mem_chart_source Plane p
  have hxp := (chart p).map_source hp
  have hI : Function.Injective (fderiv ℝ (f ∘ (chart p).symm) (chart p p)) := by
    rw [fderiv_comp_chart_symm (hf.of_le (by simp)) p hxp,(chart p).left_inv hp]
    exact hi.comp ((chart_mdifferentiable p).symm.mfderiv_injective hxp)
  obtain ⟨K,hK,hL⟩ := (fderiv ℝ (f ∘ (chart p).symm) (chart p p)).toLinearMap.exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hI)
  have hF : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hD := (hF.continuousOn_fderiv_of_isOpen (chart p).open_target (by simp)).continuousAt
    ((chart p).open_target.mem_nhds hxp)
  have hc : ∀ᶠ y in 𝓝 (chart p p),
      ‖fderiv ℝ (f ∘ (chart p).symm) y-fderiv ℝ (f ∘ (chart p).symm) (chart p p)‖ < 1/(4*(K:ℝ)) := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hD) (1/(4*(K:ℝ))) (by positivity)
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((chart p).open_target.mem_nhds hxp) hc)
  refine ⟨⟨r/2,half_pos hr,?_,K,hK,hL,?_⟩⟩
  · intro y hy
    exact (hrb (closedBall_subset_ball (by linarith : r/2 < r) hy)).1
  · intro y hy
    exact (hrb (closedBall_subset_ball (by linarith : r/2 < r) hy)).2

theorem SurfaceInjectivityPatch.injective_of_close {f g : M → ProjectionTarget 3} {p : M}
    (P : SurfaceInjectivityPatch f p)
    (hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g)
    (hclose : ∀ y ∈ closedBall (chart p p) P.radius,
      ‖fderiv ℝ (g ∘ (chart p).symm) y-fderiv ℝ (f ∘ (chart p).symm) y‖ < 1/(4*(P.K:ℝ))) :
    InjOn g P.region := by
  have hG : ContDiffOn ℝ ∞ (g ∘ (chart p).symm) (chart p).target :=
    (hg.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hi : InjOn (g ∘ (chart p).symm) (closedBall (chart p p) P.radius) := by
    apply convex_injective_of_derivative_close P.K_pos P.anti (convex_closedBall _ _)
    · intro x hx
      exact (hG.contDiffAt ((chart p).open_target.mem_nhds (P.target hx))).differentiableAt (by simp)
    · intro x hx
      calc
        _ ≤ ‖fderiv ℝ (g ∘ (chart p).symm) x-fderiv ℝ (f ∘ (chart p).symm) x‖+
            ‖fderiv ℝ (f ∘ (chart p).symm) x-fderiv ℝ (f ∘ (chart p).symm) (chart p p)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 1/(2*(P.K:ℝ)) := by
          have h1 := hclose x hx
          have h2 := P.bound x hx
          have hK : 0 < (P.K:ℝ) := P.K_pos
          have he : 1/(4*(P.K:ℝ))+1/(4*(P.K:ℝ)) = 1/(2*(P.K:ℝ)) := by ring
          linarith
  intro x hx y hy he
  apply (chart p).injOn hx.1 hy.1
  apply hi (ball_subset_closedBall hx.2) (ball_subset_closedBall hy.2)
  simpa only [Function.comp_apply,(chart p).left_inv hx.1,(chart p).left_inv hy.1] using he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
