import OAI.Analysis.CircleDomains.Topology.ExteriorSeparation
import OAI.Analysis.CircleDomains.Selection.ScaledExteriorBounds

namespace OAI

/-!
# One uniform bound for normalized finite circle models

The exterior coefficient estimate controls a physical circle and the
annulus outside it. The compact-exterior separation argument traps all
other image points and every omitted point on its bounded side.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem normalized_model_uniform_bound
    (harea : ExteriorCoefficientAreaTheorem)
    {f fi : Sphere → Sphere} {U V : Set Sphere} (heq : IsSmoothSphereEquivalence f fi U V)
    (hV : IsOpen V) {R : ℝ} (hR : 0 < R)
    (hsource : ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ U)
    (hf : IsConformalOn f ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : IsPrincipalNormalized f) :
    (∀ p ∈ Vᶜ, p ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 (3 * R)) ∧
      ∀ z : ℂ, (z : Sphere) ∈ U → ‖z‖ ≤ 4 * R →
        f (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 (5 * R) := by
  have hinf : OnePoint.infty ∈ U := hsource (by simp)
  have hfinite (z : ℂ) (hz : (z : Sphere) ∈ U) : f (z : Sphere) ≠ OnePoint.infty :=
    heq.finite_forward hinf hnorm.1 hz
  let F : ℂ → ℂ := fun z => finiteCoord (f (z : Sphere))
  have hF : DifferentiableOn ℂ F {z | R < ‖z‖} := by
    intro z hz
    change R < ‖z‖ at hz
    have hzExt : (z : Sphere) ∈ ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ) := by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall,
        dist_zero_right, mem_compl_iff, not_le] using hz
    obtain ⟨_, d, _, hd⟩ := hf z hzExt
    have hzU : (z : Sphere) ∈ U := hsource (by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
        dist_zero_right, mem_compl_iff, not_lt] using hz.le)
    have he : (fun w => chart (f (z : Sphere)) (f (chartSymm (z : Sphere) w))) = F := by
      funext w
      simp only [chart, hfinite z hzU, ite_false, chartSymm_coe_apply, F]
    rw [he, chart_coe_self] at hd
    exact hd.differentiableAt.differentiableWithinAt
  have hFi : InjOn F {z | R < ‖z‖} := by
    intro z hz w hw he
    have hzU : (z : Sphere) ∈ U := hsource (by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
        dist_zero_right, mem_compl_iff, not_lt] using hz.le)
    have hwU : (w : Sphere) ∈ U := hsource (by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
        dist_zero_right, mem_compl_iff, not_lt] using hw.le)
    apply OnePoint.coe_injective
    apply heq.bijOn.injOn hzU hwU
    calc
      f (z : Sphere) = ((F z : ℂ) : Sphere) := (coe_finiteCoord (hfinite z hzU)).symm
      _ = ((F w : ℂ) : Sphere) := congrArg ((↑) : ℂ → Sphere) he
      _ = f (w : Sphere) := coe_finiteCoord (hfinite w hwU)
  have hb : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ R :=
    harea.scaled_exterior_bound hR hF hFi hnorm.2
  have hEU : ((((↑) : ℂ → Sphere) '' Metric.ball 0 (2 * R))ᶜ) ⊆ U := by
    apply Subset.trans _ hsource
    exact compl_subset_compl.mpr (image_mono (Metric.ball_subset_ball (by linarith)))
  have hboundary : ∀ z : ℂ, ‖z‖ = 2 * R →
      f (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 (3 * R) := by
    intro z hz
    have hzU : (z : Sphere) ∈ U := hEU (by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
        dist_zero_right, mem_compl_iff, not_lt] using hz.ge)
    refine ⟨F z, ?_, coe_finiteCoord (hfinite z hzU)⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖F z‖ ≤ ‖F z - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ 3 * R := by linarith [hb z hz.ge]
  have hexterior := sphere_exterior_subset_image heq hV (by linarith : 0 < 2 * R)
    (by positivity : 0 ≤ 3 * R) hEU hnorm.1 hboundary
  constructor
  · intro p hp
    by_contra houtside
    obtain ⟨x, hx, rfl⟩ := hexterior houtside
    exact hp (heq.mapsTo (hEU (compl_subset_compl.mpr
      (image_mono Metric.ball_subset_closedBall) hx)))
  · intro z hzU hzn
    refine ⟨F z, ?_, coe_finiteCoord (hfinite z hzU)⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hz : 2 * R ≤ ‖z‖
    · calc
        ‖F z‖ ≤ ‖F z - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
        _ ≤ 5 * R := by linarith [hb z hz]
    · have hsmall : f (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 (3 * R) := by
        by_contra hout
        obtain ⟨x, hx, hfx⟩ := hexterior hout
        have hxU : x ∈ U := hEU (compl_subset_compl.mpr
          (image_mono Metric.ball_subset_closedBall) hx)
        have hxeq : x = (z : Sphere) := heq.bijOn.injOn hxU hzU hfx
        rw [hxeq] at hx
        have hn : 2 * R < ‖z‖ := by
          simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall,
            dist_zero_right, mem_compl_iff, not_le] using hx
        exact hz hn.le
      obtain ⟨w, hw, hwz⟩ := hsmall
      have he : w = F z := by
        apply OnePoint.coe_injective
        exact hwz.trans (coe_finiteCoord (hfinite z hzU)).symm
      rw [Metric.mem_closedBall, dist_zero_right, he] at hw
      linarith

end CircleDomainRigidity

end

end OAI
