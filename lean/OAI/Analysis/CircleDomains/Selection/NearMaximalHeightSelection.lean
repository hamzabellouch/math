import OAI.Analysis.CircleDomains.Selection.NearExtremalHeightCloseness
import OAI.Analysis.CircleDomains.Uniformization.ModelUniformBounds

namespace OAI

/-! Select an actual nearly maximal model and its actual controlled height,
with prescribed compact closeness and a prescribed small deficit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_close_model_height
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hne : Nonempty (CompactScalarModel G u))
    {R : ℝ} (hR : 0 < R) (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G)
    {K : Set ℂ} (hK : IsCompact K) {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) :
    ∃ d : ℝ, 0 < d ∧ d < cap ∧ ∃ M : CompactScalarModel G u,
      ∃ H : ControlledHeight (3*R+1) d,
        (∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
          heightLimitGradient H.error₀ H.error₁ p = 0) ∧
        (∀ z ∈ K, |H.height z-z.im| < ε) := by
  have hsf : ∀ z : ℂ, R < ‖z‖ → (z : Sphere) ∈ G := by
    intro z hz
    apply hsource
    rintro ⟨w,hw,he⟩
    have hwz : w = z := OnePoint.coe_injective he
    subst w
    have := mem_ball_zero_iff.mp hw
    linarith
  have hRt : 0 < 3*R+1 := by linarith
  obtain ⟨δ,hδ,hclose⟩ := uniform_near_extremal_height hsolver hprincipal hgreen harea
    hinf hu hs (CompactScalarModel.coefficientSet_bddAbove harea hR hsf) hRt hK hε
  let d := min δ cap / 2
  have hd : 0 < d := half_pos (lt_min hδ hcap)
  have hdδ : d < δ := (half_lt_self (lt_min hδ hcap)).trans_le (min_le_left _ _)
  have hdc : d < cap := (half_lt_self (lt_min hδ hcap)).trans_le (min_le_right _ _)
  obtain ⟨M,hM⟩ := CompactScalarModel.exists_near_maximal hne hd
  have htarget : complexPlaneCoordinates ''
      (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ⊆ ball 0 (3*R+1) := by
    rintro z ⟨x,hx,rfl⟩
    have hx' : (complexPlaneCoordinates x : Sphere) ∉ extendAtInfinity M.function '' G := hx
    have hb := (M.uniform_omitted_and_image_bound harea hG hR hsource).1 _ hx'
    exact mem_ball_zero_iff.mpr (by linarith)
  obtain ⟨H,hHz,hH⟩ := hclose M d hd hdδ hM.le htarget
  exact ⟨d,hd,hdc,M,H,hHz,hH⟩

end CircleDomainRigidity

end

end OAI
