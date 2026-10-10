import OAI.Analysis.CircleDomains.Selection.NearExtremalHeight
import OAI.Analysis.CircleDomains.Uniformization.UniformHeightCloseness
import OAI.Analysis.CircleDomains.Topology.HeightLevelContinuum

namespace OAI

/-! Quantitative data proved for the actual nearly extremal height. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

structure ControlledHeight (R d : ℝ) where
  height : C(ℂ, ℝ)
  error₀ : Lp ℝ 2 (volume : Measure EuclideanPlane)
  error₁ : Lp ℝ 2 (volume : Measure EuclideanPlane)
  weak_gradient : DeGiorgi.HasWeakGrad (heightLimitGradient error₀ error₁)
    (height ∘ complexPlaneCoordinates) univ
  error_bound : (∫ p, error₀ p^2+error₁ p^2) ≤ 2*Real.pi*d
  log_bound : ∀ c r, 0 < r → r ≤ 1 → ∀ z ∈ closedBall c r,
    |height c-height z|^2*Real.log (1/r) ≤
      16*Real.pi*(2*(2*Real.pi*d)+2*(volume (ball (0 : EuclideanPlane) (‖c‖+2))).toReal)
  local_bound : ∀ S, 2*R ≤ S → ∀ z ∈ closedBall 0 S, |height z| ≤ S+R
  exterior_bound : ∀ z, 2*R ≤ ‖z‖ → |height z-z.im| ≤ 2*R^2/‖z‖
  approximants : ℕ → ℂ ≃ₜ ℂ
  height_limit : TendstoLocallyUniformly (fun n z => (approximants n z).im) height atTop

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_controlled_height (M : CompactScalarModel G u)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ} (hd : 0 < d)
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    {R : ℝ} (hR : 0 < R)
    (hFR : complexPlaneCoordinates ''
      (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ⊆ ball 0 R) :
    ∃ H : ControlledHeight R d,
      ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
        heightLimitGradient H.error₀ H.error₁ p = 0 := by
  obtain ⟨v, G₀, G₁, φ, hv, hw, hE, hz, hh, hn, hl⟩ :=
    M.exists_near_extremal_height_at_radius hsolver hprincipal hgreen harea hinf hu hs hbound hd hnear hR hFR
  exact ⟨{
    height := v
    error₀ := G₀
    error₁ := G₁
    weak_gradient := hw
    error_bound := hE
    log_bound := hl
    local_bound := fun _ hS => limit_height_local_bound harea φ hv hR hS hh hn
    exterior_bound := limit_height_exterior_bound harea φ hv hR hh hn
    approximants := φ
    height_limit := hv }, hz⟩

end CompactScalarModel

 theorem ControlledHeight.level_continuum {R d : ℝ} (H : ControlledHeight R d)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ C : Set ℂ, IsCompact C ∧ IsConnected C ∧ C.Nontrivial ∧ x ∈ C ∧
      C ⊆ closedBall x r ∧ (∀ y ∈ C, H.height y = H.height x) ∧
      (C ∩ sphere x r).Nonempty :=
  height_level_continuum H.approximants H.height.continuous H.height_limit x hr

end CircleDomainRigidity

end

end OAI
