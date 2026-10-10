import OAI.Analysis.CircleDomains.Rigidity.ScalarModelConductivity
import OAI.Analysis.CircleDomains.Rigidity.ConductivityHeightLimit
import OAI.Analysis.CircleDomains.Uniformization.LimitHeightEquicontinuity

namespace OAI

/-! Applying the constructed conductivity sequence to a nearly extremal
retained model. The continuous limit, weak gradient and complementary
zero-gradient statement are conclusions of the construction. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_near_extremal_height_at_radius (M : CompactScalarModel G u)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ} (hd : 0 < d)
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    {R : ℝ} (hR : 0 < R)
    (hFR : complexPlaneCoordinates ''
      (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ⊆ ball 0 R) :
    ∃ (v : C(ℂ, ℝ)) (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
      (φ : ℕ → ℂ ≃ₜ ℂ),
      TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop ∧
      DeGiorgi.HasWeakGrad (heightLimitGradient G₀ G₁) (v ∘ complexPlaneCoordinates) univ ∧
      (∫ p, G₀ p^2+G₁ p^2) ≤ 2*Real.pi*d ∧
      (∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
        heightLimitGradient G₀ G₁ p = 0) ∧
      (∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖}) ∧
      (∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹)) ∧
      (∀ c r, 0 < r → r ≤ 1 → ∀ z ∈ closedBall c r,
        |v c-v z|^2*Real.log (1/r) ≤
          16*Real.pi*(2*(2*Real.pi*d)+2*(volume (ball (0 : EuclideanPlane) (‖c‖+2))).toReal)) := by
  let F := (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ
  have hF : IsCompact F := M.complement_compact hinf
  have H (n : ℕ) := M.near_extremal_conductivity_energy hsolver hprincipal hgreen hinf
    hu hs hbound hnear (n+2) (by omega)
  choose φ D c hc hsys hI hE hFE using H
  have hh (n : ℕ) : DifferentiableOn ℂ (φ n) {z | R < ‖z‖} := by
    apply ((D n).conductivity_holomorphic_off (φ n).continuous hF.isClosed (n+2) (hsys n)).mono
    intro z hz hzF
    have hSz : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hFR hzF
    exact (not_lt_of_ge hz.le) hSz
  have hsmall : Tendsto (fun n => ∫ p in F,
      (D n).imagGradient p 0^2+(D n).imagGradient p 1^2) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => 2*Real.pi*d/((n : ℝ)+1)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*Real.pi*d)
      simpa only [mul_one_div, mul_zero] using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    · intro n
      exact integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    · intro n
      have he : (((n+2 : ℕ) : ℝ)-1) = (n : ℝ)+1 := by push_cast; ring
      simpa only [he] using hFE n
  obtain ⟨v, G₀, G₁, s, _hs, hv, hw, he, hz⟩ := exists_conductivity_height_limit harea φ D
    (by positivity : 0 ≤ 2*Real.pi*d) hR hI hE hh (fun n => (hc n).bigO) hF hsmall
  refine ⟨v, G₀, G₁, φ ∘ s, hv, hw, he, hz, fun n => hh (s n),
    fun n => (hc (s n)).bigO, ?_⟩
  intro c r hr hr1 z hz
  exact limit_height_log_bound (φ ∘ s) (fun n => D (s n)) hv
    (fun n => hI (s n)) (fun n => hE (s n)) c hr hr1
    (T := ‖c‖+2) (by linarith) (mem_closedBall_self hr.le) hz

 theorem exists_near_extremal_height (M : CompactScalarModel G u)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ} (hd : 0 < d)
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re) :
    ∃ (v : C(ℂ, ℝ)) (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
      (φ : ℕ → ℂ ≃ₜ ℂ),
      TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop ∧
      DeGiorgi.HasWeakGrad (heightLimitGradient G₀ G₁) (v ∘ complexPlaneCoordinates) univ ∧
      (∫ p, G₀ p^2+G₁ p^2) ≤ 2*Real.pi*d ∧
      (∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
        heightLimitGradient G₀ G₁ p = 0) := by
  obtain ⟨S, hS⟩ := ((M.complement_compact hinf).image
    complexPlaneCoordinates.continuous).isBounded.subset_ball 0
  obtain ⟨v, G₀, G₁, φ, hv, hw, he, hz, _, _, _⟩ :=
    M.exists_near_extremal_height_at_radius hsolver hprincipal hgreen harea hinf hu hs hbound hd hnear
      (R := max S 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      (hS.trans (ball_subset_ball (le_max_left _ _)))
  exact ⟨v, G₀, G₁, φ, hv, hw, he, hz⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
