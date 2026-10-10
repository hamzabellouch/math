import OAI.Analysis.CircleDomains.Selection.PrincipalExteriorGerm
import OAI.Analysis.CircleDomains.Selection.PrincipalQuadrantMean

namespace OAI

/-! The actual principal inverse germ gives the exact outer-circle flux
for every sufficiently large radius. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def principalInverseMean (F : ℂ → ℂ) (w : ℂ) : ℂ :=
    1+w*invertedPrincipalRemainder F w

 theorem principalInverseMean_eq {F : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    principalInverseMean F z⁻¹ = z⁻¹*F z := by
  simp only [principalInverseMean,invertedPrincipalRemainder,
    Function.update_of_ne (inv_ne_zero hz),inv_inv]
  field_simp
  ring

 theorem eventually_principal_quadrantFlux {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (hnorm : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) :
    ∃ R₀ > 0, ∀ R ≥ R₀, quadrantFlux F 0 R = 2*Real.pi*R^2 := by
  have hH : AnalyticAt ℂ (principalInverseMean F) 0 :=
    analyticAt_const.add (analyticAt_id.mul (invertedPrincipalRemainder_analytic hF hnorm))
  obtain ⟨δ,hδ,hδH⟩ := hH.exists_ball_analyticOnNhd
  refine ⟨max 1 (δ⁻¹+1),lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro R hR
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  have hRδ : δ⁻¹ < R := by have := (le_max_right 1 (δ⁻¹+1)).trans hR; linarith
  have hinv : R⁻¹ < δ := (inv_lt_comm₀ hRp hδ).mpr hRδ
  have hA : AnalyticOnNhd ℂ (principalInverseMean F) (closedBall 0 R⁻¹) :=
    hδH.mono (closedBall_subset_ball hinv)
  have hc := hA.continuousOn
  have hd : DiffContOnCl ℂ (principalInverseMean F) (ball 0 |R⁻¹|) := by
    rw [abs_of_pos (inv_pos.mpr hRp)]
    exact DiffContOnCl.mk_ball (hA.differentiableOn.mono ball_subset_closedBall) hc
  have hm : Real.circleAverage (principalInverseMean F) 0 R⁻¹ = 1 := by
    simpa only [principalInverseMean,zero_mul,add_zero] using hd.circleAverage
  exact principal_quadrantFlux_of_inverse_mean hRp hc hm (fun _ hz => principalInverseMean_eq hz)

end CircleDomainRigidity

end

end OAI
