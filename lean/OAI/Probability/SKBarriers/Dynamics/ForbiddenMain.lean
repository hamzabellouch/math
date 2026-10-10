import Mathlib
import OAI.Probability.SKBarriers.Dynamics.ForbiddenDynamics
import OAI.Probability.SKBarriers.Dynamics.IdentityMain

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def forbiddenEndpointError (n : ℕ) : ℝ := Real.exp (-3*levelLogScale n)+48*Real.exp (-8*levelLogScale n)

 theorem forbiddenEndpointError_tendsto : Tendsto forbiddenEndpointError atTop (𝓝 0) := by
  have H := (stretched_exp_decay (by norm_num : (0:ℝ)<3)).add ((stretched_exp_decay (by norm_num : (0:ℝ)<8)).const_mul 48)
  change Tendsto (fun n => Real.exp (-3*levelLogScale n)+48*Real.exp (-8*levelLogScale n)) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using H

 theorem forbidden_main_of_static_gap (β : ℝ) {q a₀ a₁ : ℝ}
    (ha₀ : 0<a₀) (ha : a₀<a₁) (haq : a₁<q)
    (hcov : ∀D : ℝ,0<D → ∃c : ℝ,0<c ∧ ∃C : (n : ℕ) → Set (Disorder n),
      (∀n,MeasurableSet (C n)) ∧ Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
      ∀n J,J∈C n → ∀S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
        finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<Real.exp (-c*levelLogScale n)))<Real.exp (-D*levelLogScale n))
    (hstatic : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (pairStripSet n a₀ a₁) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((4:ℝ)/5))) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧ Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  obtain ⟨c,hc,C,hC,hC1,hcovC⟩ := hcov 3 (by norm_num)
  let V (n : ℕ) : Set (Disorder n) := {J | replicaGibbsMass β J (pairStripSet n a₀ a₁)≤Real.exp (-(c+10)*levelLogScale n)}
  let D (n : ℕ) : Set (Disorder n) := C n ∩ V n
  have hV (n : ℕ) : MeasurableSet (V n) := measurableSet_le (continuous_replicaGibbsMass β _).measurable measurable_const
  have hV1 : Tendsto (fun n => (disorderLaw n).real (V n)) atTop (𝓝 1) := by
    apply high_probability_small_replica β _ (by norm_num [kappa] : kappa<(4:ℝ)/5) 1 (c+10)
    simpa only [one_mul] using hstatic
  have hD (n : ℕ) : MeasurableSet (D n) := (hC n).inter (hV n)
  have hD1 : Tendsto (fun n => (disorderLaw n).real (D n)) atTop (𝓝 1) := high_probability_inter _ _ hV hC1 hV1
  apply main_of_quenched_mixed_bounds β D hD hD1 forbiddenEndpointError
    (fun n => by unfold forbiddenEndpointError; positivity) forbiddenEndpointError_tendsto
  have Hgap : Tendsto (fun n : ℕ => 2/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul 2
  filter_upwards [eventually_gt_atTop (0:ℕ),Hgap.eventually_lt_const (sub_pos.mpr ha),
    site_clock_tail_tendsto.eventually_le_const (by norm_num : (0:ℝ)<1/8)] with n hn hgap htail
  intro J hJ
  have hcovJ := gibbs_coverage_predicate β J q _ _ (hcovC n J hJ.1) (fun _ => True)
  simp only [true_and] at hcovJ
  have H := mixedMass_le_pairStrip hn β J ha₀ haq (Real.exp_pos _) hgap
    (show 0≤levelLogScale n by unfold levelLogScale; positivity) htail hcovJ
  have Hnum := pairStrip_numerical_error (show 0≤levelLogScale n by unfold levelLogScale; positivity) hJ.2
  exact ⟨H.1.trans Hnum,H.2.trans Hnum⟩

end SK.Analytic

end
end

end OAI
