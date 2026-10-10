import Mathlib
import OAI.Probability.SKBarriers.Dynamics.DynamicsMeasurable
import OAI.Probability.SKBarriers.Coverage.HighProbability
import OAI.Probability.SKBarriers.Coverage.CoverageSchedule
import OAI.Probability.SKBarriers.Dynamics.IdentityDynamics

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem site_clock_tail_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-levelLogScale n)) atTop (𝓝 0) := by
  simpa only [pow_one,neg_one_mul,levelLogScale] using
    polynomial_rpow_exp_decay (by norm_num [kappa] : 0<kappa) zero_lt_one 1

 theorem bankEndpointError_nonneg (n : ℕ) : 0≤bankEndpointError n := by
  unfold bankEndpointError
  positivity

 theorem bankEndpointError_tendsto : Tendsto bankEndpointError atTop (𝓝 0) := by
  have H := (((stretched_exp_decay (by norm_num : (0:ℝ)<2)).const_mul 9).add site_clock_tail_tendsto).const_mul 4
  change Tendsto (fun n => 4*(9*Real.exp (-2*levelLogScale n)+(n:ℝ)*Real.exp (-levelLogScale n))) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using H

 theorem identity_main_of_static_locking (β : ℝ) (μ : ProbabilityMeasure ℝ) {t b b' q : ℝ}
    (ht : 0<t) (hb : 0<b) (hpack : 3*t<b^2/2) (hcut : 3*t<b) (hcut' : 2*t<b') (hh : 2*t<q)
    (hcov : ∀D : ℝ,0<D → ∃c : ℝ,0<c ∧ ∃C : (n : ℕ) → Set (Disorder n),
      (∀n,MeasurableSet (C n)) ∧ Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
      ∀n J,J∈C n → ∀S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
        finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<Real.exp (-c*levelLogScale n)))<Real.exp (-D*levelLogScale n))
    (hstatic : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b') ∂disorderLaw n)≤3*Real.exp (-(n:ℝ)^((4:ℝ)/5))) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧ Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  let H : ℕ := ⌈2/b^2⌉₊
  let B : ℕ := H+1
  have hB : 0<B := Nat.succ_pos H
  obtain ⟨c,hc,C,hC,hC1,hcovC⟩ := exists_coverage_schedule β q hcov
  let A := 3*bankPrefix c B+20
  let V (n : ℕ) : Set (Disorder n) := {J | replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b')≤Real.exp (-A*levelLogScale n)}
  let D (n : ℕ) : Set (Disorder n) := finiteGoodEvent C B n ∩ V n
  have hV (n : ℕ) : MeasurableSet (V n) := measurableSet_le (continuous_replicaGibbsMass β _).measurable measurable_const
  have hV1 : Tendsto (fun n => (disorderLaw n).real (V n)) atTop (𝓝 1) :=
    high_probability_small_replica β _ (by norm_num [kappa] : kappa<(4:ℝ)/5) 3 A hstatic
  have hD (n : ℕ) : MeasurableSet (D n) := (finiteGoodEvent_measurable C hC B n).inter (hV n)
  have hD1 : Tendsto (fun n => (disorderLaw n).real (D n)) atTop (𝓝 1) :=
    high_probability_inter _ _ hV (finiteGoodEvent_tendsto C hC hC1 B) hV1
  apply main_of_quenched_mixed_bounds β D hD hD1 bankEndpointError bankEndpointError_nonneg bankEndpointError_tendsto
  have hsmall : Tendsto (fun n => 3*Real.exp (-4*levelLogScale n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (stretched_exp_decay (by norm_num : (0:ℝ)<4)).const_mul 3
  filter_upwards [eventually_gt_atTop (0:ℕ),stretchedLogScale_tendsto.eventually_ge_atTop 5,
    eventually_exp_dominates_linear (bankPrefix c B+5),eventually_exp_dominates_linear (t/8),
    hsmall.eventually_lt_const zero_lt_one,
    greedyScale_eventual hB (show H<B by omega) ht hb le_rfl hpack hcut hcut' hh,
    greedy_count_eventual hB ht] with n hn hL hdom hp hsmalln G hcount
  intro J hJ
  have hcovJ (j : ℕ) (hj : j<B) := hcovC j n J ((finiteGoodEvent_mem C B n J).mp hJ.1 j hj)
  exact identity_quenched_bound hn hB β J μ t b b' q c (fun j => (hc j).le) hcovJ hJ.2 hL
    ((greedy_level_count_bound hB ht n).trans hp) hdom hsmalln G hcount

end SK.Analytic

end
end

end OAI
