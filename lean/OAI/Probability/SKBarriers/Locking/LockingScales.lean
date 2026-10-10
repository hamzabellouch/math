import Mathlib
import OAI.Probability.SKBarriers.Dynamics.GreedyNumerics
import OAI.Probability.SKBarriers.Dynamics.BankDynamics

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem signedLockingSet_mono {n : ℕ} {h b c : ℝ} (hbc : b≤c) :
    signedLockingSet n h b⊆signedLockingSet n h c := by
  intro s hs
  obtain ⟨hq,hx,hy,hd⟩ := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq,hx.trans hbc,hy.trans hbc,hd⟩

 theorem signed_small_scale {β h : ℝ} (hβ : 0<β) (hh : 0<h) (hh1 : h≤1) {e : ℝ} (he : 0<e) :
    ∃b : ℝ,0<b ∧ b<e ∧ ∀ᶠ n : ℕ in atTop,
      (∫J,replicaGibbsMass β J (signedLockingSet n h b) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((9:ℝ)/10)) := by
  obtain ⟨b₀,hb₀,H⟩ := signed_fixed_scale_locking hβ hh hh1
  refine ⟨min b₀ (e/2),lt_min hb₀ (half_pos he),(min_le_right _ _).trans_lt (half_lt_self he),?_⟩
  filter_upwards [H] with n hn
  refine (integral_mono (replicaGibbsMass_integrable β _) (replicaGibbsMass_integrable β _)
    (fun J => replicaGibbsMass_mono β J (signedLockingSet_mono (min_le_left b₀ (e/2))))).trans hn

 theorem choose_dynamics_scale {q b b' : ℝ} (hq : 0<q) (hb : 0<b) (hb' : 0<b') :
    ∃t : ℝ,0<t ∧ 3*t<1 ∧ 3*t<b^2/2 ∧ 3*t<b ∧ 2*t<b' ∧ 3*t<q := by
  let a : ℝ := min (1/3) (min (b^2/6) (min (b/3) (min (b'/2) (q/3))))
  have ha : 0<a := by dsimp only [a]; positivity
  refine ⟨a/2,half_pos ha,?_,?_,?_,?_,?_⟩
  all_goals have hat : a/2<a := half_lt_self ha
  · have H : a≤1/3 := min_le_left _ _
    linarith only [hat,H]
  · have H : a≤b^2/6 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hat,H]
  · have H : a≤b/3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [hat,H]
  · have H : a≤b'/2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith only [hat,H]
  · have H : a≤q/3 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith only [hat,H]

 theorem lockingUnion_annealed_bound (β : ℝ) (μ : ProbabilityMeasure ℝ) (t q b b' : ℝ)
    (hs : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (signedLockingSet n q b) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((9:ℝ)/10)))
    (hs' : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (signedLockingSet n b b') ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((9:ℝ)/10)))
    (hnar : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (narrowLockingSet n μ t (levelRho n)) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((4:ℝ)/5))) :
    ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b') ∂disorderLaw n)≤3*Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
  filter_upwards [hs,hs',hnar,eventually_ge_atTop (1:ℕ)] with n hns hns' hnn hn1
  have H := integral_mono (replicaGibbsMass_integrable β (lockingUnion n μ t (levelRho n) q b b'))
    (((replicaGibbsMass_integrable β (signedLockingSet n q b)).add
      (replicaGibbsMass_integrable β (signedLockingSet n b b'))).add
      (replicaGibbsMass_integrable β (narrowLockingSet n μ t (levelRho n)))) (fun J => by
      have H1 := replicaGibbsMass_union_le β J (signedLockingSet n q b ∪ signedLockingSet n b b') (narrowLockingSet n μ t (levelRho n))
      have H2 := replicaGibbsMass_union_le β J (signedLockingSet n q b) (signedLockingSet n b b')
      change replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b')≤_
      dsimp only [lockingUnion, Pi.add_apply] at *
      linarith only [H1,H2])
  simp only [Pi.add_apply] at H
  have HI1 := integral_add ((replicaGibbsMass_integrable β (signedLockingSet n q b)).add
    (replicaGibbsMass_integrable β (signedLockingSet n b b'))) (replicaGibbsMass_integrable β (narrowLockingSet n μ t (levelRho n)))
  have HI2 := integral_add (replicaGibbsMass_integrable β (signedLockingSet n q b)) (replicaGibbsMass_integrable β (signedLockingSet n b b'))
  simp only [Pi.add_apply] at HI1 HI2
  rw [HI1,HI2] at H
  have HE : Real.exp (-(n:ℝ)^((9:ℝ)/10))≤Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num))
  linarith only [H,hns,hns',hnn,HE]

end SK.Analytic

end
end

end OAI
