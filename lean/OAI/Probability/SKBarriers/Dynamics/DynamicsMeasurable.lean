import Mathlib
import OAI.Probability.SKBarriers.Coverage.PressureGapProbability
import OAI.Probability.SKBarriers.Dynamics.ClockEndpoint

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem continuous_coupling {n : ℕ} (i j : Fin n) : Continuous (fun J : Disorder n => coupling J i j) := by
  unfold coupling
  split_ifs <;> first | exact continuous_apply _ | exact continuous_const

theorem continuous_localField {n : ℕ} (x : Config n) (i : Fin n) : Continuous (fun J : Disorder n => localField J x i) := by
  unfold localField
  apply Continuous.div_const
  exact continuous_finsetSum _ (fun j _ => (continuous_coupling i j).mul continuous_const)

theorem continuous_heatBath {n : ℕ} (β : ℝ) (x y : Config n) : Continuous (fun J : Disorder n => heatBath β J x y) := by
  unfold heatBath
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  split_ifs
  · apply Continuous.div
    · exact (continuous_const.mul (continuous_localField x i)).rexp
    · exact continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul (continuous_localField x i)))
    · intro J; exact mul_ne_zero (by norm_num) (Real.cosh_pos _).ne'
  · exact continuous_const

theorem continuous_discreteKernel {n : ℕ} (β : ℝ) (k : ℕ) (x y : Config n) :
    Continuous (fun J : Disorder n => discreteKernel β J k x y) := by
  induction k generalizing x y with
  | zero => exact continuous_const
  | succ k ih =>
    exact continuous_finsetSum _ (fun z _ => (continuous_heatBath β x z).mul (ih z y))

theorem measurable_continuousKernel {n : ℕ} (β : ℝ) (t : ℝ) (x y : Config n) :
    Measurable (fun J : Disorder n => continuousKernel β J t x y) := by
  exact Measurable.tsum (fun k => measurable_const.mul (continuous_discreteKernel β k x y).measurable)

theorem continuous_discreteDistance {n : ℕ} (β : ℝ) (k : ℕ) (x : Config n) :
    Continuous (fun J : Disorder n => discreteDistance β J x k) := by
  exact continuous_const.mul (continuous_finsetSum _ (fun y _ => ((continuous_discreteKernel β k x y).sub (continuous_gibbs β y)).abs))

theorem measurable_continuousDistance {n : ℕ} (β : ℝ) (t : ℝ) (x : Config n) :
    Measurable (fun J : Disorder n => continuousDistance β J x t) := by
  exact measurable_const.mul (Finset.measurable_sum _ (fun y _ => ((measurable_continuousKernel β t x y).sub (continuous_gibbs β y).measurable).abs))

theorem measurable_gibbs_predicate_mass {n : ℕ} (β : ℝ) (E : Disorder n → Config n → Prop)
    (hE : ∀x,MeasurableSet {J | E J x}) :
    Measurable (fun J => ∑x,if E J x then gibbs β J x else 0) := by
  exact Finset.measurable_sum _ (fun x _ => Measurable.ite (hE x) (continuous_gibbs β x).measurable measurable_const)

theorem gibbs_predicate_mass_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    0≤∑x,if E x then gibbs β J x else 0 := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> first | exact (gibbs_pos β J x).le | exact le_rfl

theorem gibbs_predicate_mass_le_one {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (∑x,if E x then gibbs β J x else 0)≤1 := by
  rw [← gibbs_sum β J]
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> first | exact le_rfl | exact (gibbs_pos β J x).le

theorem integrable_gibbs_predicate_mass {n : ℕ} (β : ℝ) (E : Disorder n → Config n → Prop)
    (hE : ∀x,MeasurableSet {J | E J x}) :
    Integrable (fun J => ∑x,if E J x then gibbs β J x else 0) (disorderLaw n) := by
  apply (integrable_const (1:ℝ)).mono' (measurable_gibbs_predicate_mass β E hE).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs,abs_of_nonneg (gibbs_predicate_mass_nonneg β J _)] using gibbs_predicate_mass_le_one β J (E J)

theorem discreteMixedMass_integrable (n : ℕ) (β : ℝ) (k : ℕ) :
    Integrable (fun J : Disorder n => discreteMixedMass β J k) (disorderLaw n) :=
  integrable_gibbs_predicate_mass β _ (fun x => measurableSet_le (continuous_discreteDistance β k x).measurable measurable_const)

theorem continuousMixedMass_integrable (n : ℕ) (β : ℝ) (t : ℝ) :
    Integrable (fun J : Disorder n => continuousMixedMass β J t) (disorderLaw n) :=
  integrable_gibbs_predicate_mass β _ (fun x => measurableSet_le (measurable_continuousDistance β t x) measurable_const)

theorem gibbs_predicate_mass_compl {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (∑x,if ¬E x then gibbs β J x else 0)=1-∑x,if E x then gibbs β J x else 0 := by
  rw [← gibbs_sum β J,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

theorem discreteBadMass_eq_one_sub (β : ℝ) (n : ℕ) :
    discreteBadMass β n=1-∫J,discreteMixedMass β J ⌊timeScale n⌋₊ ∂disorderLaw n := by
  have he (J : Disorder n) : (∑x,if (1/4:ℝ)<discreteDistance β J x ⌊timeScale n⌋₊ then gibbs β J x else 0)=
      1-discreteMixedMass β J ⌊timeScale n⌋₊ := by
    simpa only [not_le,discreteMixedMass] using gibbs_predicate_mass_compl β J (fun x => discreteDistance β J x ⌊timeScale n⌋₊≤(1/4:ℝ))
  unfold discreteBadMass
  simp_rw [he]
  rw [integral_sub (integrable_const 1) (discreteMixedMass_integrable n β _)]
  simp

theorem continuousBadMass_eq_one_sub (β : ℝ) (n : ℕ) :
    continuousBadMass β n=1-∫J,continuousMixedMass β J (timeScale n) ∂disorderLaw n := by
  have he (J : Disorder n) : (∑x,if (1/4:ℝ)<continuousDistance β J x (timeScale n) then gibbs β J x else 0)=
      1-continuousMixedMass β J (timeScale n) := by
    simpa only [not_le,continuousMixedMass] using gibbs_predicate_mass_compl β J (fun x => continuousDistance β J x (timeScale n)≤(1/4:ℝ))
  unfold continuousBadMass
  simp_rw [he]
  rw [integral_sub (integrable_const 1) (continuousMixedMass_integrable n β _)]
  simp

theorem main_of_quenched_mixed_bounds (β : ℝ) (C : (n : ℕ) → Set (Disorder n))
    (hC : ∀n,MeasurableSet (C n)) (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (e : ℕ → ℝ) (he : ∀n,0≤e n) (he0 : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n : ℕ in atTop,∀J∈C n,continuousMixedMass β J (timeScale n)≤e n ∧
      discreteMixedMass β J ⌊timeScale n⌋₊≤e n) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧ Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  have hcomp : Tendsto (fun n => (disorderLaw n).real (C n)ᶜ) atTop (𝓝 0) := by
    have H := (tendsto_const_nhds (x:=(1:ℝ))).sub hC1
    simpa only [measureReal_compl (hC _),probReal_univ,sub_self] using H
  have hlim := he0.add hcomp
  simp only [add_zero] at hlim
  have HC : Tendsto (fun n => ∫J,continuousMixedMass β J (timeScale n) ∂disorderLaw n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun J => gibbs_predicate_mass_nonneg β J _))) _ hlim
    filter_upwards [hbound] with n hn
    apply integral_le_off_exception (continuousMixedMass_integrable n β _) (hC n).compl (he n)
      (fun J => gibbs_predicate_mass_le_one β J _)
    intro J hJ
    exact (hn J (by simpa only [mem_compl_iff,not_not] using hJ)).1
  have HD : Tendsto (fun n => ∫J,discreteMixedMass β J ⌊timeScale n⌋₊ ∂disorderLaw n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun J => gibbs_predicate_mass_nonneg β J _))) _ hlim
    filter_upwards [hbound] with n hn
    apply integral_le_off_exception (discreteMixedMass_integrable n β _) (hC n).compl (he n)
      (fun J => gibbs_predicate_mass_le_one β J _)
    intro J hJ
    exact (hn J (by simpa only [mem_compl_iff,not_not] using hJ)).2
  constructor
  · have H := (tendsto_const_nhds (x:=(1:ℝ))).sub HC
    simpa only [← continuousBadMass_eq_one_sub,sub_zero] using H
  · have H := (tendsto_const_nhds (x:=(1:ℝ))).sub HD
    simpa only [← discreteBadMass_eq_one_sub,sub_zero] using H

end SK.Analytic

end
end

end OAI
