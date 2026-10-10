import Mathlib
import OAI.Probability.SKGap.Localization.LogPartitionDeviationProbability
import OAI.Probability.SKGap.Terminal.SingleSpinPlantedLaw

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
namespace SKGapCutoff

noncomputable def gibbsLExpectation {n : ℕ}
    (q : GaussianCoordinates n → Spin n → ℝ≥0∞) (g : GaussianCoordinates n) : ℝ≥0∞ :=
  ∑ x, ENNReal.ofReal (gibbs (sampledInteraction g) x) * q g x

lemma measurable_gibbsLExpectation {n : ℕ}
    (q : GaussianCoordinates n → Spin n → ℝ≥0∞) (hq : ∀ x, Measurable (fun g => q g x)) :
    Measurable (gibbsLExpectation q) := by
  apply Finset.measurable_sum
  intro x _
  exact (((continuous_gibbs x).comp (continuous_sampledInteraction n)).measurable.ennreal_ofReal).mul (hq x)

lemma planted_gibbs_density (β : ℝ) {n : ℕ} (hn : 0 < n)
    (g : GaussianCoordinates n) (x : Spin n) :
    (partition (sampledInteraction g) /
      (∫ h, partition (sampledInteraction h) ∂disorderLaw β n)) * gibbs (sampledInteraction g) x =
      ((2 : ℝ)^n)⁻¹ * Real.exp (energy (sampledInteraction g) x - β^2*((n:ℝ)-1)/4) := by
  rw [integral_partition_sampled β hn, gibbs, Real.exp_sub]
  field_simp [ne_of_gt (partition_pos (sampledInteraction g))]

lemma planted_gibbs_lintegral (β : ℝ) {n : ℕ} (hn : 0 < n)
    (q : GaussianCoordinates n → Spin n → ℝ≥0∞) (hq : ∀ x, Measurable (fun g => q g x)) :
    (∫⁻ g, gibbsLExpectation q g ∂plantedDisorderLaw β n) =
      ENNReal.ofReal (((2:ℝ)^n)⁻¹) *
        ∑ x : Spin n, ∫⁻ g, q g x ∂singleSpinPlantedLaw β x := by
  have hm := (continuous_partition n).comp (continuous_sampledInteraction n)
  unfold plantedDisorderLaw
  have hr : Measurable (fun g : GaussianCoordinates n => ENNReal.ofReal
      (partition (sampledInteraction g) /
        (∫ h, partition (sampledInteraction h) ∂disorderLaw β n))) := by
    exact (hm.measurable.div_const _).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hr (measurable_gibbsLExpectation q hq)]
  change (∫⁻ g, _ * (∑ x, ENNReal.ofReal (gibbs (sampledInteraction g) x) * q g x) ∂disorderLaw β n) = _
  simp only [Finset.mul_sum, ← mul_assoc]
  have hp (g : GaussianCoordinates n) (x : Spin n) :
      ENNReal.ofReal (partition (sampledInteraction g) /
        (∫ h, partition (sampledInteraction h) ∂disorderLaw β n)) *
        ENNReal.ofReal (gibbs (sampledInteraction g) x) =
      ENNReal.ofReal (((2:ℝ)^n)⁻¹) *
        ENNReal.ofReal (Real.exp (energy (sampledInteraction g) x - β^2*((n:ℝ)-1)/4)) := by
    rw [← ENNReal.ofReal_mul (by
      exact div_nonneg (partition_pos _).le (by rw [integral_partition_sampled β hn]; positivity)),
      planted_gibbs_density β hn, ENNReal.ofReal_mul (by positivity)]
  have hE (x : Spin n) : Measurable (fun g : GaussianCoordinates n =>
      ENNReal.ofReal (Real.exp (energy (sampledInteraction g) x - β^2*((n:ℝ)-1)/4))) :=
    ((((continuous_energy x).comp (continuous_sampledInteraction n)).measurable.sub_const _).exp).ennreal_ofReal
  simp_rw [hp, mul_assoc]
  have hterm (x : Spin n) : Measurable (fun g : GaussianCoordinates n =>
      ENNReal.ofReal (((2:ℝ)^n)⁻¹) *
        (ENNReal.ofReal (Real.exp (energy (sampledInteraction g) x - β^2*((n:ℝ)-1)/4)) * q g x)) :=
    measurable_const.mul ((hE x).mul (hq x))
  rw [lintegral_finsetSum Finset.univ (fun x _ => hterm x)]
  apply Finset.sum_congr rfl
  intro x _
  have hf : Measurable (fun g : GaussianCoordinates n =>
      ENNReal.ofReal (Real.exp (energy (sampledInteraction g) x - β^2*((n:ℝ)-1)/4)) * q g x) :=
    (hE x).mul (hq x)
  rw [lintegral_const_mul _ hf]
  congr 1
  rw [singleSpinPlantedLaw, lintegral_withDensity_eq_lintegral_mul _ (hE x) (hq x)]
  rfl

lemma planted_failure_probability_bound (β : ℝ) {n : ℕ} (hn : 0 < n)
    (a s : ℝ) (f : GaussianCoordinates n → ℝ≥0∞) (hf : Measurable f) :
    disorderLaw β n {g | ENNReal.ofReal (Real.exp (-s)) ≤ f g} ≤
      disorderLaw β n {g | a/(n:ℝ) < |(Real.log (partition (sampledInteraction g)) -
        Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n))/(n:ℝ)|} +
      ENNReal.ofReal (Real.exp (a+s)) * ∫⁻ g, f g ∂plantedDisorderLaw β n := by
  let m := ∫ h, partition (sampledInteraction h) ∂disorderLaw β n
  let E := {g : GaussianCoordinates n | Real.log m - a ≤ Real.log (partition (sampledInteraction g))}
  have hsub : {g | ENNReal.ofReal (Real.exp (-s)) ≤ f g} ⊆
      Eᶜ ∪ {g | Real.log m - a ≤ Real.log (partition (sampledInteraction g)) ∧
        ENNReal.ofReal (Real.exp (-s)) ≤ f g} := by
    intro g hg
    by_cases h : g ∈ E
    · exact Or.inr ⟨h,hg⟩
    · exact Or.inl h
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply add_le_add _ (planted_law_transfer β hn a s f hf)
  apply measure_mono
  intro g hg
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hh : Real.log (partition (sampledInteraction g)) < Real.log m - a := lt_of_not_ge hg
  change a/(n:ℝ) < |(Real.log (partition (sampledInteraction g)) - Real.log m)/(n:ℝ)|
  rw [abs_div, abs_of_pos hnR]
  apply (div_lt_div_iff_of_pos_right hnR).mpr
  linarith [neg_le_abs (Real.log (partition (sampledInteraction g)) - Real.log m)]

lemma quenched_exponential_transfer (β : ℝ) (hβ : β^2 < 1)
    (c : ℝ) (hc : 0 < c) (f : (n : ℕ) → GaussianCoordinates n → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hsmall : ∀ᶠ n : ℕ in atTop, (∫⁻ g, f n g ∂plantedDisorderLaw β n) ≤
      ENNReal.ofReal (Real.exp (-c*n))) :
    Tendsto (fun n => disorderLaw β n {g | ENNReal.ofReal (Real.exp (-(c/2)*n)) ≤ f n g})
      atTop (nhds 0) := by
  have hlog := log_partition_annealed_difference_limit β hβ (c/4) (by positivity)
  simp only [sub_zero] at hlog
  have he : Tendsto (fun n : ℕ => Real.exp (-(c/4)*n)) atTop (nhds 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).const_mul_atTop
        (show 0 < c/4 by positivity))
    simpa only [Function.comp_def, neg_mul] using hh
  have he' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
  simp only [ENNReal.ofReal_zero] at he'
  have hb := hlog.add he'
  simp only [zero_add] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_gt_atTop 0, hsmall] with n hn hs
  have hh := planted_failure_probability_bound β hn (c*n/4) (c*n/2) (f n) (hf n)
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfrac : (c*(n:ℝ)/4)/(n:ℝ) = c/4 := by field_simp
  rw [hfrac] at hh
  have hleft : -(c*(n:ℝ)/2) = -(c/2)*n := by ring
  rw [hleft] at hh
  apply hh.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ENNReal.ofReal (Real.exp (c*n/4+c*n/2)) *
        ENNReal.ofReal (Real.exp (-c*n)) := mul_le_mul' le_rfl hs
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix

end

end OAI
