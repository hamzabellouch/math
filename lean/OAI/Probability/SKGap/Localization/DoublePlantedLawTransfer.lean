import Mathlib
import OAI.Probability.SKGap.Matrix.DoublePlantLogNorm

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
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace SKGapCutoff

lemma double_planted_law_transfer (β : ℝ) (hβ : β^2 < 1) {n : ℕ} (hn : 0 < n)
    (a s : ℝ) (f : GaussianCoordinates n → ℝ≥0∞) (hf : Measurable f) :
    (disorderLaw β n) {g | Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n) - a ≤
        Real.log (partition (sampledInteraction g)) ∧ ENNReal.ofReal (Real.exp (-s)) ≤ f g} ≤
      ENNReal.ofReal ((Real.sqrt (1-β^2))⁻¹ * Real.exp (2*a+s)) *
        ∫⁻ g, f g ∂doublePlantedDisorderLaw β n := by
  let m := ∫ h, partition (sampledInteraction h) ∂disorderLaw β n
  let C := (Real.sqrt (1-β^2))⁻¹
  have hC : 0 < C := inv_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hβ))
  let r := fun g : GaussianCoordinates n => ENNReal.ofReal
    (partition (sampledInteraction g)^2/doublePlantNorm β n)
  let A := {g : GaussianCoordinates n | Real.log m - a ≤
    Real.log (partition (sampledInteraction g)) ∧ ENNReal.ofReal (Real.exp (-s)) ≤ f g}
  have hm : 0 < m := by dsimp [m]; rw [integral_partition_sampled β hn]; positivity
  have hZ := (continuous_partition n).comp (continuous_sampledInteraction n)
  have hr : Measurable r := ((hZ.measurable.pow_const 2).div_const _).ennreal_ofReal
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const hZ.measurable.log).inter
      (measurableSet_le measurable_const hf)
  have hNorm : doublePlantNorm β n ≤ C*m^2 :=
    (div_le_iff₀ (sq_pos_of_pos hm)).mp (partition_second_moment_bound β hβ hn)
  have hd : ∀ g ∈ A, ENNReal.ofReal (Real.exp (-2*a)/C) ≤ r g := by
    intro g hg
    apply ENNReal.ofReal_le_ofReal
    have hl : m*Real.exp (-a) ≤ partition (sampledInteraction g) := by
      have he := Real.exp_le_exp.mpr hg.1
      rwa [Real.exp_sub, Real.exp_log hm, Real.exp_log (partition_pos _),
        div_eq_mul_inv, ← Real.exp_neg] at he
    have hs : m^2*Real.exp (-2*a) ≤ partition (sampledInteraction g)^2 := by
      have hh := pow_le_pow_left₀ (mul_nonneg hm.le (Real.exp_pos _).le) hl 2
      rw [mul_pow, ← Real.exp_nat_mul] at hh
      convert! hh using 1
      congr 2
      ring
    apply (div_le_div_iff₀ hC (doublePlantNorm_pos β hn)).mpr
    calc
      _ ≤ Real.exp (-2*a)*(C*m^2) := mul_le_mul_of_nonneg_left hNorm (Real.exp_pos _).le
      _ ≤ partition (sampledInteraction g)^2*C := by
        nlinarith [mul_le_mul_of_nonneg_right hs hC.le]
  have h := lower_density_markov_div (disorderLaw β n) r f hr hf A hA
    (ENNReal.ofReal (Real.exp (-2*a)/C)) (ENNReal.ofReal (Real.exp (-s)))
    (by positivity) ENNReal.ofReal_ne_top (by positivity) ENNReal.ofReal_ne_top hd
    (fun g hg => hg.2)
  have he : (ENNReal.ofReal (Real.exp (-2*a)/C) * ENNReal.ofReal (Real.exp (-s)))⁻¹ =
      ENNReal.ofReal (C*Real.exp (2*a+s)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [_root_.mul_inv_rev, inv_div, ← Real.exp_neg, neg_neg]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    rw [show -(-2*a) = 2*a by ring]
    rw [Real.exp_add]
    ring
  rw [div_eq_mul_inv, he, mul_comm] at h
  exact h

lemma double_planted_failure_probability_bound (β : ℝ) (hβ : β^2 < 1)
    {n : ℕ} (hn : 0 < n) (a s : ℝ)
    (f : GaussianCoordinates n → ℝ≥0∞) (hf : Measurable f) :
    disorderLaw β n {g | ENNReal.ofReal (Real.exp (-s)) ≤ f g} ≤
      disorderLaw β n {g | a/(n:ℝ) < |(Real.log (partition (sampledInteraction g)) -
        Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n))/(n:ℝ)|} +
      ENNReal.ofReal ((Real.sqrt (1-β^2))⁻¹ * Real.exp (2*a+s)) *
        ∫⁻ g, f g ∂doublePlantedDisorderLaw β n := by
  let m := ∫ h, partition (sampledInteraction h) ∂disorderLaw β n
  let E := {g : GaussianCoordinates n | Real.log m-a ≤ Real.log (partition (sampledInteraction g))}
  have hsub : {g | ENNReal.ofReal (Real.exp (-s)) ≤ f g} ⊆ Eᶜ ∪
      {g | Real.log m-a ≤ Real.log (partition (sampledInteraction g)) ∧
        ENNReal.ofReal (Real.exp (-s)) ≤ f g} := by
    intro g hg
    by_cases h : g ∈ E
    · exact Or.inr ⟨h,hg⟩
    · exact Or.inl h
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply add_le_add _ (double_planted_law_transfer β hβ hn a s f hf)
  apply measure_mono
  intro g hg
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hh : Real.log (partition (sampledInteraction g)) < Real.log m-a := lt_of_not_ge hg
  change a/(n:ℝ) < |(Real.log (partition (sampledInteraction g))-Real.log m)/(n:ℝ)|
  rw [abs_div, abs_of_pos hnR]
  apply (div_lt_div_iff_of_pos_right hnR).mpr
  linarith [neg_le_abs (Real.log (partition (sampledInteraction g))-Real.log m)]

lemma quenched_double_exponential_transfer (β : ℝ) (hβ : β^2 < 1)
    (c : ℝ) (hc : 0 < c) (f : (n : ℕ) → GaussianCoordinates n → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hsmall : ∀ᶠ n : ℕ in atTop, (∫⁻ g, f n g ∂doublePlantedDisorderLaw β n) ≤
      ENNReal.ofReal (Real.exp (-c*n))) :
    Tendsto (fun n => disorderLaw β n {g | ENNReal.ofReal (Real.exp (-(c/2)*n)) ≤ f n g})
      atTop (nhds 0) := by
  have hlog := log_partition_annealed_difference_limit β hβ (c/8) (by positivity)
  simp only [sub_zero] at hlog
  have he : Tendsto (fun n : ℕ => (Real.sqrt (1-β^2))⁻¹ * Real.exp (-(c/4)*n))
      atTop (nhds 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).const_mul_atTop
        (show 0 < c/4 by positivity))
    simpa only [Function.comp_def, neg_mul, mul_zero] using hh.const_mul ((Real.sqrt (1-β^2))⁻¹)
  have he' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
  simp only [ENNReal.ofReal_zero] at he'
  have hb := hlog.add he'
  simp only [zero_add] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_gt_atTop 0, hsmall] with n hn hs
  have hh := double_planted_failure_probability_bound β hβ hn (c*n/8) (c*n/2) (f n) (hf n)
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfrac : (c*(n:ℝ)/8)/(n:ℝ) = c/8 := by field_simp
  rw [hfrac] at hh
  have hleft : -(c*(n:ℝ)/2) = -(c/2)*n := by ring
  rw [hleft] at hh
  apply hh.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ENNReal.ofReal ((Real.sqrt (1-β^2))⁻¹ * Real.exp (2*(c*n/8)+c*n/2)) *
        ENNReal.ofReal (Real.exp (-c*n)) := mul_le_mul' le_rfl hs
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
      congr 3
      ring

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

end

end OAI
