import Mathlib
import OAI.Analysis.CoulombIonization.Localization.SqrtMultiplier

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationIntegral_scope

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

lemma integrable_bounded_probability {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {q : Ω → ℝ} (hq : Measurable q)
    (hn : ∀ x, 0 ≤ q x) (hb : ∀ x, q x ≤ 1) : Integrable q μ := by
  apply (integrable_const (1:ℝ)).mono' hq.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn x)] using hb x)

lemma bounded_probability_rpow_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {q : Ω → ℝ} (hq : Measurable q)
    (hn : ∀ x, 0 ≤ q x) (hb : ∀ x, q x ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x => q x ^ a) μ := by
  apply integrable_bounded_probability (hq.pow_const a)
  · exact fun x => Real.rpow_nonneg (hn x) _
  · exact fun x => Real.rpow_le_one (hn x) (hb x) ha

lemma integral_bounded_probability_rpow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {q : Ω → ℝ} (hq : Measurable q)
    (hn : ∀ x, 0 ≤ q x) (hb : ∀ x, q x ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ x, q x ^ a ∂μ) ≤ (∫ x, q x ∂μ)^a := by
  apply (Real.concaveOn_rpow ha ha1).le_map_integral
  · exact (Real.continuous_rpow_const ha).continuousOn
  · exact isClosed_Ici
  · exact ae_of_all _ hn
  · exact integrable_bounded_probability hq hn hb
  · exact bounded_probability_rpow_integrable hq hn hb ha

def eventMomentOrder (p : ℝ) : ℕ := ⌈-Real.log p⌉₊+1

lemma eventMomentOrder_pos (p : ℝ) : 0 < eventMomentOrder p := by
  unfold eventMomentOrder; omega

lemma eventMomentOrder_bound {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (eventMomentOrder p : ℝ) ≤ 2*(1-Real.log p) := by
  have hl := Real.log_nonpos hp.le hp1
  have hc := Nat.ceil_lt_add_one (show 0 ≤ -Real.log p by linarith)
  dsimp [eventMomentOrder]
  push_cast
  linarith

lemma eventMomentOrder_rpow_bound {p : ℝ} (hp : 0 < p) :
    p ^ (-((eventMomentOrder p : ℝ)⁻¹)) ≤ Real.exp 1 := by
  rw [Real.rpow_def_of_pos hp, Real.exp_le_exp]
  have hk : (0:ℝ) < eventMomentOrder p := by exact_mod_cast eventMomentOrder_pos p
  have hc := Nat.le_ceil (-Real.log p)
  have hle : -Real.log p ≤ (eventMomentOrder p : ℝ) := by
    dsimp [eventMomentOrder]; push_cast; linarith
  rw [mul_neg, ← neg_mul, ← div_eq_mul_inv, div_le_iff₀ hk]
  simpa using hle

lemma eventMomentOrder_integral_bound {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (eventMomentOrder p : ℝ)^5 * p^(1-(eventMomentOrder p:ℝ)⁻¹) ≤
      (32*Real.exp 1)*(1-Real.log p)^5*p := by
  have hl : 0 ≤ 1-Real.log p := by linarith [Real.log_nonpos hp.le hp1]
  have hk : 0 ≤ (eventMomentOrder p : ℝ) := Nat.cast_nonneg _
  have hpow := pow_le_pow_left₀ hk (eventMomentOrder_bound hp hp1) 5
  have hprod := mul_le_mul hpow (eventMomentOrder_rpow_bound hp)
    (Real.rpow_nonneg hp.le _) (by positivity : 0 ≤ (2*(1-Real.log p))^5)
  rw [sub_eq_add_neg, Real.rpow_add hp, Real.rpow_one]
  calc
    _ = ((eventMomentOrder p : ℝ)^5 * p^(-((eventMomentOrder p:ℝ)⁻¹)))*p := by ring
    _ ≤ (2*(1-Real.log p))^5 * Real.exp 1 * p := mul_le_mul_of_nonneg_right hprod hp.le
    _ = _ := by ring

lemma eventLog_eq {p : ℝ} (hp : 0 < p) : Real.log (Real.exp 1/p) = 1-Real.log p := by
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hp), Real.log_exp]

end Work_ObservationIntegral_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

def arrayFisher {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (x : I → ℝ) : ℝ :=
  ∑ i, (lineDeriv ℝ (fun y => Real.sqrt (arrayLikelihood b s y)) x (Pi.single i 1))^2

lemma arrayFisher_nonneg {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (x : I → ℝ) : 0 ≤ arrayFisher b s x :=
  sum_nonneg (fun _ _ => sq_nonneg _)

lemma arrayFisher_measurable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) :
    Measurable (arrayFisher b s) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_lineDeriv (sqrtArrayLikelihood_lipschitz b hs).continuous).pow_const 2

lemma reciprocal_moment_sub_one_nonneg {k : ℕ} (hk : 0 < k) : 0 ≤ 1-(k:ℝ)⁻¹ := by
  have hh : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hi : (k:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hh
  linarith

lemma arrayFisher_integrable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s)
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] : Integrable (arrayFisher b s) μ := by
  have hC := observationMomentConstant_pos
  have hbound (x : I → ℝ) : arrayFisher b s x ≤
      (observationMomentConstant/4) * ∑ j, (b j)^2 := by
    simpa [arrayFisher] using sqrtArrayLikelihood_lineDeriv_sq b hs x (k := 1) (by decide)
  apply (integrable_const ((observationMomentConstant/4) * ∑ j, (b j)^2)).mono'
    (arrayFisher_measurable b hs).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (arrayFisher_nonneg b s x)] using hbound x

lemma arrayFisher_integral_moment {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s)
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k) :
    (∫ x, arrayFisher b s x ∂μ) ≤
      (observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (∫ x, arrayLikelihood b s x ∂μ)^(1-(k:ℝ)⁻¹) := by
  have ha := reciprocal_moment_sub_one_nonneg hk
  have ha1 : 1-(k:ℝ)⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hq := (arrayLikelihood_contDiff b hs (n := 1)).continuous.measurable
  have hC := observationMomentConstant_pos
  have hj := integral_bounded_probability_rpow (μ := μ) hq
    (arrayLikelihood_nonneg b hs) (arrayLikelihood_le_one b hs) ha ha1
  calc
    _ ≤ ∫ x, (observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(1-(k:ℝ)⁻¹) ∂μ := by
      apply integral_mono (arrayFisher_integrable b hs μ)
        ((bounded_probability_rpow_integrable hq (arrayLikelihood_nonneg b hs)
          (arrayLikelihood_le_one b hs) ha).const_mul _)
      exact fun x => sqrtArrayLikelihood_lineDeriv_sq b hs x hk
    _ = ((observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2)) *
        ∫ x, (arrayLikelihood b s x)^(1-(k:ℝ)⁻¹) ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hj (by positivity)

def observationFisherConstant : ℝ := 8 * Real.exp 1 * observationMomentConstant

lemma observationFisherConstant_pos : 0 < observationFisherConstant := by
  unfold observationFisherConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) observationMomentConstant_pos

theorem arrayFisher_integral_log {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s)
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hp : 0 < ∫ x, arrayLikelihood b s x ∂μ) :
    (∫ x, arrayFisher b s x ∂μ) ≤
      observationFisherConstant * (∑ j, (b j)^2) *
        (Real.log (Real.exp 1/(∫ x, arrayLikelihood b s x ∂μ)))^5 *
        (∫ x, arrayLikelihood b s x ∂μ) := by
  let p := ∫ x, arrayLikelihood b s x ∂μ
  have hp1 : p ≤ 1 := by
    have h := integral_mono
      (integrable_bounded_probability (μ := μ) ((arrayLikelihood_contDiff b hs (n:=1)).continuous.measurable)
        (arrayLikelihood_nonneg b hs) (arrayLikelihood_le_one b hs))
      (integrable_const (1:ℝ)) (arrayLikelihood_le_one b hs)
    simpa [p] using h
  have hC := observationMomentConstant_pos
  have hb : 0 ≤ ∑ j, (b j)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound := arrayFisher_integral_moment b hs μ (eventMomentOrder_pos p)
  have hlog := mul_le_mul_of_nonneg_left (eventMomentOrder_integral_bound hp hp1)
    (show 0 ≤ observationMomentConstant/4 * ∑ j, (b j)^2 by positivity)
  change _ ≤ observationFisherConstant * (∑ j, (b j)^2) * Real.log (Real.exp 1/p)^5 * p
  rw [eventLog_eq hp]
  calc
    _ ≤ (observationMomentConstant/4) * (eventMomentOrder p:ℝ)^5 * (∑ j, (b j)^2) *
        p^(1-(eventMomentOrder p:ℝ)⁻¹) := hbound
    _ = (observationMomentConstant/4 * ∑ j, (b j)^2) *
        ((eventMomentOrder p:ℝ)^5 * p^(1-(eventMomentOrder p:ℝ)⁻¹)) := by ring
    _ ≤ (observationMomentConstant/4 * ∑ j, (b j)^2) *
        ((32*Real.exp 1)*(1-Real.log p)^5*p) := hlog
    _ = _ := by dsimp [observationFisherConstant]; ring

end CoulombObservation

end

end OAI
