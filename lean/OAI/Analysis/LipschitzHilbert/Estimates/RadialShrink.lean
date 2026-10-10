import OAI.Analysis.LipschitzHilbert.Estimates.LogEnergy
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# Radial snapshot shrinkage and the balanced prediction comparison

Section 9 shrinks each snapshot amplitude radially by a controlled distance.
The exact norm formula makes its denominator smaller than every nearby moved
denominator. The numerator motion and the logarithmic-energy Lipschitz bound
then give the balanced-case comparison, with its relative path-drop factor.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial truncation by the distance `δ`; its value at the zero vector is zero. -/
def radialShrink (δ : ℝ) (x : E) : E := max (1 - δ / ‖x‖) 0 • x

@[simp] theorem radialShrink_zero (δ : ℝ) : radialShrink δ (0 : E) = 0 := by
  simp [radialShrink]

/-- The radial truncation removes exactly the smaller of `δ` and the norm. -/
theorem norm_radialShrink {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    ‖radialShrink δ x‖ = max (‖x‖ - δ) 0 := by
  by_cases hx : x = 0
  · subst x
    simp [max_eq_right (neg_nonpos.mpr hδ)]
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [radialShrink, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  by_cases hsmall : δ ≤ ‖x‖
  · have hfactor : 0 ≤ 1 - δ / ‖x‖ := by
      exact sub_nonneg.mpr ((div_le_one hxnorm).2 hsmall)
    rw [max_eq_left hfactor, max_eq_left (sub_nonneg.mpr hsmall)]
    field_simp
  · have hlarge : ‖x‖ ≤ δ := le_of_lt (lt_of_not_ge hsmall)
    have hfactor : 1 - δ / ‖x‖ ≤ 0 := by
      exact sub_nonpos.mpr ((one_le_div hxnorm).2 hlarge)
    rw [max_eq_right hfactor, max_eq_right (sub_nonpos.mpr hlarge), zero_mul]

/-- Vectors already within the discarded radius are suppressed completely. -/
theorem radialShrink_eq_zero_iff {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    radialShrink δ x = 0 ↔ ‖x‖ ≤ δ := by
  rw [← norm_eq_zero, norm_radialShrink hδ]
  constructor
  · intro h
    have hle := le_max_left (‖x‖ - δ) 0
    rw [h] at hle
    linarith
  · intro h
    exact max_eq_right (sub_nonpos.mpr h)

theorem norm_radialShrink_le {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    ‖radialShrink δ x‖ ≤ ‖x‖ := by
  rw [norm_radialShrink hδ]
  exact max_le (sub_le_self _ hδ) (norm_nonneg _)

/-- The change in the amplitude never exceeds the requested shrinkage distance. -/
theorem norm_radialShrink_sub_le {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    ‖radialShrink δ x - x‖ ≤ δ := by
  let c := max (1 - δ / ‖x‖) 0
  have hc1 : c ≤ 1 := max_le (sub_le_self _ (div_nonneg hδ (norm_nonneg x))) zero_le_one
  have hnorm : c * ‖x‖ = max (‖x‖ - δ) 0 := by
    have h := norm_radialShrink hδ x
    rw [radialShrink, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (1 - δ / ‖x‖) 0)] at h
    exact h
  have heq : radialShrink δ x - x = (c - 1) • x := by
    simp only [radialShrink, sub_smul, one_smul, c]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hc1)]
  nlinarith [le_max_left (‖x‖ - δ) 0]

/-- A nearby moved vector has norm at least the scaled, radially shrunken
snapshot. `z` allows an arbitrary norm-preserving rotation of the snapshot. -/
theorem scaled_radialShrink_norm_le_of_error {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (x y z : E) (hz : ‖z‖ = c * ‖x‖) (hmotion : ‖y - z‖ ≤ c * δ) :
    ‖c • radialShrink δ x‖ ≤ ‖y‖ := by
  have hreverse : c * ‖x‖ ≤ ‖y‖ + c * δ := by
    have h := norm_sub_le y (y - z)
    rw [sub_sub_cancel, hz] at h
    exact h.trans (add_le_add_right hmotion _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, norm_radialShrink hδ]
  by_cases hsmall : δ ≤ ‖x‖
  · rw [max_eq_left (sub_nonneg.mpr hsmall)]
    nlinarith
  · rw [max_eq_right (sub_nonpos.mpr (le_of_lt (lt_of_not_ge hsmall))), mul_zero]
    exact norm_nonneg _

/-- Raising the denominator comparison to any nonnegative real power preserves it. -/
theorem scaled_radialShrink_power_le_of_error {δ c p : ℝ}
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (x y z : E) (hz : ‖z‖ = c * ‖x‖) (hmotion : ‖y - z‖ ≤ c * δ) :
    ‖c • radialShrink δ x‖ ^ p ≤ ‖y‖ ^ p :=
  Real.rpow_le_rpow (norm_nonneg _) (scaled_radialShrink_norm_le_of_error hδ hc x y z hz hmotion) hp

theorem norm_weighted_smul_rpow {p l : ℝ} (hp : 0 < p) (hl : 0 ≤ l) (x : E) :
    ‖(l ^ (1 / p)) • x‖ ^ p = l * ‖x‖ ^ p := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl _),
    Real.mul_rpow (Real.rpow_nonneg hl _) (norm_nonneg _), ← Real.rpow_mul hl]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The exact weighted denominator comparison from `pred:denominator-lower-bound`.
The permitted motion is measured after the positive `l^(1/p)` rescaling. -/
theorem weighted_radialShrink_power_le_of_error {δ p l l' : ℝ}
    (hδ : 0 ≤ δ) (hp : 0 < p) (hl : 0 ≤ l) (hl' : 0 ≤ l')
    (x y z : E) (hz : ‖z‖ = l ^ (1 / p) * ‖x‖)
    (hmotion : ‖l' ^ (1 / p) • y - z‖ ≤ l ^ (1 / p) * δ) :
    l * ‖radialShrink δ x‖ ^ p ≤ l' * ‖y‖ ^ p := by
  have h := scaled_radialShrink_power_le_of_error hδ (Real.rpow_nonneg hl _) hp.le
    x (l' ^ (1 / p) • y) z hz hmotion
  simpa only [norm_weighted_smul_rpow hp hl, norm_weighted_smul_rpow hp hl'] using h

omit [NormedSpace ℝ E] in
/-- With the model denominator below the actual denominator, only numerator
motion contributes positively to the logarithmic ratio comparison. -/
theorem prediction_log_comparison {p dActual dModel : ℝ} (hp : 1 ≤ p)
    (hdModel : 0 < dModel) (hden : dModel ≤ dActual) (actual model : E) :
    Real.log (energyRatio p dActual actual) - Real.log (energyRatio p dModel model) ≤
      p * ‖actual - model‖ := by
  have hdActual : 0 < dActual := hdModel.trans_le hden
  have hlogden : Real.log dModel ≤ Real.log dActual := Real.log_le_log hdModel hden
  have hnum := (abs_le.mp (logEnergy_lipschitz hp actual model)).2
  rw [energyRatio, energyRatio, Real.log_div (by positivity) hdActual.ne',
    Real.log_div (by positivity) hdModel.ne']
  unfold logEnergy at hnum
  linarith

variable {ι : Type*} [Fintype ι]

omit [NormedSpace ℝ E] in
/-- The balanced case of `pred:balanced-comparison`. Each child contributes
`ε K lᵢ` to numerator motion, the weights have total mass at most one, and
`u ≥ 1/2` recovers the relative path-drop factor at the cost of exactly two. -/
theorem balanced_prediction_log_comparison
    {p dActual dModel ε K u : ℝ} (hp : 1 ≤ p)
    (hdModel : 0 < dModel) (hden : dModel ≤ dActual)
    (hε : 0 ≤ ε) (hK : 0 ≤ K) (hu : 1 / 2 ≤ u)
    (l : ι → ℝ) (hsum : ∑ i, l i ≤ 1)
    (actual model : ι → E) (hmotion : ∀ i, ‖actual i - model i‖ ≤ ε * K * l i) :
    Real.log (energyRatio p dActual (∑ i, actual i)) -
      Real.log (energyRatio p dModel (∑ i, model i)) ≤ 2 * p * ε * K * u := by
  have hmotionSum : ‖(∑ i, actual i) - ∑ i, model i‖ ≤ ε * K := by
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ i, (actual i - model i)‖ ≤ ∑ i, ‖actual i - model i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ε * K * l i := Finset.sum_le_sum (fun i _ => hmotion i)
      _ = ε * K * ∑ i, l i := (Finset.mul_sum _ _ _).symm
      _ ≤ ε * K := by nlinarith [mul_nonneg hε hK]
  have h := (prediction_log_comparison hp hdModel hden (∑ i, actual i) (∑ i, model i)).trans
    (mul_le_mul_of_nonneg_left hmotionSum (by linarith))
  have hpεK : 0 ≤ p * ε * K := mul_nonneg (mul_nonneg (by linarith) hε) hK
  nlinarith

/-- Summing the individual shrinkage comparisons produces the actual
one-sided child denominator bound, including its constant term. -/
theorem weighted_radialShrink_denominator_le_of_error {p : ℝ} (hp : 0 < p)
    (δ l l' : ι → ℝ) (hδ : ∀ i, 0 ≤ δ i) (hl : ∀ i, 0 ≤ l i)
    (hl' : ∀ i, 0 ≤ l' i) (x y z : ι → E)
    (hz : ∀ i, ‖z i‖ = l i ^ (1 / p) * ‖x i‖)
    (hmotion : ∀ i, ‖l' i ^ (1 / p) • y i - z i‖ ≤ l i ^ (1 / p) * δ i) :
    1 + ∑ i, l i * ‖radialShrink (δ i) (x i)‖ ^ p ≤
      1 + ∑ i, l' i * ‖y i‖ ^ p := by
  apply add_le_add_right
  exact Finset.sum_le_sum fun i _ =>
    weighted_radialShrink_power_le_of_error (hδ i) hp (hl i) (hl' i)
      (x i) (y i) (z i) (hz i) (hmotion i)

/-- The balanced snapshot comparison with the denominator ordering discharged
by radial shrinkage rather than supplied as a separate analytic assumption. -/
theorem balanced_radial_prediction_log_comparison
    {p ε K u : ℝ} (hp : 1 ≤ p) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hu : 1 / 2 ≤ u)
    (δ l l' : ι → ℝ) (hδ : ∀ i, 0 ≤ δ i) (hl : ∀ i, 0 ≤ l i)
    (hl' : ∀ i, 0 ≤ l' i) (hsum : ∑ i, l i ≤ 1)
    (x y z actual model : ι → E)
    (hz : ∀ i, ‖z i‖ = l i ^ (1 / p) * ‖x i‖)
    (hscaledMotion : ∀ i, ‖l' i ^ (1 / p) • y i - z i‖ ≤ l i ^ (1 / p) * δ i)
    (hnumeratorMotion : ∀ i, ‖actual i - model i‖ ≤ ε * K * l i) :
    Real.log (energyRatio p (1 + ∑ i, l' i * ‖y i‖ ^ p) (∑ i, actual i)) -
      Real.log (energyRatio p (1 + ∑ i, l i * ‖radialShrink (δ i) (x i)‖ ^ p)
        (∑ i, model i)) ≤ 2 * p * ε * K * u := by
  have hp0 : 0 < p := by linarith
  have hpositive : 0 < 1 + ∑ i, l i * ‖radialShrink (δ i) (x i)‖ ^ p := by
    have hnonneg : 0 ≤ ∑ i, l i * ‖radialShrink (δ i) (x i)‖ ^ p :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _)
    linarith
  exact balanced_prediction_log_comparison hp hpositive
    (weighted_radialShrink_denominator_le_of_error hp0 δ l l' hδ hl hl' x y z hz hscaledMotion)
    hε hK hu l hsum actual model hnumeratorMotion

end LipschitzHilbert

end

end OAI
