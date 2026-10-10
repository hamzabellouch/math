import Mathlib

namespace OAI

/-!
# Threshold reconstruction in the initial estimator

Deterministic reconstruction from Section 3 of the September 24, 2026
edit-distance manuscript.  Concentration is kept separate: the thresholds
can influence the approximate child costs, so no independence assumption
about those approximate costs is made here.
-/

namespace EditApproximation

/-- A threshold contribution of the coarse estimator. -/
noncomputable def thresholdContribution (threshold scale value : ℝ) : ℝ :=
  if threshold ≤ value then max value scale else 0

theorem thresholdContribution_nonneg {threshold scale value : ℝ} (hscale : 0 ≤ scale) :
    0 ≤ thresholdContribution threshold scale value := by
  unfold thresholdContribution
  split_ifs
  · exact hscale.trans (le_max_right _ _)
  · rfl

theorem thresholdContribution_mono {threshold scale value value' : ℝ}
    (hscale : 0 ≤ scale) (hle : value ≤ value') :
    thresholdContribution threshold scale value ≤
      thresholdContribution threshold scale value' := by
  unfold thresholdContribution
  split_ifs with h h'
  · exact max_le_max hle le_rfl
  · exact False.elim (h' (h.trans hle))
  · exact hscale.trans (le_max_right _ _)
  · rfl

/-- Pathwise threshold sandwich. In particular, `estimate` may depend on
`threshold`; the proof only uses its two deterministic error bounds. -/
theorem threshold_sandwich {threshold scale estimate lower upper lam : ℝ}
    (hscale : 0 ≤ scale) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hlower : (1 + lam) * lower - lam * threshold ≤ estimate)
    (hupper : estimate ≤ (1 - lam) * upper + lam * threshold) :
    thresholdContribution threshold scale lower ≤
        thresholdContribution threshold scale estimate ∧
      thresholdContribution threshold scale estimate ≤
        thresholdContribution threshold scale upper := by
  constructor
  · by_cases hlt : threshold ≤ lower
    · have hprod := mul_nonneg hlam (sub_nonneg.mpr hlt)
      have hle : lower ≤ estimate := by nlinarith
      exact thresholdContribution_mono hscale hle
    · simp only [thresholdContribution, ite_eq_right hlt]
      exact thresholdContribution_nonneg hscale
  · by_cases hlt : threshold ≤ estimate
    · have hprod := mul_le_mul_of_nonneg_left hlt hlam
      have hle : estimate ≤ upper := by nlinarith
      exact thresholdContribution_mono hscale hle
    · simp only [thresholdContribution, ite_eq_right hlt]
      exact thresholdContribution_nonneg hscale

/-- The precise factors used in the manuscript's threshold sandwich. -/
theorem coarse_threshold_sandwich {threshold scale estimate trueCost f lam : ℝ}
    (hscale : 0 ≤ scale) (hf : 0 < f) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hlower : trueCost / f - lam * threshold ≤ estimate)
    (hupper : estimate ≤ f * trueCost + lam * threshold) :
    thresholdContribution threshold scale (trueCost / (f * (1 + lam))) ≤
        thresholdContribution threshold scale estimate ∧
      thresholdContribution threshold scale estimate ≤
        thresholdContribution threshold scale (f * trueCost / (1 - lam)) := by
  apply threshold_sandwich hscale hlam hlamone
  · have hid : (1 + lam) * (trueCost / (f * (1 + lam))) = trueCost / f := by
      field_simp
    simpa only [hid] using hlower
  · have hid : (1 - lam) * (f * trueCost / (1 - lam)) = f * trueCost := by
      field_simp [ne_of_gt (sub_pos.mpr hlamone)]
    simpa only [hid] using hupper

/-- Combining the two true-cost concentration events with the pathwise
sandwich updates the structural factor from `f` to
`f * (1 + lam) / (1 - lam)`.  Neither event conditions on child accuracy. -/
theorem coarse_reconstruction {ι : Type*} (children : Finset ι)
    (threshold estimate trueCost : ι → ℝ) (scale allowance f lam : ℝ)
    (hscale : 0 ≤ scale) (hf : 0 < f) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hchildLower : ∀ i ∈ children, trueCost i / f - lam * threshold i ≤ estimate i)
    (hchildUpper : ∀ i ∈ children, estimate i ≤ f * trueCost i + lam * threshold i)
    (hconcentrationLower :
      (1 - lam) * (∑ i ∈ children, trueCost i / (f * (1 + lam))) - allowance ≤
        ∑ i ∈ children, thresholdContribution (threshold i) scale
          (trueCost i / (f * (1 + lam))))
    (hconcentrationUpper :
      (∑ i ∈ children, thresholdContribution (threshold i) scale
        (f * trueCost i / (1 - lam))) ≤
          (1 + lam) * (∑ i ∈ children, f * trueCost i / (1 - lam)) + allowance) :
    (∑ i ∈ children, trueCost i) / (f * (1 + lam) / (1 - lam)) - allowance ≤
        ∑ i ∈ children, thresholdContribution (threshold i) scale (estimate i) ∧
      (∑ i ∈ children, thresholdContribution (threshold i) scale (estimate i)) ≤
        (f * (1 + lam) / (1 - lam)) * (∑ i ∈ children, trueCost i) + allowance := by
  have hsandwich (i : ι) (hi : i ∈ children) := coarse_threshold_sandwich
    hscale hf hlam hlamone (hchildLower i hi) (hchildUpper i hi)
  constructor
  · have hlo := hconcentrationLower.trans
      (Finset.sum_le_sum fun i hi => (hsandwich i hi).1)
    have hid : (1 - lam) * (∑ i ∈ children, trueCost i / (f * (1 + lam))) =
        (∑ i ∈ children, trueCost i) / (f * (1 + lam) / (1 - lam)) := by
      rw [← Finset.sum_div]
      field_simp
    simpa only [hid] using hlo
  · have hhi := (Finset.sum_le_sum fun i hi => (hsandwich i hi).2).trans
      hconcentrationUpper
    have hid : (1 + lam) * (∑ i ∈ children, f * trueCost i / (1 - lam)) =
        (f * (1 + lam) / (1 - lam)) * (∑ i ∈ children, trueCost i) := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
      ring
    simpa only [hid] using hhi

end EditApproximation

end OAI
