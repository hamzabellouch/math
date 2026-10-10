import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

lemma smoothTransition_reflect (x : ℝ) :
    Real.smoothTransition (1-x) = 1 - Real.smoothTransition x := by
  unfold Real.smoothTransition
  rw [show 1-(1-x) = x by ring]
  have h : expNegInvGlue x + expNegInvGlue (1-x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  rw [add_comm (expNegInvGlue (1-x))]
  field_simp
  ring

def smoothPositiveSlope (ε t : ℝ) : ℝ := Real.smoothTransition ((t+ε)/(2*ε))

def smoothPositivePart (ε t : ℝ) : ℝ := ∫ s in (-ε)..t, smoothPositiveSlope ε s

lemma smoothPositiveSlope_smooth (ε : ℝ) : ContDiff ℝ ∞ (smoothPositiveSlope ε) := by
  unfold smoothPositiveSlope
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)

lemma smoothPositivePart_hasDeriv (ε t : ℝ) :
    HasDerivAt (smoothPositivePart ε) (smoothPositiveSlope ε t) t := by
  have hc := (smoothPositiveSlope_smooth ε).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma smoothPositivePart_smooth (ε : ℝ) : ContDiff ℝ ∞ (smoothPositivePart ε) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (smoothPositivePart_hasDeriv ε t).differentiableAt, ?_⟩
  have he : deriv (smoothPositivePart ε) = smoothPositiveSlope ε :=
    funext fun t => (smoothPositivePart_hasDeriv ε t).deriv
  rw [he]
  exact smoothPositiveSlope_smooth ε

lemma smoothPositivePart_deriv_bounds (ε t : ℝ) :
    0 ≤ deriv (smoothPositivePart ε) t ∧ deriv (smoothPositivePart ε) t ≤ 1 := by
  rw [(smoothPositivePart_hasDeriv ε t).deriv]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma smoothPositiveSlope_monotone {ε : ℝ} (hε : 0 < ε) :
    Monotone (smoothPositiveSlope ε) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

lemma smoothPositivePart_second_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (deriv (smoothPositivePart ε)) t := by
  rw [show deriv (smoothPositivePart ε) = smoothPositiveSlope ε from
    funext fun t => (smoothPositivePart_hasDeriv ε t).deriv]
  exact (smoothPositiveSlope_monotone hε).deriv_nonneg

lemma smoothPositiveSlope_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε) :
    smoothPositiveSlope ε t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma smoothPositiveSlope_one {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    smoothPositiveSlope ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

lemma smoothPositiveSlope_reflect {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    smoothPositiveSlope ε (-t) = 1 - smoothPositiveSlope ε t := by
  unfold smoothPositiveSlope
  rw [show (-t+ε)/(2*ε) = 1 - (t+ε)/(2*ε) by field_simp; ring]
  exact smoothTransition_reflect _

lemma smoothPositivePart_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε) :
    smoothPositivePart ε t = 0 := by
  unfold smoothPositivePart
  calc
    _ = ∫ s in (-ε)..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_ge ht] at hs
      exact smoothPositiveSlope_zero hε hs.2
    _ = 0 := by simp

lemma smoothPositivePart_at_right {ε : ℝ} (hε : 0 < ε) :
    smoothPositivePart ε ε = ε := by
  have hc := (smoothPositiveSlope_smooth ε).continuous
  have hr : (∫ t in (-ε)..ε, smoothPositiveSlope ε (-t)) = smoothPositivePart ε ε := by
    have hh := intervalIntegral.integral_comp_sub_left (a := -ε) (b := ε)
      (smoothPositiveSlope ε) 0
    simp [smoothPositivePart]
  have he : (∫ t in (-ε)..ε, smoothPositiveSlope ε (-t)) =
      2*ε - smoothPositivePart ε ε := by
    simp_rw [smoothPositiveSlope_reflect hε]
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    simp [smoothPositivePart]
    ring
  linarith

lemma smoothPositivePart_identity {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    smoothPositivePart ε t = t := by
  have hc := (smoothPositiveSlope_smooth ε).continuous
  have hi : (∫ s in ε..t, smoothPositiveSlope ε s) = t-ε := by
    calc
      _ = ∫ s in ε..t, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        exact smoothPositiveSlope_one hε hs.1
      _ = t-ε := by simp
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (a := -ε) (b := ε) (c := t) (μ := volume) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  change smoothPositivePart ε ε + _ = smoothPositivePart ε t at ha
  rw [smoothPositivePart_at_right hε, hi] at ha
  linarith

end AffineBernstein
end

end OAI
