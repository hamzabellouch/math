import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimePartialSummation

namespace OAI

/-! Calculus for the variable denominator in the second prime convolution. -/

namespace TwoPointCorrelations

open MeasureTheory

noncomputable def halaszDenominatorWeight (X x : ℝ) : ℝ :=
  (Real.log X - Real.log x)⁻¹

lemma halasz_log_gap_pos {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    0 < Real.log X - Real.log x := sub_pos.mpr (Real.log_lt_log hx hxX)

lemma halasz_denominator_hasDerivAt {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    HasDerivAt (halaszDenominatorWeight X)
      (x⁻¹ / (Real.log X - Real.log x) ^ 2) x := by
  have hg := (hasDerivAt_const x (Real.log X)).sub (Real.hasDerivAt_log hx.ne')
  have hd := hg.inv (ne_of_gt (halasz_log_gap_pos hx hxX))
  convert hd using 1
  · rfl
  · simp only [Pi.sub_apply, zero_sub, neg_neg]

lemma halasz_denominator_primitive {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    HasDerivAt (fun y => -Real.log (Real.log X - Real.log y))
      (halaszDenominatorWeight X x / x) x := by
  have hg := (hasDerivAt_const x (Real.log X)).sub (Real.hasDerivAt_log hx.ne')
  have hd := ((Real.hasDerivAt_log (ne_of_gt (halasz_log_gap_pos hx hxX))).comp x hg).neg
  convert hd using 1
  · rfl
  · simp only [zero_sub, halaszDenominatorWeight]
    ring

lemma halasz_denominator_deriv_continuous {X a b : ℝ} (ha : 0 < a)
    (hbX : b < X) : ContinuousOn (deriv (halaszDenominatorWeight X)) (Set.Icc a b) := by
  have hxn (x : ℝ) (hx : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hgap (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log X - Real.log x ≠ 0 :=
    (halasz_log_gap_pos (ha.trans_le hx.1) (hx.2.trans_lt hbX)).ne'
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  apply ContinuousOn.congr (f := fun x => x⁻¹ / (Real.log X - Real.log x) ^ 2)
  · exact (continuousOn_id.inv₀ hxn).div
      ((continuousOn_const.sub hlog).pow 2) (fun x hx => pow_ne_zero 2 (hgap x hx))
  · intro x hx
    exact (halasz_denominator_hasDerivAt (ha.trans_le hx.1) (hx.2.trans_lt hbX)).deriv

lemma halasz_denominator_integral {X a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbX : b < X) :
    (∫ t in a..b, halaszDenominatorWeight X t / t) =
      Real.log (Real.log X - Real.log a) - Real.log (Real.log X - Real.log b) := by
  have hf : ContinuousOn (fun t => halaszDenominatorWeight X t / t) (Set.Icc a b) := by
    have hxn (x : ℝ) (hx : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le hx.1).ne'
    have hgap (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log X - Real.log x ≠ 0 :=
      (halasz_log_gap_pos (ha.trans_le hx.1) (hx.2.trans_lt hbX)).ne'
    have hlog : ContinuousOn Real.log (Set.Icc a b) :=
      fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
    exact ((continuousOn_const.sub hlog).inv₀ hgap).div continuousOn_id hxn
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => halasz_denominator_primitive
      (ha.trans_le (show x ∈ Set.Icc a b from by simpa [Set.uIcc_of_le hab] using hx).1)
      ((show x ∈ Set.Icc a b from by simpa [Set.uIcc_of_le hab] using hx).2.trans_lt hbX))
    (hf.intervalIntegrable_of_Icc hab)
  linarith

end TwoPointCorrelations

end OAI
