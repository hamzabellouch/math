import OAI.NumberTheory.TwoPoint.Halasz.HalaszDenominatorCalculus

namespace OAI

/-! The weighted prime mass left by the second logarithmic convolution is
only of order log log X, with an absolute constant. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_denominator_prime_error {X a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hbX : b < X) :
    (∑ p ∈ mrtPrimeBand a b,
      halaszDenominatorWeight X p * (Real.log (p : ℝ) / p)) ≤
      Real.log (Real.log X - Real.log a) - Real.log (Real.log X - Real.log b) +
        2 * halaszMertensConstant * halaszDenominatorWeight X b := by
  let w := halaszDenominatorWeight X
  let E := fun x => partialCoefficientSum halaszPrimeWeight x - Real.log x
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hxpos (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 < x := ha0.trans_le hx.1
  have hxX (x : ℝ) (hx : x ∈ Set.Icc a b) : x < X := hx.2.trans_lt hbX
  have hwpos (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 ≤ w x :=
    inv_nonneg.mpr (halasz_log_gap_pos (hxpos x hx) (hxX x hx)).le
  have hE (x : ℝ) (hx : x ∈ Set.Icc a b) : |E x| ≤ halaszMertensConstant := by
    dsimp [E]
    rw [halasz_prime_weight_prefix]
    exact halasz_prime_prefix_mass (ha.trans hx.1)
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) : HasDerivAt w (deriv w x) x :=
    (halasz_denominator_hasDerivAt (hxpos x hx) (hxX x hx)).differentiableAt.hasDerivAt
  have hdc : ContinuousOn (deriv w) (Set.Icc a b) :=
    halasz_denominator_deriv_continuous ha0 hbX
  have hdi : IntervalIntegrable (deriv w) volume a b := hdc.intervalIntegrable_of_Icc hab
  have hint : (∫ x in a..b, deriv w x) = w b - w a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd x (by simpa [Set.uIcc_of_le hab] using hx)) hdi
  have hi : |∫ x in a..b, deriv w x * E x| ≤ halaszMertensConstant * (w b - w a) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun x => deriv w x * E x) (g := fun x => halaszMertensConstant * deriv w x) hab
      (Filter.Eventually.of_forall (fun x hx => by
        have hxi : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2⟩
        have hd0 : 0 ≤ deriv w x := by
          rw [(halasz_denominator_hasDerivAt (hxpos x hxi) (hxX x hxi)).deriv]
          exact div_nonneg (inv_nonneg.mpr (hxpos x hxi).le) (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd0]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hE x hxi) hd0))
      (hdi.const_mul halaszMertensConstant)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, hint] at hb
    exact hb
  have hAbel := halasz_prime_partial_summation a b ha0 hab w
    (fun x hx => (hd x hx).differentiableAt) hdc
  rw [halasz_denominator_integral ha0 hab hbX] at hAbel
  change _ = w b * E b - w a * E a - _ at hAbel
  have heb := mul_le_mul_of_nonneg_left (abs_le.mp (hE b ⟨hab, le_rfl⟩)).2
    (hwpos b ⟨hab, le_rfl⟩)
  have hea := mul_le_mul_of_nonneg_left (abs_le.mp (hE a ⟨le_rfl, hab⟩)).1
    (hwpos a ⟨le_rfl, hab⟩)
  have hilow := (abs_le.mp hi).1
  dsimp [w] at *
  linarith

theorem halasz_denominator_prime_mass {X L : ℝ} (hL : 1 ≤ L) (hLX : L ≤ X / 2) :
    (∑ p ∈ mrtPrimeBand L (X / 2),
      Real.log (p : ℝ) / ((p : ℝ) * Real.log (X / p))) ≤
      Real.log (Real.log X) - Real.log (Real.log 2) +
        2 * halaszMertensConstant / Real.log 2 := by
  have hX : 2 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hhX : X / 2 < X := by linarith
  have he : Real.log X - Real.log (X / 2) = Real.log 2 := by
    rw [Real.log_div hX0.ne' (by norm_num)]
    ring
  have hgap := halasz_log_gap_pos hL0 (lt_of_le_of_lt hLX hhX)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hmain := Real.log_le_log hgap (show Real.log X - Real.log L ≤ Real.log X by linarith)
  have hb := halasz_denominator_prime_error hL hLX hhX
  have hsum : (∑ p ∈ mrtPrimeBand L (X / 2),
      Real.log (p : ℝ) / ((p : ℝ) * Real.log (X / p))) =
      ∑ p ∈ mrtPrimeBand L (X / 2),
        halaszDenominatorWeight X p * (Real.log (p : ℝ) / p) := by
    apply sum_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mrtPrimeBand_prime hp).pos
    rw [Real.log_div hX0.ne' hp0.ne', halaszDenominatorWeight]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsum]
  dsimp [halaszDenominatorWeight]
  simp only [halaszDenominatorWeight, he, ← div_eq_mul_inv] at hb
  linarith

end TwoPointCorrelations

end OAI
