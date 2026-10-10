import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftAverage
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTScale

namespace OAI

/-! Explicit power arithmetic in the rough-shift Fourier argument. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma rough_reciprocal_mass_le_sup (Z : Finset ℕ) (h : ℕ) (U : ℝ)
    (hU : ‖roughFourierPolynomial Z h 0‖ ≤ U) :
    (∑ z ∈ Z, (z : ℝ)⁻¹) ≤ U := by
  have he : roughFourierPolynomial Z h 0 = ((∑ z ∈ Z, (z : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [roughFourierPolynomial, fourierPolynomial, fourier_eval_zero, mul_one,
      Complex.ofReal_sum, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [he, Complex.norm_real, Real.norm_of_nonneg
    (sum_nonneg (fun z _ => by positivity))] at hU
  exact hU

lemma rough_window_sqrt_bound (D h : ℕ) :
    Real.sqrt (D : ℝ) * Real.sqrt ((2 * (h : ℝ) + 1) * D) ≤
      (2 * (h : ℝ) + 1) * D := by
  have ht : (D : ℝ) ≤ (2 * (h : ℝ) + 1) * D := by
    nlinarith [show (0 : ℝ) ≤ (h : ℝ) * D by positivity]
  calc
    _ ≤ Real.sqrt ((2 * (h : ℝ) + 1) * D) *
        Real.sqrt ((2 * (h : ℝ) + 1) * D) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht) (Real.sqrt_nonneg _)
    _ = _ := by rw [← pow_two, Real.sq_sqrt (by positivity)]

lemma rough_fourier_exponent_identity (L : ℝ) (hL : 0 < L) :
    L ^ (-99 / 100 : ℝ) * L ^ (-4 / 5 : ℝ) * L ^ (-99 / 25 : ℝ) /
        (L ^ (-21 / 20 : ℝ)) ^ (4 : ℕ) = L ^ (-31 / 20 : ℝ) := by
  have hp : (L ^ (-21 / 20 : ℝ)) ^ (4 : ℕ) = L ^ ((-21 / 20 : ℝ) * 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  rw [hp, ← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_sub hL]
  norm_num

lemma rough_low_term_bound (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (ε * ((Y : ℝ) * (Real.sqrt D * Real.sqrt ((2 * (h : ℝ) + 1) * D)))) /
      ((Y : ℝ) * D) ≤ (2 * (h : ℝ) + 1) * ε := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  calc
    _ ≤ (ε * ((Y : ℝ) * ((2 * (h : ℝ) + 1) * D))) / ((Y : ℝ) * D) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (rough_window_sqrt_bound D h) hYr.le) hε)
        (mul_pos hYr hDr).le
    _ = _ := by field_simp

lemma rough_high_term_identity (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (L U V K : ℝ) (hL : 0 < L) :
    (((U * L ^ (-99 / 100 : ℝ)) * ((2 * (h : ℝ) + 1) * D) *
        (K * Y * D * L ^ (-4 / 5 : ℝ)) / (L ^ (-21 / 20 : ℝ)) ^ (4 : ℕ)) *
        (V / D * L ^ (-99 / 25 : ℝ))) / ((Y : ℝ) * D) =
      (2 * (h : ℝ) + 1) * U * V * K * L ^ (-31 / 20 : ℝ) := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hYr : (Y : ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpow : L ^ (-21 / 20 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  calc
    _ = ((2 * (h : ℝ) + 1) * U * V * K) *
        (L ^ (-99 / 100 : ℝ) * L ^ (-4 / 5 : ℝ) * L ^ (-99 / 25 : ℝ) /
          (L ^ (-21 / 20 : ℝ)) ^ (4 : ℕ)) := by
      field_simp
    _ = _ := by rw [rough_fourier_exponent_identity L hL]

/-- The Fourier bound has the exact exponent `-21/20`. The stronger
`-31/20` contribution is absorbed only at this final numerical step. -/
theorem rough_shift_power_bound (f g : ℕ → ℂ) (hf : OneBounded f)
    (hg : OneBounded g) (Z : Finset ℕ) (D h Y : ℕ) (hD : 0 < D) (hY : 0 < Y)
    (hZ : ∀ z ∈ Z, z ≤ 2 * D) (L U V K : ℝ)
    (hL : 1 ≤ L) (hU : 0 ≤ U) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (hendpoint : (D : ℝ) / Y ≤ L ^ (-21 / 20 : ℝ))
    (hB : ∀ θ, ‖roughFourierPolynomial Z h θ‖ ≤ U * L ^ (-99 / 100 : ℝ))
    (hfourth : (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4
      ∂AddCircle.haarAddCircle) ≤ V / D * L ^ (-99 / 25 : ℝ))
    (hF : ∀ θ, (∑ v ∈ range Y, ‖forwardWindowPolynomial f D (v + 1) θ‖) ≤
      K * Y * D * L ^ (-4 / 5 : ℝ)) :
    ‖roughShiftAverage f g Z h Y‖ ≤
      (2 * U + (2 * (h : ℝ) + 1) + (2 * (h : ℝ) + 1) * U * V * K) *
        L ^ (-21 / 20 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hmass : (∑ z ∈ Z, (z : ℝ)⁻¹) ≤ U := by
    apply (rough_reciprocal_mass_le_sup Z h _ (hB 0)).trans
    have hp : L ^ (-99 / 100 : ℝ) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hL (show (-99 / 100 : ℝ) ≤ 0 by norm_num)
    exact (mul_le_mul_of_nonneg_left hp hU).trans_eq (mul_one U)
  have he : 2 * (D : ℝ) / Y * (∑ z ∈ Z, (z : ℝ)⁻¹) ≤
      2 * U * L ^ (-21 / 20 : ℝ) := by
    calc
      _ = 2 * ((D : ℝ) / Y) * (∑ z ∈ Z, (z : ℝ)⁻¹) := by ring
      _ ≤ 2 * L ^ (-21 / 20 : ℝ) * U :=
        mul_le_mul (mul_le_mul_of_nonneg_left hendpoint (by norm_num)) hmass
          (sum_nonneg (fun z _ => by positivity)) (by positivity)
      _ = _ := by ring
  have hraw := rough_shift_average_bound f g hf hg Z D h Y hD hY hZ
    (L ^ (-21 / 20 : ℝ)) (U * L ^ (-99 / 100 : ℝ))
    (V / D * L ^ (-99 / 25 : ℝ)) (K * Y * D * L ^ (-4 / 5 : ℝ))
    (Real.rpow_pos_of_pos hLp _) (by positivity) (by positivity) hB hfourth hF
  have hlow := rough_low_term_bound D h Y hD hY
    (L ^ (-21 / 20 : ℝ)) (Real.rpow_nonneg hLp.le _)
  have hhigh := rough_high_term_identity D h Y hD hY L U V K hLp
  have hgap : L ^ (-31 / 20 : ℝ) ≤ L ^ (-21 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  apply hraw.trans
  rw [add_div, hhigh]
  have ht := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ (2 * (h : ℝ) + 1) * U * V * K by positivity)
  nlinarith

end TwoPointCorrelations

end OAI
