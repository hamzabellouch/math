import OAI.NumberTheory.TwoPoint.Bounds.PrimeAlphabetSize
import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftEndpoints

namespace OAI

/-! An absolute long-interval scale survives extraction of every bounded
padding divisor and every partial tuple product, including both floor operations. -/

namespace TwoPointCorrelations

lemma extracted_window_lower (L T : ℝ) (u : ℕ) (hL : 1000 ≤ L)
    (hu : 0 < u) (hT : Real.exp (L ^ (1000 : ℝ)) ≤ T)
    (hupper : (u : ℝ) ≤ Real.exp (100 * L ^ 2 + 2 * L)) :
    Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ ((⌊T⌋₊ / u : ℕ) : ℝ) := by
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hp : L ^ (4 : ℕ) ≤ L ^ (1000 : ℝ) := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hLone (show (4 : ℝ) ≤ 1000 by norm_num)
  have hsq : (1000 : ℝ) ≤ L ^ 2 := by nlinarith
  have hfour : 1000 * L ^ 2 ≤ L ^ (4 : ℕ) := by
    calc
      _ ≤ (L ^ 2) * (L ^ 2) := mul_le_mul_of_nonneg_right hsq (sq_nonneg L)
      _ = _ := by ring
  have hgap : 3 ≤ (1 / 2 : ℝ) * L ^ (1000 : ℝ) - (100 * L ^ 2 + 2 * L) := by
    nlinarith
  have he : 4 ≤ Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) - (100 * L ^ 2 + 2 * L)) := by
    linarith [Real.add_one_le_exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) - (100 * L ^ 2 + 2 * L))]
  let E := Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ))
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have hup : (0 : ℝ) < u := by exact_mod_cast hu
  have huone : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hEu : 1 ≤ E * u := one_le_mul_of_one_le_of_one_le hE huone
  have hsmall : 4 * (E * u) ≤ T := by
    apply le_trans _ hT
    calc
      _ ≤ 4 * (E * Real.exp (100 * L ^ 2 + 2 * L)) := by gcongr
      _ = 4 * Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) + (100 * L ^ 2 + 2 * L)) := by
        congr 1
        exact (Real.exp_add _ _).symm
      _ ≤ Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) - (100 * L ^ 2 + 2 * L)) *
          Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ) + (100 * L ^ 2 + 2 * L)) := by
        exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hfloor : 2 * (E * u) ≤ (⌊T⌋₊ : ℝ) := by
    have ht := Nat.lt_floor_add_one T
    nlinarith
  have hdiv : (⌊T⌋₊ : ℝ) < (u : ℝ) * (((⌊T⌋₊ / u : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ ⌊T⌋₊ hu
  have hratio : 2 * E < ((⌊T⌋₊ / u : ℕ) : ℝ) + 1 := by
    apply (mul_lt_mul_iff_right₀ hup).mp
    nlinarith
  change E ≤ _
  linarith

end TwoPointCorrelations

end OAI
