import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroQuotientBound
import OAI.NumberTheory.Ostmann.ZeroDensity.LogDerivativeContourDisk

namespace OAI

/-! # The normalized logarithm of the quotient by all nearby zeros -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem character_contour_quotient_log_bound (χ : PrimitiveComplexCharacter) (t M : ℝ)
    (hM : 1 ≤ M)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M)
    (g : ℂ → ℂ) (hg : ∀ s, AnalyticAt ℂ g s)
    (he : ∀ s, χ.L s = characterZeroPolynomial χ (characterContourZeros χ t) s * g s)
    (hne : ∀ s ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ), g s ≠ 0) :
    ∀ z ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ),
      Real.log ‖g z‖ - Real.log ‖g (characterZeroCenter t)‖ ≤
        Real.log (3 * M) +
          (∑ w ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L w : ℝ)) * Real.log 21 := by
  let N := ∑ w ∈ characterContourZeros χ t, analyticOrderNatAt χ.L w
  have hc : characterZeroCenter t ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ) :=
    mem_closedBall_self (by norm_num)
  have hgc : 0 < ‖g (characterZeroCenter t)‖ := norm_pos_iff.mpr (hne _ hc)
  have hp : ‖characterZeroPolynomial χ (characterContourZeros χ t) (characterZeroCenter t)‖ ≤
      (21 / 8 : ℝ) ^ N := by
    apply characterZeroPolynomial_norm_le χ _ _ _ (by norm_num)
    intro w hw
    rw [norm_sub_rev]
    exact (mem_closedBall_iff_norm.mp ((mem_characterContourZeros χ t w).mp hw).1)
  have hlo : (1 / 3 : ℝ) ≤ (21 / 8 : ℝ) ^ N * ‖g (characterZeroCenter t)‖ := by
    have hh := χ.L_lower_re_two (characterZeroCenter t) (characterZeroCenter_re t)
    rw [he, norm_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  have hpow : (8 : ℝ) ^ N * (21 / 8 : ℝ) ^ N = 21 ^ N := by
    rw [← mul_pow]
    norm_num
  have hm : M * 8 ^ N ≤ 3 * M * 21 ^ N * ‖g (characterZeroCenter t)‖ := by
    calc
      _ = (3 * M * 8 ^ N) * (1 / 3) := by ring
      _ ≤ (3 * M * 8 ^ N) * ((21 / 8) ^ N * ‖g (characterZeroCenter t)‖) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = 3 * M * (8 ^ N * (21 / 8) ^ N) * ‖g (characterZeroCenter t)‖ := by ring
      _ = _ := by rw [hpow]
  intro z hz
  have hzouter : z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ) :=
    closedBall_subset_closedBall (by norm_num) hz
  have hupper := character_contour_quotient_bound χ t M (by linarith) hbound g hg he z hzouter
  have hratio : ‖g z‖ / ‖g (characterZeroCenter t)‖ ≤ 3 * M * 21 ^ N :=
    (div_le_iff₀ hgc).mpr (hupper.trans hm)
  have hnz : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z hz)
  rw [← Real.log_div hnz.ne' hgc.ne']
  apply (Real.log_le_log (div_pos hnz hgc) hratio).trans_eq
  rw [Real.log_mul (by positivity : 3 * M ≠ 0) (by positivity : (21 : ℝ) ^ N ≠ 0),
    Real.log_pow]
  simp only [N, Nat.cast_sum]

end Ostmann

end OAI
