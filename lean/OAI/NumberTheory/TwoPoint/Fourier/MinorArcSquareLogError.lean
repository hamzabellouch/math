import OAI.NumberTheory.TwoPoint.Fourier.MinorArcPrimeRanges

namespace OAI

/-! Absorbing the single prime-square error in the logarithmic saving. -/

namespace TwoPointCorrelations

open Finset

lemma minor_arc_square_log_error (P : Finset ℕ) (X H : ℕ) (hHX : H ≤ X)
    (hlogH : 1 ≤ Real.log (H : ℝ)) (hloglogH : 1 ≤ Real.log (Real.log (H : ℝ)))
    (hP : ∀ p ∈ P, (Real.log (H : ℝ)) ^ 5 ≤ (p : ℝ) ∧ p ≤ H) :
    3 * (H : ℝ) * (X + H) * (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤
      12 * (X : ℝ) * H * Real.log (Real.log (H : ℝ)) / Real.log (H : ℝ) := by
  let W := (Real.log (H : ℝ)) ^ 5
  have hL : 0 < Real.log (H : ℝ) := by linarith
  have hW : 0 < W := by dsimp [W]; positivity
  have hR : 0 < ⌈W⌉₊ := Nat.one_le_ceil_iff.mpr hW
  have htail := minor_arc_square_reciprocal_sum P ⌈W⌉₊ H hR
    (fun p hp => ⟨Nat.ceil_le.mpr (hP p hp).1, (hP p hp).2⟩)
  have hsum : (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 2 / W :=
    htail.trans (div_le_div_of_nonneg_left (by norm_num) hW (Nat.le_ceil W))
  have hpow : Real.log (H : ℝ) ≤ W := le_self_pow₀ hlogH (by norm_num : (5 : ℕ) ≠ 0)
  have hratio : 1 / W ≤ Real.log (Real.log (H : ℝ)) / Real.log (H : ℝ) := by
    exact (one_div_le_one_div_of_le hL hpow).trans
      (div_le_div_of_nonneg_right hloglogH hL.le)
  have hXH : (X : ℝ) + H ≤ 2 * X := by exact_mod_cast (by omega : X + H ≤ 2 * X)
  calc
    3 * (H : ℝ) * (X + H) * (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤
        3 * (H : ℝ) * (X + H) * (2 / W) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 3 * (H : ℝ) * (2 * X) * (2 / W) := by gcongr
    _ = (12 * (X : ℝ) * H) * (1 / W) := by ring
    _ ≤ (12 * (X : ℝ) * H) * (Real.log (Real.log (H : ℝ)) / Real.log (H : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
