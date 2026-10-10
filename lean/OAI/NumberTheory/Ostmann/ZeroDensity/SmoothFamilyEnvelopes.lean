import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothCharacterFamily
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveCharacterCard

namespace OAI

/-! # Elementary exponential envelopes for the non-low-zero errors -/
namespace Ostmann
open scoped Classical BigOperators

private theorem exponential_split (X t : ℝ) (hX : 0 < X) :
    X * Real.exp (t - Real.log X / 2) = Real.exp (Real.log X / 2 + t) := by
  calc
    _ = Real.exp (Real.log X) * Real.exp (t - Real.log X / 2) := by
      rw [Real.exp_log hX]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

private theorem log_height_bound (Q : ℝ) (hQ : 1 ≤ Q) :
    Real.log (Q * (Q ^ 5 + 2)) ≤ 8 * Q := by
  have hp : 0 < Q := by linarith
  have hpow : 1 ≤ Q ^ 5 := one_le_pow₀ hQ
  calc
    _ ≤ Real.log (3 * Q ^ 6) := by
      apply Real.log_le_log (by positivity)
      nlinarith
    _ = Real.log 3 + 6 * Real.log Q := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hp.ne'), Real.log_pow]
      norm_num
    _ ≤ 8 * Q := by
      have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      have hh := Real.log_le_self hp.le
      linarith

/-- The zeros with real part below one half. -/
theorem smooth_middle_zero_envelope (Cm Cz Q X : ℝ)
    (hm : 0 ≤ Cm) (hz : 0 ≤ Cz) (hQ : 1 ≤ Q) (hX : 0 < X) :
    (Real.exp ((1 / 2 : ℝ) * Real.log X) * Cm) *
      (Cz * Q ^ 2 * (Q ^ 5 + 1) * Real.log (Q * (Q ^ 5 + 2))) ≤
      X * ((16 * Cm * Cz) * Real.exp (8 * Real.log Q - Real.log X / 2)) := by
  have hp : 0 < Q := by linarith
  have hp5 : 1 ≤ Q ^ 5 := one_le_pow₀ hQ
  have he : Q ^ 8 = Real.exp (8 * Real.log Q) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hp] using (Real.exp_nat_mul (Real.log Q) 8).symm
  calc
    _ ≤ (Real.exp ((1 / 2 : ℝ) * Real.log X) * Cm) *
        (Cz * Q ^ 2 * (2 * Q ^ 5) * (8 * Q)) := by
      have hl : 0 ≤ Real.log (Q * (Q ^ 5 + 2)) :=
        Real.log_nonneg (by nlinarith)
      gcongr
      · linarith
      · exact log_height_bound Q hQ
    _ = (16 * Cm * Cz) * (Real.exp ((1 / 2 : ℝ) * Real.log X) * Q ^ 8) := by ring
    _ = _ := by
      rw [he, ← Real.exp_add]
      calc
        _ = (16 * Cm * Cz) * (X * Real.exp (8 * Real.log Q - Real.log X / 2)) := by
          rw [exponential_split X _ hX]
          congr 2
          ring
        _ = _ := by ring

/-- The complete high-ordinate tail, including all its zeros. -/
theorem smooth_high_zero_envelope (Cm Cz Q X : ℝ)
    (hm : 0 ≤ Cm) (hz : 0 ≤ Cz) (hQ : 1 ≤ Q) (hX : 0 ≤ X) :
    (X * Cm) * (2 * (2 * (Cz * Q ^ 2) * (Real.log Q + 3)) ^ 2 *
      Real.exp (-4 * Real.log (1 + Q ^ 5))) ≤
      X * ((128 * Cm * Cz ^ 2) * Real.exp (-Real.log Q)) := by
  have hp : 0 < Q := by linarith
  have hl0 := Real.log_nonneg hQ
  have hl : Real.log Q + 3 ≤ 4 * Q := by
    have hh := Real.log_le_self hp.le
    linarith
  have htail : Real.exp (-4 * Real.log (1 + Q ^ 5)) ≤
      Real.exp (-20 * Real.log Q) := by
    apply Real.exp_le_exp.mpr
    have hh := Real.log_le_log (pow_pos hp 5) (show Q ^ 5 ≤ 1 + Q ^ 5 by linarith)
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hpow : Q ^ 6 = Real.exp (6 * Real.log Q) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hp] using (Real.exp_nat_mul (Real.log Q) 6).symm
  calc
    _ ≤ (X * Cm) * (2 * (2 * (Cz * Q ^ 2) * (4 * Q)) ^ 2 *
        Real.exp (-20 * Real.log Q)) := by
      gcongr
    _ = X * ((128 * Cm * Cz ^ 2) *
        (Q ^ 6 * Real.exp (-20 * Real.log Q))) := by ring
    _ = X * ((128 * Cm * Cz ^ 2) * Real.exp (-14 * Real.log Q)) := by
      rw [hpow, ← Real.exp_add]
      congr 3
      ring
    _ ≤ _ := by gcongr; linarith

/-- The trivial-zero and shifted-contour remainders, summed over the family. -/
theorem smooth_family_remainder_envelope (Cm E Q X : ℝ) (N : ℕ)
    (hm : 0 ≤ Cm) (hE : 0 ≤ E) (hQ : 1 ≤ Q) (hX : 1 ≤ X)
    (hN : (N : ℝ) ≤ Q ^ 2) :
    (N : ℝ) * (Cm + E / Real.sqrt X * Real.log (2 * Q)) ≤
      X * ((Cm + 2 * E) * Real.exp (3 * Real.log Q - Real.log X / 2)) := by
  have hp : 0 < Q := by linarith
  have hXp : 0 < X := by linarith
  have hs : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa)
  have hi : E / Real.sqrt X ≤ E := (div_le_self hE hs)
  have hl0 : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
  have hl : Real.log (2 * Q) ≤ 2 * Q := Real.log_le_self (by positivity)
  have hpow : Q ^ 3 = Real.exp (3 * Real.log Q) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hp] using (Real.exp_nat_mul (Real.log Q) 3).symm
  have hexp : 1 ≤ Real.exp (Real.log X / 2) :=
    Real.one_le_exp (by have hh := Real.log_nonneg hX; linarith)
  calc
    _ ≤ Q ^ 2 * (Cm + E * (2 * Q)) := by gcongr
    _ ≤ (Cm + 2 * E) * Q ^ 3 := by
      have hh := mul_le_mul_of_nonneg_left hQ (mul_nonneg hm (sq_nonneg Q))
      nlinarith
    _ ≤ (Cm + 2 * E) * (Real.exp (Real.log X / 2) * Q ^ 3) := by
      gcongr
      exact le_mul_of_one_le_left (by positivity) hexp
    _ = _ := by
      rw [hpow, ← Real.exp_add]
      calc
        _ = (Cm + 2 * E) * (X * Real.exp (3 * Real.log Q - Real.log X / 2)) := by
          rw [exponential_split X _ hXp]
        _ = _ := by ring

end Ostmann

end OAI
