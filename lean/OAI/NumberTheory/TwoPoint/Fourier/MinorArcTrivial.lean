import OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling

namespace OAI

/-! The exact trivial bound used for bounded ranges of the short length. -/

namespace TwoPointCorrelations

open Finset

lemma minor_arc_short_sum_trivial (F : ℕ → ℂ) (hF : OneBounded F)
    (H k : ℕ) (α : ℝ) : ‖shortExponentialSum F H α k‖ ≤ H := by
  rw [shortExponentialSum_at_nat]
  calc
    _ ≤ ∑ n ∈ Icc (k + 1) (k + H), ‖F n * additiveCharacter α n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc (k + 1) (k + H), (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul, norm_additiveCharacter, mul_one]
      exact hF n (by have hh := (mem_Icc.mp hn).1; omega)
    _ = H := by
      simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
      congr 1
      omega

lemma minor_arc_short_integral_trivial (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) (α : ℝ) : shortExponentialIntegral F X H α ≤ (X : ℝ) * H := by
  rw [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ _k ∈ range X, (H : ℝ) :=
      sum_le_sum (fun k _ => minor_arc_short_sum_trivial F hF H k α)
    _ = _ := by simp

end TwoPointCorrelations

end OAI
