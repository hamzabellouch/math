import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingWeights
import Mathlib.Algebra.Order.Floor.Semifield

namespace OAI

/-! The literal logarithmic bin places T/(dq) between X exp(-eta)
and X. Floor normalization introduces a scalar of norm at most one. -/

namespace TwoPointCorrelations

lemma actualPaddingBin_cutoff (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (η X : ℝ) (hX : 0 < X) (j : ℤ)
    (hb : actualPaddingBin η (Real.log d) j q) :
    X * Real.exp (-η) ≤ (X * Real.exp ((j : ℝ) * η)) / (d * q : ℕ) ∧
      (X * Real.exp ((j : ℝ) * η)) / (d * q : ℕ) ≤ X := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hu : (0 : ℝ) < (d * q : ℕ) := by exact_mod_cast Nat.mul_pos hd hq
  have hlog : Real.log (d * q : ℕ) = Real.log q + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hdR.ne' hqR.ne']
    ring
  have hl : Real.exp ((j : ℝ) * η) ≤ (d * q : ℕ) := by
    calc
      _ ≤ Real.exp (Real.log (d * q : ℕ)) := Real.exp_le_exp.mpr (by rw [hlog]; exact hb.1)
      _ = _ := Real.exp_log hu
  have hh : (d * q : ℕ) ≤ Real.exp (((j : ℝ) + 1) * η) := by
    calc
      _ = Real.exp (Real.log (d * q : ℕ)) := (Real.exp_log hu).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by rw [hlog]; exact hb.2.le)
  constructor
  · apply (le_div_iff₀ hu).mpr
    have he : Real.exp (-η) * Real.exp (((j : ℝ) + 1) * η) =
        Real.exp ((j : ℝ) * η) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (X * Real.exp (-η)) * Real.exp (((j : ℝ) + 1) * η) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by rw [mul_assoc, he]
  · apply (div_le_iff₀ hu).mpr
    exact mul_le_mul_of_nonneg_left hl hX.le

lemma floor_cutoff_weight_norm_le (T : ℝ) (hT : 0 < T) :
    ‖(⌊T⌋₊ : ℂ) / (T : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  exact (div_le_one hT).mpr (Nat.floor_le hT.le)

end TwoPointCorrelations

end OAI
