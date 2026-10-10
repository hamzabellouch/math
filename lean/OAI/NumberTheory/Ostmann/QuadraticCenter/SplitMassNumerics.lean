import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.NumberTheory.Ostmann.Construction.RetainedSplitPrimeMass

namespace OAI

/-! # Explicit numerical margin in the split-prime estimate -/

namespace Ostmann

open scoped BigOperators

theorem exp_neg_twelve_fifths_le : Real.exp (-(12 / 5 : ℝ)) ≤ 1 / 11 := by
  have he : (11 : ℝ) ≤ Real.exp (12 / 5) := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 12 / 5) 10)
    norm_num [Finset.sum_range_succ]
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

/-- A cutoff whose logarithm is at least 0.48L suffices for the exponent
comparison tail. The later choices have logarithm asymptotic to 0.5L. -/
theorem split_prime_tail_factor_bound (Q : ℕ) (L : ℝ) (hQ : 0 < Q) (hL : 0 < L)
    (hlog : (12 / 25 : ℝ) * L ≤ Real.log (Q : ℝ)) :
    (Q : ℝ) ^ (-(10 / L) / 2) ≤ 1 / 11 := by
  have hneg : -(5 / L) ≤ (0 : ℝ) := neg_nonpos.mpr (div_nonneg (by norm_num) hL.le)
  have hm := mul_le_mul_of_nonpos_right hlog hneg
  have hid : ((12 / 25 : ℝ) * L) * -(5 / L) = -(12 / 5 : ℝ) := by
    field_simp
    ring
  rw [hid] at hm
  rw [Real.rpow_def_of_pos (by exact_mod_cast hQ)]
  have he : Real.log (Q : ℝ) * (-(10 / L) / 2) ≤ -(12 / 5 : ℝ) := by
    convert hm using 1
    ring
  exact (Real.exp_le_exp.mpr he).trans exp_neg_twelve_fifths_le

/-- The elementary margin leaves room for all constant and Siegel errors. -/
theorem split_mass_numeric_margin (L C B E t : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hCsmall : C ≤ L / 10000) (hBsmall : B ≤ L / 10000)
    (hEsmall : E ≤ L / 10000) (ht : t ≤ 1 / 11) :
    (3 / 100 : ℝ) * L ≤ (L / 10 - C - B) / 2 - t * (L / 5 + C) - E := by
  have hfactor : 0 ≤ L / 5 + C := by positivity
  have hprod := mul_le_mul_of_nonneg_right ht hfactor
  nlinarith

/-- Specialization of the proved split mass, with no prime-sum hypothesis. -/
theorem split_prime_mass_of_small_errors (d : ℤ) (D Q Y : ℕ)
    (L C B : ℝ) (hL : 0 < L) (hQ : 0 < Q) (hC : 0 ≤ C)
    (hCsmall : C ≤ L / 10000) (hBsmall : B ≤ L / 10000)
    (hEsmall : (Y : ℝ) + Real.log D / Y ≤ L / 10000)
    (hlog : (12 / 25 : ℝ) * L ≤ Real.log (Q : ℝ))
    (hmass : (1 / ((1 + 10 / L) - 1) - C - B) / 2 -
      (Q : ℝ) ^ (-((1 + 10 / L) - 1) / 2) * (2 / ((1 + 10 / L) - 1) + C) -
      (Y + Real.log D / Y) ≤
      ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
        Real.log p / (p : ℝ)) :
    (3 / 100 : ℝ) * L ≤
      ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
        Real.log p / (p : ℝ) := by
  have hfrac : 1 / ((1 + 10 / L) - 1) = L / 10 := by
    field_simp
    ring
  have hfrac2 : 2 / ((1 + 10 / L) - 1) = L / 5 := by
    field_simp
    ring
  rw [hfrac, hfrac2, add_sub_cancel_left] at hmass
  exact (split_mass_numeric_margin L C B _ _ hL.le hC hCsmall hBsmall hEsmall
    (split_prime_tail_factor_bound Q L hQ hL hlog)).trans hmass

end Ostmann

end OAI
