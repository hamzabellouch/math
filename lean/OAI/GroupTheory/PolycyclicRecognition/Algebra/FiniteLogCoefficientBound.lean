import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteExponentialLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordPowerCoefficientBound
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Field.Basic

namespace OAI

/-! # Coefficient bounds for the finite logarithm of a word polynomial -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem finiteNilpotentLog_sum {A : Type*} [Ring A] [Algebra ℚ A] (p : A) (c : ℕ) :
    finiteNilpotentLog (c + 1) p =
      ∑ k : Fin c, ((-1 : ℚ) ^ (k.val + 2) / (k.val + 1)) • p ^ (k.val + 1) := by
  rw [finiteNilpotentLog, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, PowerSeries.coeff_log, ite_true, map_zero, zero_mul,
    Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
    Algebra.algebraMap_self, RingHom.id_apply, zero_add, ← Algebra.smul_def,
    Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd]

theorem sum_choose_initial_le (a c : ℕ) (ha : a ≤ c) :
    (∑ k ∈ Finset.range c, a.choose k) ≤ 2 ^ c := by
  calc
    _ ≤ ∑ k ∈ Finset.range c, c.choose k :=
      Finset.sum_le_sum (fun k _ => Nat.choose_le_choose k ha)
    _ ≤ ∑ k ∈ Finset.range (c + 1), c.choose k := by
      rw [Finset.sum_range_succ]
      exact Nat.le_add_right _ _
    _ = _ := Nat.sum_range_choose c

theorem finiteLog_coefficient_bound {n : ℕ} (p : RationalWords n) (c : ℕ)
    (hp : p.coeff 1 = 0) (hbound : ∀ w, |p.coeff w| ≤ 1)
    (w : FreeMonoid (Fin n)) (hw : 0 < w.length) (hc : w.length ≤ c + 1) :
    |(finiteNilpotentLog (c + 1) p).coeff w| ≤ (2 : ℚ) ^ c := by
  rw [finiteNilpotentLog_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ k : Fin c, |((-1 : ℚ) ^ (k.val + 2) / (k.val + 1)) *
        (p ^ (k.val + 1)).coeff w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin c, ((w.length - 1).choose k.val : ℚ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      have hs : |(-1 : ℚ) ^ (k.val + 2) / (k.val + 1)| ≤ 1 := by
        simp only [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg (by positivity : (0 : ℚ) ≤ k.val + 1), one_div]
        exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      exact (mul_le_mul hs (word_power_coefficient_bound p hp hbound k.val w hw)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ ≤ (2 : ℚ) ^ c := by
      have h := sum_choose_initial_le (w.length - 1) c (by omega)
      rw [← Fin.sum_univ_eq_sum_range] at h
      exact_mod_cast h

end PolycyclicRecognition

end

end OAI
