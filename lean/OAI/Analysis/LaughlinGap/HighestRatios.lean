import Mathlib
import OAI.Analysis.LaughlinGap.SpinWork

namespace OAI

/-! Highest Ratios. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma highest_numerator_product {m z : ℕ} (hz : z ≤ m) (p : ℕ) :
    (∏ k ∈ Finset.range p, ((m : ℝ)-z+k+1)) =
      ((m-z+p).descFactorial p : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.prod_range_succ, ih]
    rw [show m-z+(p+1) = (m-z+p)+1 by omega, Nat.succ_descFactorial_succ]
    push_cast
    rw [Nat.cast_sub hz]
    ring

lemma highest_denominator_product {n p : ℕ} (hp : p ≤ n) :
    (∏ k ∈ Finset.range p, ((n : ℝ)-k)) = (n.descFactorial p : ℝ) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Nat.cast_sub ((Finset.mem_range.mp hk).le.trans hp)]

theorem highestWeight_factorial {n m z p : ℕ} (hz : z ≤ min n m) (hp : p ≤ z) :
    highestWeight n m z p = (z.choose p : ℝ) *
      ((m-z+p).descFactorial p : ℝ) / (n.descFactorial p : ℝ) := by
  simp only [highestWeight, highestFactor, Finset.prod_div_distrib,
    highest_numerator_product (le_min_iff.mp hz).2 p,
    highest_denominator_product (hp.trans (le_min_iff.mp hz).1), mul_div_assoc]

lemma highestCoefficient_zero_ne {n m z : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z 0 ≠ 0 := by
  simp only [highestCoefficient, highestWeight_zero, Real.sqrt_one, mul_one, Nat.sub_zero]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Real.sqrt_pos.mpr (highestNormalization_pos hz)).ne'

theorem highestCoefficient_ratio {n m z p : ℕ} (_hz : z ≤ min n m) (hp : p ≤ z) :
    highestCoefficient n m z p = highestCoefficient n m z 0 *
      ((-1 : ℝ)^p * Real.sqrt (highestWeight n m z p)) := by
  have he : (-1 : ℝ)^(z-p) = (-1 : ℝ)^z * (-1 : ℝ)^p := by
    have hzz : z=(z-p)+p := by omega
    conv_rhs => rw [hzz, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [highestCoefficient, highestWeight_zero, Real.sqrt_one, mul_one, Nat.sub_zero]
  rw [he]
  ring

lemma highestCoefficient_last {n m z : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z z = highestCoefficient n m z 0 *
      ((-1 : ℝ)^z * Real.sqrt ((m.descFactorial z : ℝ)/(n.descFactorial z : ℝ))) := by
  rw [highestCoefficient_ratio hz (le_refl z), highestWeight_factorial hz (le_refl z),
    Nat.sub_add_cancel (le_min_iff.mp hz).2, Nat.choose_self, Nat.cast_one, one_mul]

lemma highestCoefficient_penultimate {n m z : ℕ} (hz : z ≤ min n m) (hpos : 0<z) :
    highestCoefficient n m z (z-1) = highestCoefficient n m z 0 *
      ((-1 : ℝ)^(z-1) * Real.sqrt ((z : ℝ)*((m-1).descFactorial (z-1) : ℝ) /
        (n.descFactorial (z-1) : ℝ))) := by
  rw [highestCoefficient_ratio hz (by omega), highestWeight_factorial hz (by omega)]
  rw [show m-z+(z-1) = m-1 by omega,
    show z.choose (z-1) = z by simpa using Nat.choose_symm (by omega : 1 ≤ z)]

end LaughlinGap.Spin

end

end OAI
