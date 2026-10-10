import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityHarmonicDivisors

namespace OAI

/-! # The actual truncated Möbius coefficients in the zero detector -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def densityMobiusCutoff (X n : ℕ) : ℂ :=
  if n ≤ X then (ArithmeticFunction.moebius n : ℂ) else 0

noncomputable def densityDetectorCoefficient (X n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, densityMobiusCutoff X d

 theorem densityMobiusCutoff_norm (X n : ℕ) : ‖densityMobiusCutoff X n‖ ≤ 1 := by
  unfold densityMobiusCutoff
  split_ifs
  · norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  · simp

 theorem densityDetectorCoefficient_norm (X n : ℕ) :
    ‖densityDetectorCoefficient X n‖ ≤ n.divisors.card := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ n.divisors, (1 : ℝ) :=
      Finset.sum_le_sum (fun d _ => densityMobiusCutoff_norm X d)
    _ = _ := by simp

 theorem densityDetectorCoefficient_initial (X n : ℕ) (hn : n ≤ X) :
    densityDetectorCoefficient X n = if n = 1 then 1 else 0 := by
  have he : densityDetectorCoefficient X n = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℂ) := by
    apply Finset.sum_congr rfl
    intro d hd
    unfold densityMobiusCutoff
    exact ite_eq_left ((Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)).trans hn)
  rw [he]
  have hm := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ))
  rw [ArithmeticFunction.coe_zeta_mul_apply] at hm
  simpa only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using hm

 theorem densityDetectorCoefficient_one {X : ℕ} (hX : 1 ≤ X) :
    densityDetectorCoefficient X 1 = 1 := by
  rw [densityDetectorCoefficient_initial X 1 hX, ite_eq_left rfl]

 theorem densityDetectorCoefficient_small {X n : ℕ} (hn : 2 ≤ n) (hX : n ≤ X) :
    densityDetectorCoefficient X n = 0 := by
  rw [densityDetectorCoefficient_initial X n hX, ite_eq_right (by omega)]

 theorem densityDetectorCoefficient_energy (X N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ‖densityDetectorCoefficient X n‖ ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  apply (Finset.sum_le_sum (fun n _ =>
    pow_le_pow_left₀ (norm_nonneg _) (densityDetectorCoefficient_norm X n) 2)).trans
  exact density_divisor_square_sum N

 theorem densityDetectorCoefficient_harmonic_energy (X N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ‖densityDetectorCoefficient X n‖ ^ 2 / n) ≤
      (1 + Real.log N) ^ 4 := by
  apply (Finset.sum_le_sum (fun n _ =>
    div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (densityDetectorCoefficient_norm X n) 2)
      (Nat.cast_nonneg n))).trans
  exact density_divisor_square_harmonic N

end Ostmann

end OAI
