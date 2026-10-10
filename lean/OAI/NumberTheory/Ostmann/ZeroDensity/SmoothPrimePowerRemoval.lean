import Mathlib.NumberTheory.Chebyshev
import OAI.NumberTheory.Ostmann.Construction.SmoothPrimeMeanTest

namespace OAI

/-! # Removing higher prime powers from the fixed smooth mean -/
namespace Ostmann
open scoped Classical BigOperators

 theorem primeMeanTest_nat_support (X : ℝ) (hX : 0 < X) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) : primeMeanTest (n / X) = 0 := by
  apply primeMeanTest_zero_outside
  intro h
  apply hn
  rw [Finset.mem_Ioc]
  constructor
  · by_contra hz
    have : n = 0 := by omega
    subst n
    norm_num at h
  · apply (Nat.le_floor_iff hX.le).mpr
    have hh := (div_le_iff₀ hX).mp h.2
    linarith

 theorem smoothMangoldtMean_eq_sum (q : ℕ) (χ : DirichletCharacter ℂ q)
    (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean q χ X = ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * primeMeanTest (n / X) := by
  apply tsum_eq_sum
  intro n hn
  rw [primeMeanTest_nat_support X hX n hn, Complex.ofReal_zero, mul_zero]

 theorem nonprime_mangoldt_sum (X : ℝ) :
    (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
      ArithmeticFunction.vonMangoldt n) = Chebyshev.psi X - Chebyshev.theta X := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊X⌋₊)
    Nat.Prime (fun n => ArithmeticFunction.vonMangoldt n)
  have hp : (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      ArithmeticFunction.vonMangoldt n) = Chebyshev.theta X := by
    apply Finset.sum_congr rfl
    intro n hn
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
  rw [hp] at h
  change Chebyshev.theta X + _ = Chebyshev.psi X at h
  linarith

noncomputable def smoothPrimeSum (g : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
    (Real.log n : ℂ) * g n * primeMeanTest (n / X)

 theorem smooth_mangoldt_prime_error (g : ℕ → ℂ) (X B : ℝ)
    (hX : 1 ≤ X) (hB : 0 ≤ B)
    (hg : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊, ‖g n‖ ≤ B) :
    ‖(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X)) -
      smoothPrimeSum g X‖ ≤ B * (2 * Real.sqrt X * Real.log X) := by
  have he : (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X)) -
      smoothPrimeSum g X =
      ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X) := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊X⌋₊) Nat.Prime
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X))
    have hp : (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
        (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X)) =
        smoothPrimeSum g X := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
    rw [hp] at h
    exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)).symm
  rw [he]
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        B * ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        abs_of_nonneg (primeMeanTest_nonneg _)]
      calc
        _ ≤ ArithmeticFunction.vonMangoldt n * B * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hg n (Finset.mem_filter.mp hn).1)
            ArithmeticFunction.vonMangoldt_nonneg) (primeMeanTest_le_one _)
            (primeMeanTest_nonneg _) (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hB)
        _ = _ := by ring
    _ = B * (Chebyshev.psi X - Chebyshev.theta X) := by
      rw [← Finset.mul_sum, nonprime_mangoldt_sum]
    _ ≤ B * (2 * Real.sqrt X * Real.log X) :=
      mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hX)) hB

end Ostmann

end OAI
