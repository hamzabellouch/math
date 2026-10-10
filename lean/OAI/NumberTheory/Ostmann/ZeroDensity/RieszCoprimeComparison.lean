import OAI.NumberTheory.Ostmann.ZeroDensity.RieszPrimeRemoval

namespace OAI

/-! # The Riesz cost of changing coefficients only at primes dividing the modulus -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem rieszPrimeMean_norm_le_of_coprime_zero (g : ℕ → ℂ) (q : ℕ) (X B : ℝ)
    (hq : 0 < q) (hX : 1 ≤ X) (hB : 0 ≤ B)
    (hg : ∀ n, ‖g n‖ ≤ B) (hz : ∀ n, n.Coprime q → g n = 0) :
    ‖rieszPrimeMean g X‖ ≤ B * q * Real.log X := by
  classical
  let S := (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime
  let D := S.filter (fun n => ¬n.Coprime q)
  have hsub : D ⊆ Finset.Ioc 0 q := by
    intro n hn
    obtain ⟨hnS, hnq⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, hnp⟩ := Finset.mem_filter.mp hnS
    have hd : n ∣ q := by
      by_contra hd
      exact hnq (hnp.coprime_iff_not_dvd.mpr hd)
    exact Finset.mem_Ioc.mpr ⟨hnp.pos, Nat.le_of_dvd hq hd⟩
  have hcard : D.card ≤ q := by
    simpa using Finset.card_le_card hsub
  have heq : rieszPrimeMean g X = ∑ n ∈ D,
      (Real.log n : ℂ) * g n * rieszPrimeTest (n / X) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnd
    have hnq : n.Coprime q := by
      by_contra hh
      exact hnd (Finset.mem_filter.mpr ⟨hn, hh⟩)
    rw [hz n hnq, mul_zero, zero_mul]
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hb (n : ℕ) (hn : n ∈ D) :
      ‖(Real.log n : ℂ) * g n * rieszPrimeTest (n / X)‖ ≤ B * Real.log X := by
    obtain ⟨hnS, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, _⟩ := Finset.mem_filter.mp hnS
    obtain ⟨hn0, hnX⟩ := Finset.mem_Ioc.mp hnI
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnX' : (n : ℝ) ≤ X := (Nat.le_floor_iff (by linarith : 0 ≤ X)).mp hnX
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn0)
    have hlogle : Real.log n ≤ Real.log X := Real.log_le_log hnR hnX'
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogn]
    calc
      _ ≤ (Real.log n * B) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (hg n) hlogn)
        (rieszPrimeTest_norm_le_one (n / X) (by positivity)) (norm_nonneg _) (by positivity)
      _ ≤ B * Real.log X := by nlinarith
  rw [heq]
  calc
    _ ≤ ∑ n ∈ D, ‖(Real.log n : ℂ) * g n * rieszPrimeTest (n / X)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ D, B * Real.log X := Finset.sum_le_sum hb
    _ = (D.card : ℝ) * (B * Real.log X) := by simp
    _ ≤ B * q * Real.log X := by
      have hc : (D.card : ℝ) ≤ q := by exact_mod_cast hcard
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hB hlog)
      convert hh using 1
      ring

theorem rieszTwistMean_norm_le_of_coprime_zero (g : ℕ → ℂ) (q : ℕ) (X B : ℝ)
    (hq : 0 < q) (hX : 1 ≤ X) (hB : 0 ≤ B)
    (hg : ∀ n, ‖g n‖ ≤ B) (hz : ∀ n, n.Coprime q → g n = 0) :
    ‖rieszTwistMean g X‖ ≤ B * q * Real.log X + B * (2 * Real.sqrt X * Real.log X) := by
  have hp := rieszPrimeMean_norm_le_of_coprime_zero g q X B hq hX hB hg hz
  have he := rieszTwistMean_prime_error g X B hX hB hg
  have ht := norm_le_norm_sub_add (rieszTwistMean g X) (rieszPrimeMean g X)
  linarith

theorem rieszTwistMean_coprime_comparison (g h : ℕ → ℂ) (q : ℕ) (X : ℝ)
    (hq : 0 < q) (hX : 1 ≤ X) (hg : ∀ n, ‖g n‖ ≤ 1) (hh : ∀ n, ‖h n‖ ≤ 1)
    (he : ∀ n, n.Coprime q → g n = h n) :
    ‖rieszTwistMean g X - rieszTwistMean h X‖ ≤
      2 * q * Real.log X + 4 * Real.sqrt X * Real.log X := by
  rw [rieszTwistMean_sub]
  have hb (n : ℕ) : ‖g n - h n‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hg n, hh n])
  have hz (n : ℕ) (hn : n.Coprime q) : g n - h n = 0 := by rw [he n hn, sub_self]
  have ht := rieszTwistMean_norm_le_of_coprime_zero (fun n => g n - h n) q X 2
    hq hX (by norm_num) hb hz
  convert ht using 1
  ring

end Ostmann

end OAI
