import OAI.NumberTheory.TwoPoint.Bounds.SieveGoldbachLocal
import OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem

namespace OAI

/-! The required logarithmic Euler-product lower bound and singular factor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def sieveEulerFactor (p : ℕ) : ℝ := (1 - 1 / (p : ℝ))⁻¹

noncomputable def sieveSingularFactor (N : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors, sieveEulerFactor p

lemma sieve_euler_base_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [sub_pos, div_lt_one (by positivity)]
  exact hpR

lemma sieve_euler_factor_pos {p : ℕ} (hp : p.Prime) : 0 < sieveEulerFactor p :=
  inv_pos.mpr (sieve_euler_base_pos hp)

lemma sieve_euler_factor_one_le {p : ℕ} (hp : p.Prime) : 1 ≤ sieveEulerFactor p := by
  unfold sieveEulerFactor
  apply (one_le_inv₀ (sieve_euler_base_pos hp)).mpr
  have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  linarith

lemma sieve_euler_factor_exp {p : ℕ} (hp : p.Prime) :
    Real.exp (1 / (p : ℝ)) ≤ sieveEulerFactor p := by
  apply (Real.le_log_iff_exp_le (sieve_euler_factor_pos hp)).mp
  rw [sieveEulerFactor, Real.log_inv]
  linarith [Real.log_le_sub_one_of_pos (sieve_euler_base_pos hp)]

lemma sieve_euler_product_exp (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.exp (∑ p ∈ P, 1 / (p : ℝ)) ≤ ∏ p ∈ P, sieveEulerFactor p := by
  rw [Real.exp_sum]
  exact prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
    (fun p hp => sieve_euler_factor_exp (hP p hp))

lemma sieve_euler_product_log_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y →
      c * Real.log y ≤ ∏ p ∈ sievePrimesUpTo y, sieveEulerFactor p := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  refine ⟨Real.exp (-C), Real.exp_pos _, ?_⟩
  intro y hy
  have hy1 : 1 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy1
  have hsum : Real.log (Real.log y) - C ≤ ∑ p ∈ sievePrimesUpTo y, 1 / (p : ℝ) := by
    linarith [(abs_le.mp (hC y hy)).1]
  calc
    Real.exp (-C) * Real.log y = Real.exp (Real.log (Real.log y) - C) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hlog]
      ring
    _ ≤ Real.exp (∑ p ∈ sievePrimesUpTo y, 1 / (p : ℝ)) := Real.exp_le_exp.mpr hsum
    _ ≤ _ := sieve_euler_product_exp _ (sievePrimesUpTo_prime y)

lemma sieve_singular_factor_pos (N : ℕ) : 0 < sieveSingularFactor N := by
  apply prod_pos
  intro p hp
  exact sieve_euler_factor_pos (Nat.mem_primeFactors.mp hp).1

lemma sieve_singular_factor_one_le (N : ℕ) : 1 ≤ sieveSingularFactor N := by
  apply one_le_prod₀
  intro p hp
  exact sieve_euler_factor_one_le (Nat.mem_primeFactors.mp hp).1

lemma sieve_singular_correction_le {N : ℕ} (hN : N ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (sieveSingularFactor N)⁻¹ ≤ ∏ p ∈ P, (if p ∣ N then 1 - 1 / (p : ℝ) else 1) := by
  have hsub : P.filter (fun p => p ∣ N) ⊆ N.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hP p (mem_filter.mp hp).1, (mem_filter.mp hp).2, hN⟩
  have he := prod_le_prod_of_subset_of_le_one₀ (f := fun p : ℕ => 1 - 1 / (p : ℝ)) hsub
    (fun p hp => (sieve_euler_base_pos (Nat.mem_primeFactors.mp hp).1).le)
    (fun p _ _ => by
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith)
  simpa only [sieveSingularFactor, sieveEulerFactor, ← prod_inv_distrib, inv_inv, prod_filter] using he

lemma sieve_goldbach_product_lower {N : ℕ} (hN : 2 ∣ N) (hN0 : N ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, sieveEulerFactor p) ^ 2 / sieveSingularFactor N ≤
      ∏ p ∈ P, (1 + sieveGoldbachWeight N p) := by
  have hnonneg : 0 ≤ (∏ p ∈ P, sieveEulerFactor p) ^ 2 := sq_nonneg _
  calc
    _ ≤ (∏ p ∈ P, sieveEulerFactor p) ^ 2 *
        (∏ p ∈ P, (if p ∣ N then 1 - 1 / (p : ℝ) else 1)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (sieve_singular_correction_le hN0 P hP) hnonneg
    _ = ∏ p ∈ P, (sieveEulerFactor p ^ 2 * (if p ∣ N then 1 - 1 / (p : ℝ) else 1)) := by
      rw [prod_mul_distrib, prod_pow]
    _ ≤ _ := by
      apply prod_le_prod₀
      · intro p hp
        apply mul_nonneg (sq_nonneg _)
        split_ifs
        · exact (sieve_euler_base_pos (hP p hp)).le
        · norm_num
      · exact fun p hp => sieve_goldbach_factor_ge hN (hP p hp)

end TwoPointCorrelations

end OAI
