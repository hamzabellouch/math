import OAI.NumberTheory.Ostmann.Quadratic.QuadraticAmplificationBias
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeDivisors

namespace OAI

/-! # Passing from an affine value to its squarefree kernel -/

namespace Ostmann

open scoped BigOperators Classical

theorem jacobi_kernel_eq {u x : ℤ} {t p : ℕ} (hp : p.Prime) (hpt : ¬p ∣ t)
    (hx : u * (t : ℤ) ^ 2 = x) : jacobiSym x p = jacobiSym u p := by
  have hc : (t : ℤ).gcd p = 1 := by
    simpa using ((hp.coprime_iff_not_dvd.mpr hpt).symm : t.Coprime p)
  rw [← hx, jacobiSym.mul_left, jacobiSym.sq_one' hc, mul_one]

theorem quadratic_kernel_mean_error (P : Finset ℕ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1)
    (u x : ℤ) (t : ℕ) (hx : u * (t : ℤ) ^ 2 = x) :
    ‖quadraticPrimeMean P e x - quadraticPrimeMean P e u‖ ≤
      2 * ((P.filter fun p => p ∣ t).card : ℝ) / P.card := by
  unfold quadraticPrimeMean
  rw [← sub_div, ← Finset.sum_sub_distrib, norm_div]
  have hsum : ‖∑ p ∈ P, (e p * (jacobiSym x p : ℂ) - e p * (jacobiSym u p : ℂ))‖ ≤
      2 * ((P.filter fun p => p ∣ t).card : ℝ) := by
    calc
      _ ≤ ∑ p ∈ P, ‖e p * (jacobiSym x p : ℂ) - e p * (jacobiSym u p : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ P, if p ∣ t then (2 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        split_ifs with hpt
        · have hxnorm : ‖e p * (jacobiSym x p : ℂ)‖ ≤ 1 := by
            rw [norm_mul]
            exact (mul_le_mul (he p hp) (norm_jacobi_complex_le x p) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
          have hunorm : ‖e p * (jacobiSym u p : ℂ)‖ ≤ 1 := by
            rw [norm_mul]
            exact (mul_le_mul (he p hp) (norm_jacobi_complex_le u p) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
          exact (norm_sub_le _ _).trans (by linarith)
        · rw [jacobi_kernel_eq (hP p hp) hpt hx, sub_self, norm_zero]
      _ = _ := by rw [← Finset.sum_filter]; simp; ring
  have hden : ‖(P.card : ℂ)‖ = (P.card : ℝ) := by simp
  rw [hden]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

theorem prime_divisors_card_log_le (P : Finset ℕ) (t : ℕ) (ht : 0 < t)
    (hP : ∀ p ∈ P, p.Prime) (L : ℝ) (hL : ∀ p ∈ P, L ≤ Real.log (p : ℝ)) :
    ((P.filter fun p => p ∣ t).card : ℝ) * L ≤ Real.log (t : ℝ) := by
  calc
    _ = ∑ _p ∈ P.filter (fun p => p ∣ t), L := by simp
    _ ≤ ∑ p ∈ P.filter (fun p => p ∣ t), Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hL p (Finset.mem_filter.mp hp).1
    _ ≤ _ := sum_log_prime_divisors_le _ ht
      (fun p hp => hP p (Finset.mem_filter.mp hp).1)
      (fun _ hp => (Finset.mem_filter.mp hp).2)

theorem quadratic_kernel_bias_lower (P : Finset ℕ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1)
    (u x : ℤ) (t : ℕ) (hx : u * (t : ℤ) ^ 2 = x)
    (c E : ℝ) (hbias : c + E ≤ ‖quadraticPrimeMean P e x‖)
    (hloss : 2 * ((P.filter fun p => p ∣ t).card : ℝ) / P.card ≤ E) :
    c ≤ ‖quadraticPrimeMean P e u‖ := by
  have herr := (quadratic_kernel_mean_error P e hP he u x t hx).trans hloss
  have ht := norm_add_le (quadraticPrimeMean P e x - quadraticPrimeMean P e u)
    (quadraticPrimeMean P e u)
  rw [sub_add_cancel] at ht
  linarith

end Ostmann

end OAI
