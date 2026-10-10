import OAI.NumberTheory.JointDickman.Arithmetic.FinitePrimeWeight

namespace OAI

/-! # Removing a fixed divisor from finite-prime weights and intervals -/
namespace JointDickman
open Finset Classical

theorem finitePrimeWeight_mul_fixed {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (t : ℕ → ℝ) {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    finitePrimeWeight P t (d*n) = finitePrimeWeight P t d*
      finitePrimeWeight P (fun p => if p ∣ d then 1 else t p) n := by
  by_cases hn : n = 0
  · subst n
    simp
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hd,hn,mul_ne_zero hd hn,ite_false,
    ← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  simp only [(hP p hp).dvd_mul]
  by_cases hpd : p ∣ d <;> by_cases hpn : p ∣ n <;> simp [hpd,hpn]

theorem fixedDivisorWeight_bounds {P : Finset ℕ} {t : ℕ → ℝ}
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1) (d : ℕ) :
    ∀ p ∈ P, 0 ≤ (if p ∣ d then 1 else t p) ∧ (if p ∣ d then 1 else t p) ≤ (1 : ℝ) := by
  intro p hp
  by_cases hd : p ∣ d
  · simp [hd]
  · simpa only [ite_eq_right hd] using ht p hp

theorem sum_divisible_interval {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (a b d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Ioc a b, if d ∣ n then f n else 0) =
      ∑ k ∈ Ioc (a/d) (b/d), f (d*k) := by
  rw [← sum_filter]
  have hsets : (Ioc (a/d) (b/d)).image (fun k => d*k) = (Ioc a b).filter (fun n => d ∣ n) := by
    ext n
    simp only [mem_image,mem_Ioc,mem_filter]
    constructor
    · rintro ⟨k,⟨hk,hkb⟩,rfl⟩
      constructor
      · constructor
        · have h := (Nat.div_lt_iff_lt_mul hd).mp hk
          simpa only [Nat.mul_comm] using h
        · exact (Nat.mul_le_mul_left d hkb).trans (Nat.mul_div_le b d)
      · exact dvd_mul_right d k
    · rintro ⟨⟨han,hnb⟩,hdn⟩
      refine ⟨n/d,⟨?_,Nat.div_le_div_right hnb⟩,Nat.mul_div_cancel' hdn⟩
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      simpa only [Nat.mul_comm,Nat.mul_div_cancel' hdn] using han
  rw [← hsets,sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hd hab

end JointDickman

end OAI
