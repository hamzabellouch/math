import OAI.NumberTheory.JointDickman.Arithmetic.SmoothInclusionExclusion
import OAI.NumberTheory.JointDickman.Counting.BinShortAverages

namespace OAI

/-! # Exact divisor expansion for weights supported on finitely many primes -/
namespace JointDickman
open Finset Classical

noncomputable def finitePrimeWeight (P : Finset ℕ) (t : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else ∏ p ∈ P, if p ∣ n then t p else 1, by simp⟩

theorem finitePrimeWeight_multiplicative {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ) :
    (finitePrimeWeight P t).IsMultiplicative := by
  refine ⟨?_,?_⟩
  · simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,one_ne_zero,ite_false]
    exact prod_eq_one (fun p hp => by simp [(hP p hp).not_dvd_one])
  · intro m n hcop
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hm,hn,mul_ne_zero hm hn,ite_false,
      ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hnot : ¬(p ∣ m ∧ p ∣ n) := by
      rintro ⟨hpm,hpn⟩
      exact (hP p hp).ne_one (Nat.eq_one_of_dvd_coprimes hcop hpm hpn)
    simp only [(hP p hp).dvd_mul]
    by_cases hpm : p ∣ m <;> by_cases hpn : p ∣ n <;> simp_all

theorem finitePrimeWeight_bounds {P : Finset ℕ} {t : ℕ → ℝ}
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1) (n : ℕ) :
    0 ≤ finitePrimeWeight P t n ∧ finitePrimeWeight P t n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hn,ite_false]
  exact ⟨prod_nonneg (fun p hp => by split_ifs; exact (ht p hp).1; norm_num),
    prod_le_one₀ (fun p hp => by split_ifs; exact (ht p hp).1; norm_num)
      (fun p hp => by split_ifs; exact (ht p hp).2; exact le_rfl)⟩

theorem finitePrimeWeight_expansion {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (t : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    finitePrimeWeight P t n = ∑ S ∈ P.powerset,
      (∏ p ∈ S, (t p-1))*(if (∏ p ∈ S,p) ∣ n then 1 else 0) := by
  have he (p : ℕ) : (if p ∣ n then t p else (1 : ℝ)) =
      (t p-1)*(if p ∣ n then 1 else 0)+1 := by split_ifs <;> ring
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hn,ite_false,he]
  rw [prod_add]
  apply sum_congr rfl
  intro S hS
  simp only [prod_const_one,mul_one,prod_mul_distrib]
  congr 1
  by_cases hd : (∏ p ∈ S,p) ∣ n
  · rw [ite_eq_left hd]
    exact prod_eq_one (fun p hp => by
      rw [ite_eq_left ((primeProduct_dvd_iff S
        (fun p hp => hP p (mem_powerset.mp hS hp)) n).mp hd p hp)])
  · rw [ite_eq_right hd]
    have hh : ¬∀ p ∈ S, p ∣ n := by
      intro hall
      exact hd ((primeProduct_dvd_iff S (fun p hp => hP p (mem_powerset.mp hS hp)) n).mpr hall)
    push Not at hh
    obtain ⟨p,hp,hpn⟩ := hh
    exact prod_eq_zero hp (by simp [hpn])

theorem sum_divisible_Ioc {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Ioc 0 N, if d ∣ n then f n else 0) =
      ∑ k ∈ Ioc 0 (N/d), f (d*k) := by
  rw [← sum_filter]
  have hsets : (Ioc 0 (N/d)).image (fun k => d*k) = (Ioc 0 N).filter (fun n => d ∣ n) := by
    ext n
    simp only [mem_image,mem_Ioc,mem_filter]
    constructor
    · rintro ⟨k,⟨hk,hkN⟩,rfl⟩
      exact ⟨⟨Nat.mul_pos hd hk,(Nat.mul_le_mul_left d hkN).trans (Nat.mul_div_le N d)⟩,
        dvd_mul_right d k⟩
    · rintro ⟨⟨hn,hnN⟩,hdn⟩
      refine ⟨n/d,⟨Nat.div_pos (Nat.le_of_dvd hn hdn) hd,Nat.div_le_div_right hnN⟩,
        Nat.mul_div_cancel' hdn⟩
  rw [← hsets,sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hd hab

end JointDickman

end OAI
