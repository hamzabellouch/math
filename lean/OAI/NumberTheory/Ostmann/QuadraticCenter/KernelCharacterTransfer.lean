import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCharacterTransferBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem prime_divisor_count_le_of_lt_power {P : Finset ℕ}
    (hP : ∀ p ∈ P,Nat.Prime p) {Z r n : ℕ}
    (hZ : 1 ≤ Z) (hlarge : ∀ p ∈ P,Z ≤ p) (hn : 0 < n)
    (hbound : n < Z^(r+1)) : (P.filter (fun p => p ∣ n)).card ≤ r := by
  classical
  let S := P.filter (fun p => p ∣ n)
  have hd : (∏ p ∈ S,p) ∣ n := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hP p (Finset.mem_filter.mp hp).1)
          (hP q (Finset.mem_filter.mp hq).1)).mpr hpq)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  have hprod : Z^S.card ≤ ∏ p ∈ S,p := by
    rw [←Finset.prod_const]
    exact Finset.prod_le_prod (fun p hp => hlarge p (Finset.mem_filter.mp hp).1)
  have hpow : Z^S.card < Z^(r+1) := (hprod.trans (Nat.le_of_dvd hn hd)).trans_lt hbound
  by_contra hh
  have hc : r+1 ≤ S.card := by change ¬S.card≤r at hh; omega
  exact (not_le_of_gt hpow) (Nat.pow_le_pow_right hZ hc)

theorem kernelFactorization_squareFactor_le {z : ℤ} (F : KernelFactorization z) :
    F.squareFactor ≤ z.natAbs := by
  rw [F.abs_factorization]
  have hu : 1 ≤ F.kernel.natAbs := Int.natAbs_pos.mpr F.kernel_ne_zero
  have ht := F.squareFactor_pos
  nlinarith

theorem signedJacobiAverage_kernel_error {P : Finset ℕ}
    (hP : ∀ p ∈ P,Nat.Prime p) (ε : ℕ → ℤ)
    (hε : ∀ p ∈ P,ε p = -1 ∨ ε p = 1) {z : ℤ} (F : KernelFactorization z) :
    |signedJacobiAverage P ε z-signedJacobiAverage P ε F.kernel| ≤
      2*((P.filter (fun p => p ∣ F.squareFactor)).card:ℝ)/P.card := by
  classical
  rw [signedJacobiAverage,signedJacobiAverage,←sub_div,abs_div,
    (show |(P.card:ℝ)|=(P.card:ℝ) from abs_of_nonneg (Nat.cast_nonneg P.card))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg P.card)
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ P,|((ε p*jacobiSym z p:ℤ):ℝ)-((ε p*jacobiSym F.kernel p:ℤ):ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P,if p ∣ F.squareFactor then (2:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpt : p ∣ F.squareFactor
      · rw [ite_eq_left hpt]
        have hb (u : ℤ) : |((ε p*jacobiSym u p:ℤ):ℝ)| ≤ 1 := by
          rcases oriented_jacobi_trichotomy (ε p) u p (hε p hp) with h|h|h <;>
            simp only [h] <;> norm_num
        exact (abs_sub _ _).trans (by linarith [hb z,hb F.kernel])
      · rw [ite_eq_right hpt,kernelFactorization_jacobi_eq F (hP p hp) hpt]
        simp
    _ = _ := by rw [←Finset.sum_filter]; simp [mul_comm]

theorem signedJacobiAverage_kernel_lower {P : Finset ℕ}
    (hP : ∀ p ∈ P,Nat.Prime p) (ε : ℕ → ℤ)
    (hε : ∀ p ∈ P,ε p = -1 ∨ ε p = 1) {z : ℤ} (F : KernelFactorization z)
    {Z r : ℕ} (hZ : 1 ≤ Z) (hlarge : ∀ p ∈ P,Z ≤ p)
    (hbound : z.natAbs < Z^(r+1)) {c : ℝ}
    (hbias : c ≤ |signedJacobiAverage P ε z|)
    (hcost : 2*(r:ℝ)/P.card ≤ c/2) :
    c/2 ≤ |signedJacobiAverage P ε F.kernel| := by
  have hcount := prime_divisor_count_le_of_lt_power hP hZ hlarge F.squareFactor_pos
    ((kernelFactorization_squareFactor_le F).trans_lt hbound)
  have herr := signedJacobiAverage_kernel_error hP ε hε F
  have herr' : |signedJacobiAverage P ε z-signedJacobiAverage P ε F.kernel| ≤ c/2 := by
    apply herr.trans
    apply le_trans _ hcost
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg P.card)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) (by norm_num)
  have htri := abs_sub_le (signedJacobiAverage P ε z) (signedJacobiAverage P ε F.kernel) 0
  simp only [sub_zero] at htri
  linarith

end Ostmann.QuadraticCenter

end

end OAI
