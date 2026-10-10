import Mathlib

namespace OAI

/-! # The logarithmic prime decomposition for squarefree-supported coefficients

This is the coefficient identity used to start the Montgomery--Vaughan
bilinear reduction. The error is supported on prime-square divisibility.
-/
namespace JointDickman
open Finset

lemma squarefree_log_eq_sum_primeFactors {n : ℕ} (hn : Squarefree n) :
    Real.log n = ∑ p ∈ n.primeFactors, Real.log p := by
  have he : (∏ p ∈ n.primeFactors, (p:ℝ)) = (n:ℝ) := by
    rw [←Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  rw [←he,Real.log_prod]
  intro p hp
  exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero

lemma multiplicative_squarefree_log_identity (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    f n*Real.log n = ∑ p ∈ n.primeFactors, (f p*f (n/p))*Real.log p := by
  rw [squarefree_log_eq_sum_primeFactors hn,mul_sum]
  apply sum_congr rfl
  intro p hp
  have hd := (Nat.mem_primeFactors.mp hp).2.1
  have hc : p.Coprime (n/p) := Nat.coprime_of_squarefree_mul
    (by simpa only [Nat.mul_div_cancel' hd] using hn)
  rw [←hf.map_mul_of_coprime hc,Nat.mul_div_cancel' hd]

/-- Prime powers cause the only error when the logarithmic identity is used
without restricting the outer sum to squarefree integers. -/
lemma squarefree_supported_log_error (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1)
    (hsupport : ∀ n, ¬Squarefree n → f n = 0) (n : ℕ) :
    |f n*Real.log n - ∑ p ∈ n.primeFactors, (f p*f (n/p))*Real.log p| ≤
      ∑ p ∈ n.primeFactors, if p^2 ∣ n then Real.log p else 0 := by
  by_cases hn : Squarefree n
  · rw [multiplicative_squarefree_log_identity f hf hn,sub_self,abs_zero]
    exact sum_nonneg (fun p hp => by
      split_ifs
      · exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt.le)
      · exact le_rfl)
  · rw [hsupport n hn,zero_mul,zero_sub,abs_neg]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro p hp
    obtain ⟨hpprime,hpn,_⟩ := Nat.mem_primeFactors.mp hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
    by_cases hpp : p^2 ∣ n
    · rw [ite_eq_left hpp,abs_mul,abs_of_nonneg hlog,abs_mul]
      have hb' : |f p| * |f (n/p)| ≤ 1 := by
        simpa only [one_mul] using mul_le_mul (hb p) (hb (n/p)) (abs_nonneg _) zero_le_one
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb' hlog
    · have hcof : ¬Squarefree (n/p) := by
        intro hh
        have hnot : ¬p ∣ n/p := by
          intro hd
          apply hpp
          simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hpn).mp hd
        have hc : p.Coprime (n/p) := hpprime.coprime_iff_not_dvd.mpr hnot
        have hsf := (Nat.squarefree_mul hc).mpr ⟨hpprime.squarefree,hh⟩
        exact hn (by simpa only [Nat.mul_div_cancel' hpn] using hsf)
      simp [hpp,hsupport (n/p) hcof]

end JointDickman

end OAI
