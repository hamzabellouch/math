import OAI.NumberTheory.JointDickman.Arithmetic.PrimeLogarithmicReduction
import OAI.NumberTheory.JointDickman.Probability.CyclicKernelSum

namespace OAI

/-! # The linear prime-square error in the logarithmic reduction -/
namespace JointDickman
open Finset

lemma summable_log_div_square :
    Summable (fun n : ℕ => Real.log n/(n:ℝ)^2) := by
  have hs : Summable (fun n : ℕ => 2*(n:ℝ)^(-3/2:ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-3/2:ℝ) < -1)).mul_left 2
  apply hs.of_nonneg_of_le (fun n => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _))
  intro n
  by_cases hn : n=0
  · simp [hn]
  have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hl := Real.log_natCast_le_rpow_div n (by norm_num : (0:ℝ) < 1/2)
  calc
    _ ≤ ((n:ℝ)^(1/2:ℝ)/(1/2:ℝ))/(n:ℝ)^2 := div_le_div_of_nonneg_right hl (sq_nonneg _)
    _ = _ := by
      have hp : (n:ℝ)^(-3/2:ℝ) = (n:ℝ)^(1/2:ℝ)/(n:ℝ)^2 := by
        rw [show (n:ℝ)^2 = (n:ℝ)^(2:ℝ) by rw [Real.rpow_two],←Real.rpow_sub hnR]
        norm_num
      rw [hp]
      ring

lemma primeSquareLogError_eq (N : ℕ) :
    primeSquareLogError N = ∑ p ∈ Nat.primesLE N, Real.log p * ((N/p^2:ℕ):ℝ) := by
  classical
  have hi : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc,mem_Icc]
    omega
  have he (n : ℕ) (hn : n ∈ Ioc 0 N) :
      (∑ p ∈ n.primeFactors, if p^2 ∣ n then Real.log p else 0) =
      ∑ p ∈ Nat.primesLE N, if p^2 ∣ n then Real.log p else 0 := by
    have hsub : n.primeFactors ⊆ Nat.primesLE N := by
      intro p hp
      obtain ⟨hprime,hpn,hn0⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (mem_Ioc.mp hn).1 hpn).trans (mem_Ioc.mp hn).2,hprime⟩
    apply sum_subset hsub
    intro p hp hnot
    have hpd : ¬p^2 ∣ n := by
      intro hpp
      apply hnot
      exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesLE.mp hp).2,
        (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hpp,(mem_Ioc.mp hn).1.ne'⟩
    simp [hpd]
  unfold primeSquareLogError
  rw [sum_congr rfl he,sum_comm]
  apply sum_congr rfl
  intro p hp
  calc
    _ = Real.log p * (∑ n ∈ Icc 1 N, if p^2 ∣ n then (1:ℝ) else 0) := by
      rw [hi,mul_sum]
      apply sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = _ := by rw [sum_positive_multiples]

theorem primeSquareLogError_linear_bound : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, primeSquareLogError N ≤ C*N := by
  let S := ∑' n : ℕ, Real.log n/(n:ℝ)^2
  have hS : 0 ≤ S := tsum_nonneg (fun n => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _))
  refine ⟨1+S,by positivity,fun N => ?_⟩
  rw [primeSquareLogError_eq]
  have hpoint (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      Real.log p * ((N/p^2:ℕ):ℝ) ≤ (N:ℝ)*(Real.log p/(p:ℝ)^2) := by
    have hp0 := (Nat.mem_primesLE.mp hp).2.pos
    have hpsq : (0:ℝ) < (p:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hp0)
    have hfloor : ((N/p^2:ℕ):ℝ) ≤ (N:ℝ)/(p:ℝ)^2 := by
      apply (le_div_iff₀ hpsq).mpr
      exact_mod_cast Nat.div_mul_le_self N (p^2)
    convert mul_le_mul_of_nonneg_left hfloor (Real.log_natCast_nonneg p) using 1
    ring
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, (N:ℝ)*(Real.log p/(p:ℝ)^2) := sum_le_sum hpoint
    _ = (N:ℝ)*(∑ p ∈ Nat.primesLE N, Real.log p/(p:ℝ)^2) := (mul_sum _ _ _).symm
    _ ≤ (N:ℝ)*S := mul_le_mul_of_nonneg_left
      (summable_log_div_square.sum_le_tsum _ (fun n _ => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _)))
      (Nat.cast_nonneg N)
    _ ≤ _ := by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]

/-- The logarithmic prime-bilinear reduction with its O(N) error discharged. -/
theorem squarefree_sum_prime_bilinear_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n = 0) → ∀ N : ℕ, 0 < N → ∀ θ : ℝ,
    Real.log N * ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤
      C*N + ‖primeLogBilinear f N θ‖ := by
  obtain ⟨C,hC,hbound⟩ := primeSquareLogError_linear_bound
  refine ⟨1+C,by positivity,?_⟩
  intro f hf hb hs N hN θ
  have h := squarefree_sum_prime_bilinear_reduction f hf hb hs N hN θ
  have he := hbound N
  linarith

end JointDickman

end OAI
