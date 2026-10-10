import OAI.NumberTheory.JointDickman.Arithmetic.PrimePresenceBound
import OAI.NumberTheory.JointDickman.Arithmetic.RepeatedPrimeDensity

namespace OAI

/-! # Passing from ordinary multiplicative weights to prime presence -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma primePresence_norm_le_one (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : ∀ p ∈ P, ‖F p‖ ≤ 1) (n : ℕ) : ‖primePresence P F n‖ ≤ 1 := by
  classical
  unfold primePresence
  rw [norm_prod]
  apply prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro p hp
  split_ifs <;> simp_all

/-- Away from repeated active primes, prime-power agreement outside the
active set identifies the ordinary multiplicative weight exactly. -/
theorem rough_eq_primePresence (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (hF1 : F 1 = 1) (hFm : Multiplicative F)
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hlocal : ∀ p k : ℕ, p.Prime → p ∉ P → p^k ≤ N → F (p^k) = 1)
    (hsq : ∀ p ∈ P, ¬p^2 ∣ n) : F n = primePresence P F n := by
  classical
  rw [← fromPrimePowers_reconstruct F hFm hF1 hn]
  unfold fromPrimePowers primePresence
  rw [Finsupp.prod,Nat.support_factorization]
  apply prod_congr_of_eq_on_inter
  · intro p hp hpP
    exact hlocal p (n.factorization p) (Nat.prime_of_mem_primeFactors hp) hpP
      ((Nat.le_of_dvd hn (Nat.ordProj_dvd n p)).trans hnN)
  · intro p hp hpn
    have hnd : ¬p ∣ n := fun hd => hpn ((hP p hp).mem_primeFactors hd hn.ne')
    simp only [hnd,ite_false]
  · intro p hpn hp
    have hprime := hP p hp
    have hd := Nat.dvd_of_mem_primeFactors hpn
    have hlo := hprime.factorization_pos_of_dvd hn.ne' hd
    have hhi : ¬2 ≤ n.factorization p := fun h => hsq p hp
      ((hprime.pow_dvd_iff_le_factorization hn.ne').mpr h)
    have he : n.factorization p = 1 := by omega
    simp only [he,pow_one,hd,ite_true]

theorem rough_primePresence_phase_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (hF1 : F 1 = 1) (hFm : Multiplicative F) (hFb : OneBounded F)
    (t : ℝ) (N : ℕ)
    (hlocal : ∀ p k : ℕ, p.Prime → p ∉ P → p^k ≤ N → F (p^k) = 1) :
    ‖halaszPhaseMean F t N-halaszPhaseMean (primePresence P F) t N‖ ≤
      2*((repeatedPrimeExceptions P N).card:ℝ) := by
  classical
  have hpF : ∀ p ∈ P, ‖F p‖ ≤ 1 := fun p hp => hFb p (hP p hp).pos
  rw [halaszPhaseMean,halaszPhaseMean,← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Icc 1 N,
        ‖F n*halaszPowerPhase t n-primePresence P F n*halaszPowerPhase t n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, if ∃ p ∈ P, p^2 ∣ n then (2:ℝ) else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases he : ∃ p ∈ P, p^2 ∣ n
      · rw [ite_eq_left he,← sub_mul,norm_mul,halasz_power_phase_norm,mul_one]
        have hbn := hFb n (mem_Icc.mp hn).1
        have hbp := primePresence_norm_le_one P F hpF n
        exact (norm_sub_le _ _).trans (by linarith)
      · rw [ite_eq_right he,rough_eq_primePresence P hP F hF1 hFm
          (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 hlocal
          (fun p hp hd => he ⟨p,hp,hd⟩),sub_self,norm_zero]
    _ = _ := by
      have he : (Icc 1 N).filter (fun n => ∃ p ∈ P, p^2 ∣ n) =
          repeatedPrimeExceptions P N := by
        ext n
        simp only [repeatedPrimeExceptions,mem_filter,mem_Icc,mem_Ioc,Nat.succ_le_iff]
      rw [← sum_filter,he,sum_const,nsmul_eq_mul,mul_comm]

end JointDickman

end OAI
