import Mathlib

namespace OAI

namespace Ostmann.QuadraticSieve

open scoped ArithmeticFunction.Moebius

theorem sum_moebius_divisors_complex (n : ℕ) :
    (∑ k ∈ n.divisors, (μ k : ℂ)) = if n = 1 then 1 else 0 := by
  have hi : (∑ k ∈ n.divisors, μ k) = if n = 1 then 1 else 0 := by
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using
      congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  exact_mod_cast hi

theorem common_divisors_eq_filter_Icc {N n t : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (Finset.Icc 1 N).filter (fun k => k ∣ n ∧ k ∣ t) = (n.gcd t).divisors := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨_, hkn, hkt⟩
    exact ⟨⟨hkn, hkt⟩, Nat.gcd_ne_zero_left hn.ne'⟩
  · rintro ⟨⟨hkn, hkt⟩, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hkn hn, (Nat.le_of_dvd hn hkn).trans hnN⟩, hkn, hkt⟩

theorem sum_common_moebius {N n t : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, if k ∣ n ∧ k ∣ t then (μ k : ℂ) else 0) =
      if n.Coprime t then 1 else 0 := by
  rw [← Finset.sum_filter, common_divisors_eq_filter_Icc hn hnN,
    sum_moebius_divisors_complex]

theorem coprime_bilinear_moebius (S T : Finset ℕ) (F G : ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ n ∈ S, ∑ t ∈ T, if n.Coprime t then F n * G t else 0) =
      ∑ k ∈ Finset.Icc 1 N, (μ k : ℂ) *
        (∑ n ∈ S, if k ∣ n then F n else 0) *
        (∑ t ∈ T, if k ∣ t then G t else 0) := by
  calc
    (∑ n ∈ S, ∑ t ∈ T, if n.Coprime t then F n * G t else 0) =
        ∑ n ∈ S, ∑ t ∈ T,
          (∑ k ∈ Finset.Icc 1 N, if k ∣ n ∧ k ∣ t then (μ k : ℂ) else 0) *
            (F n * G t) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      rw [sum_common_moebius (hS n hn).1 (hS n hn).2]
      split <;> simp
    _ = ∑ n ∈ S, ∑ k ∈ Finset.Icc 1 N, ∑ t ∈ T,
        (if k ∣ n ∧ k ∣ t then (μ k : ℂ) else 0) * (F n * G t) := by
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ S, ∑ t ∈ T,
        (if k ∣ n ∧ k ∣ t then (μ k : ℂ) else 0) * (F n * G t) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hkn : k ∣ n <;> by_cases hkt : k ∣ t <;> simp [hkn, hkt, mul_assoc]

theorem coprime_jacobi_bilinear_moebius (S T : Finset ℕ) (a b : ℕ → ℂ)
    (m : ℤ) (d₁ d₂ N : ℕ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N)
    (hT : ∀ t ∈ T, 0 < t) :
    (∑ n ∈ S, ∑ t ∈ T,
      if n.Coprime t ∧ d₁ ∣ n ∧ d₂ ∣ t then
        a n * b t * (jacobiSym m (n * t) : ℂ) else 0) =
      ∑ k ∈ Finset.Icc 1 N, (μ k : ℂ) *
        (∑ n ∈ S, if k ∣ n ∧ d₁ ∣ n then a n * (jacobiSym m n : ℂ) else 0) *
        (∑ t ∈ T, if k ∣ t ∧ d₂ ∣ t then b t * (jacobiSym m t : ℂ) else 0) := by
  have h := coprime_bilinear_moebius S T
    (fun n => if d₁ ∣ n then a n * (jacobiSym m n : ℂ) else 0)
    (fun t => if d₂ ∣ t then b t * (jacobiSym m t : ℂ) else 0) N hS
  calc
    _ = ∑ n ∈ S, ∑ t ∈ T,
        if n.Coprime t then
          (if d₁ ∣ n then a n * (jacobiSym m n : ℂ) else 0) *
          (if d₂ ∣ t then b t * (jacobiSym m t : ℂ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      rw [jacobiSym.mul_right' m (hS n hn).1.ne' (hT t ht).ne', Int.cast_mul]
      by_cases hnt : n.Coprime t <;> by_cases hdn : d₁ ∣ n <;> by_cases hdt : d₂ ∣ t <;>
        simp [hnt, hdn, hdt]
      ring_nf
    _ = _ := by simpa only [ite_and] using h

theorem shared_divisor_restriction (k d n : ℕ) :
    k ∣ n ∧ d ∣ n ↔ k.lcm d ∣ n := Nat.lcm_dvd_iff.symm

theorem norm_moebius_complex_le_one (k : ℕ) : ‖(μ k : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or k with h | h | h <;> simp [h]

theorem coprime_bilinear_norm_le (S T : Finset ℕ) (F G : ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    ‖∑ n ∈ S, ∑ t ∈ T, if n.Coprime t then F n * G t else 0‖ ≤
      ∑ k ∈ Finset.Icc 1 N,
        ‖∑ n ∈ S, if k ∣ n then F n else 0‖ *
        ‖∑ t ∈ T, if k ∣ t then G t else 0‖ := by
  rw [coprime_bilinear_moebius S T F G N hS]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_mul]
  calc
    _ ≤ 1 * ‖∑ n ∈ S, if k ∣ n then F n else 0‖ *
        ‖∑ t ∈ T, if k ∣ t then G t else 0‖ := by
      gcongr
      exact norm_moebius_complex_le_one k
    _ = _ := by ring

theorem coprime_bilinear_norm_sq_le (S T : Finset ℕ) (F G : ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    ‖∑ n ∈ S, ∑ t ∈ T, if n.Coprime t then F n * G t else 0‖ ^ 2 ≤
      (∑ k ∈ Finset.Icc 1 N, ‖∑ n ∈ S, if k ∣ n then F n else 0‖ ^ 2) *
      (∑ k ∈ Finset.Icc 1 N, ‖∑ t ∈ T, if k ∣ t then G t else 0‖ ^ 2) := by
  calc
    _ ≤ (∑ k ∈ Finset.Icc 1 N,
        ‖∑ n ∈ S, if k ∣ n then F n else 0‖ *
        ‖∑ t ∈ T, if k ∣ t then G t else 0‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (coprime_bilinear_norm_le S T F G N hS) 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem sum_coprime_bilinear_norm_sq_le {ι : Type*} (V : Finset ι)
    (S T : Finset ℕ) (F G : ι → ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T, if n.Coprime t then F v n * G v t else 0‖) ^ 2 ≤
      (∑ v ∈ V, ∑ k ∈ Finset.Icc 1 N, ‖∑ n ∈ S, if k ∣ n then F v n else 0‖ ^ 2) *
      (∑ v ∈ V, ∑ k ∈ Finset.Icc 1 N, ‖∑ t ∈ T, if k ∣ t then G v t else 0‖ ^ 2) := by
  have hle := Finset.sum_le_sum (s := V) (fun v hv => coprime_bilinear_norm_le S T (F v) (G v) N hS)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (V ×ˢ Finset.Icc 1 N)
    (fun x => ‖∑ n ∈ S, if x.2 ∣ n then F x.1 n else 0‖)
    (fun x => ‖∑ t ∈ T, if x.2 ∣ t then G x.1 t else 0‖)
  simp only [Finset.sum_product] at hcs
  exact (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hle 2).trans hcs

theorem sum_divisor_restricted_norm_sq (S : Finset ℕ) (a : ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, ∑ n ∈ S, if k ∣ n then ‖a n‖ ^ 2 else 0) =
      ∑ n ∈ S, (n.divisors.card : ℝ) * ‖a n‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hf : (Finset.Icc 1 N).filter (fun k => k ∣ n) = n.divisors := by
    simpa only [and_self, Nat.gcd_self] using
      common_divisors_eq_filter_Icc (t := n) (hS n hn).1 (hS n hn).2
  rw [← Finset.sum_filter, hf, Finset.sum_const, nsmul_eq_mul]

theorem sum_divisor_restricted_norm_sq_le (S : Finset ℕ) (a : ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, ∑ n ∈ S, if k ∣ n then ‖a n‖ ^ 2 else 0) ≤
      ((S.sup (fun n => n.divisors.card) : ℕ) : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [sum_divisor_restricted_norm_sq S a N hS, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast Finset.le_sup (f := fun n => n.divisors.card) hn

end Ostmann.QuadraticSieve

end OAI
