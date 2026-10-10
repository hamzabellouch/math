import OAI.NumberTheory.TwoPointCorrelations.FinitePrimePhases
import OAI.NumberTheory.TwoPointCorrelations.DivisibilityPrefix

namespace OAI

/-! The corrected Ramaré identity from MRT v3, equation (3.2).
The denominator retains `1_{p ∤ m}`; repeated prime factors are allowed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma finitePrimeDivisorCount_eq_card (P : Finset ℕ) (n : ℕ) :
    finitePrimeDivisorCount P n = (P.filter (fun p => p ∣ n)).card := by
  simp [finitePrimeDivisorCount, sum_boole]

lemma finitePrimeDivisorCount_insert {P : Finset ℕ} {p : ℕ} (hp : p ∉ P) (n : ℕ) :
    finitePrimeDivisorCount (insert p P) n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount P n := by
  simp only [finitePrimeDivisorCount, sum_insert hp]

lemma finitePrimeDivisorCount_pos_of_mem {P : Finset ℕ} {p n : ℕ}
    (hp : p ∈ P) (hpn : p ∣ n) : 0 < finitePrimeDivisorCount P n := by
  rw [finitePrimeDivisorCount_eq_card, card_pos]
  exact ⟨p, mem_filter.mpr ⟨hp, hpn⟩⟩

/-- The correction term distinguishes a new prime from a repeated prime. -/
theorem mrt_prime_divisor_count_mul (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) (m : ℕ) :
    finitePrimeDivisorCount P (p * m) =
      (if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m := by
  have hc (n : ℕ) : finitePrimeDivisorCount P n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount (P.erase p) n := by
    conv_lhs => rw [← insert_erase hp]
    exact finitePrimeDivisorCount_insert (notMem_erase p P) n
  have he : finitePrimeDivisorCount (P.erase p) (p * m) =
      finitePrimeDivisorCount (P.erase p) m := by
    unfold finitePrimeDivisorCount
    apply sum_congr rfl
    intro q hq
    have hq' := mem_erase.mp hq
    have hqprime := hP q hq'.2
    have hqp : ¬q ∣ p := by
      intro hdiv
      exact hq'.1 ((Nat.prime_dvd_prime_iff_eq hqprime (hP p hp)).mp hdiv)
    simp only [hqprime.dvd_mul, hqp, false_or]
  rw [hc (p * m), hc m, he]
  simp only [dvd_mul_right, ite_true]
  split_ifs <;> omega

lemma mrt_ramare_common_denominator (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    (∑ p ∈ P, if p ∣ n then F n / (finitePrimeDivisorCount P n : ℂ) else 0) =
      if finitePrimeDivisorCount P n = 0 then 0 else F n := by
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, ← finitePrimeDivisorCount_eq_card]
  by_cases hn : finitePrimeDivisorCount P n = 0
  · simp [hn]
  · rw [ite_eq_right hn]
    have hn' : (finitePrimeDivisorCount P n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp

/-- Corrected pointwise factorization, with no squarefree assumption. -/
theorem mrt_ramare_identity (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (n : ℕ) :
    (if finitePrimeDivisorCount P n = 0 then 0 else F n) =
      ∑ p ∈ P, if p ∣ n then
        F (p * (n / p)) /
          (((if p ∣ n / p then 0 else 1) + finitePrimeDivisorCount P (n / p) : ℕ) : ℂ)
        else 0 := by
  rw [← mrt_ramare_common_denominator P F n]
  apply sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · simp only [hpn, ite_true]
    have he := Nat.mul_div_cancel' hpn
    have hc := mrt_prime_divisor_count_mul P hP hp (n / p)
    rw [he] at hc ⊢
    rw [hc]
  · simp only [hpn, ite_false]

/-- Exact finite prime/cofactor decomposition of a supported sum. -/
theorem mrt_ramare_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, if finitePrimeDivisorCount P n = 0 then 0 else F n) =
      ∑ p ∈ P, ∑ m ∈ Icc 1 (N / p),
        F (p * m) /
          (((if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m : ℕ) : ℂ) := by
  simp_rw [← mrt_ramare_common_denominator P F]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have he := divisibility_positivePrefix
    (fun n => F n / (finitePrimeDivisorCount P n : ℂ)) p N (hP p hp).pos
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, ite_mul, one_mul, zero_mul] at he
  rw [he]
  apply sum_congr rfl
  intro m _
  rw [mrt_prime_divisor_count_mul P hP hp m]

lemma mrt_inverse_successor_difference {k : ℕ} (hk : 0 < k) :
    ‖(k : ℂ)⁻¹ - ((k + 1 : ℕ) : ℂ)⁻¹‖ ≤ 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1C : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have he : (k : ℂ)⁻¹ - ((k + 1 : ℕ) : ℂ)⁻¹ =
      ((1 / ((k : ℝ) * (k + 1)) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  apply (div_le_one (by positivity)).mpr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- Replacing the corrected denominator by `ω_P(m)+1` costs only the
prime-square terms.  This is the correction explicitly needed in MRT v3. -/
theorem mrt_ramare_denominator_error (P : Finset ℕ) {p m : ℕ}
    (hp : p ∈ P) (z : ℂ) :
    ‖z / (((if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m : ℕ) : ℂ) -
      z / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)‖ ≤
        if p ∣ m then ‖z‖ else 0 := by
  by_cases hpm : p ∣ m
  · simp only [hpm, ite_true, zero_add]
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, norm_mul]
    have hk := finitePrimeDivisorCount_pos_of_mem hp hpm
    exact (mul_le_mul_of_nonneg_left (mrt_inverse_successor_difference hk)
      (norm_nonneg z)).trans_eq (mul_one _)
  · simp only [hpm, ite_false, Nat.add_comm 1, sub_self, norm_zero, le_refl]

theorem mrt_ramare_sum_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (N : ℕ) :
    ‖(∑ n ∈ Icc 1 N, if finitePrimeDivisorCount P n = 0 then 0 else F n) -
      (∑ p ∈ P, ∑ m ∈ Icc 1 (N / p),
        F (p * m) / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ))‖ ≤
      ∑ p ∈ P, ∑ m ∈ Icc 1 (N / p), if p ∣ m then ‖F (p * m)‖ else 0 := by
  rw [mrt_ramare_sum P hP F N, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro m _
  exact mrt_ramare_denominator_error P hp _

lemma mrt_count_multiples {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ m ∈ Icc 1 N, if p ∣ m then (1 : ℝ) else 0) = (N / p : ℕ) := by
  have he := divisibility_positivePrefix (fun _ => (1 : ℂ)) p N hp
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, mul_one,
    sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum, apply_ite, Complex.one_re, Complex.zero_re,
    Complex.natCast_re] using hr

/-- The prime-square exceptional contribution has the expected reciprocal
square bound.  No sieve estimate is needed for this error. -/
theorem mrt_ramare_error_of_bounded (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (N : ℕ) (hF : ∀ n, 0 < n → ‖F n‖ ≤ 1) :
    ‖(∑ n ∈ Icc 1 N, if finitePrimeDivisorCount P n = 0 then 0 else F n) -
      (∑ p ∈ P, ∑ m ∈ Icc 1 (N / p),
        F (p * m) / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ))‖ ≤
      (N : ℝ) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
  apply (mrt_ramare_sum_error P hP F N).trans
  calc
    _ ≤ ∑ p ∈ P, ∑ m ∈ Icc 1 (N / p), if p ∣ m then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro m hm
      split_ifs
      · exact hF (p * m) (Nat.mul_pos (hP p hp).pos (mem_Icc.mp hm).1)
      · rfl
    _ = ∑ p ∈ P, ((N / (p * p) : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro p hp
      rw [mrt_count_multiples (hP p hp).pos, Nat.div_div_eq_div_mul]
    _ ≤ ∑ p ∈ P, (N : ℝ) * (1 / (p : ℝ) ^ 2) := by
      apply sum_le_sum
      intro p _
      convert (Nat.cast_div_le (m := N) (n := p * p) :
        ((N / (p * p) : ℕ) : ℝ) ≤ (N : ℝ) / (p * p : ℕ)) using 1
      push_cast
      ring
    _ = _ := (mul_sum _ _ _).symm

end TwoPointCorrelations

end OAI
