import OAI.NumberTheory.TotientAsymptotic.TwoExceptionalPrimeLayer
import OAI.NumberTheory.TotientAsymptotic.ShiftDivisorMass

namespace OAI

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma empty_prime_initial_mass {N : ℕ} (Q : Finset (Fin N → ℕ)) :
    (∑ p ∈ Q.image (fun p => primeInitial p 0 (Nat.zero_le N)), reciprocalShiftWeight p) ≤ 1 := by
  classical
  have hc : (Q.image (fun p => primeInitial p 0 (Nat.zero_le N))).card ≤ 1 :=
    Finset.card_le_one.mpr (fun p _ q _ => Subsingleton.elim _ _)
  have hcR : ((Q.image (fun p => primeInitial p 0 (Nat.zero_le N))).card : ℝ) ≤ 1 := by exact_mod_cast hc
  simpa only [reciprocalShiftWeight,Fin.prod_univ_zero,Nat.cast_one,inv_one,
    Finset.sum_const,nsmul_eq_mul,smul_eq_mul,mul_one,Nat.cast_le,Nat.cast_one] using
    hcR

lemma prime_square_mass {d h N q : ℕ} (hN : 1 ≤ N) (hq : q.Prime) (hd : d ≤ h)
    (Q : Finset (Fin d → ℕ)) (j k : Fin d) {E : ℝ} (hE : 1 ≤ E)
    (hU : ∀ p ∈ Q, ∀ l, p l ∈ Nat.primesLE N)
    (hdiv : ∀ p ∈ Q, if j=k then q^2 ∣ p j-1 else q ∣ p j-1 ∧ q ∣ p k-1)
    (hmass : (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ E) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (1+Real.log N)^2*E^h*((q : ℝ)^2)⁻¹ := by
  classical
  let A := 1+Real.log N
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 1 ≤ A := by dsimp [A]; linarith [Real.log_nonneg hNR]
  have hpre := empty_prime_initial_mass Q
  have hpow (e : ℕ) (he : e ≤ h) :
      (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹)^e ≤ E^h :=
    (pow_le_pow_left₀ (by positivity) hmass e).trans (pow_le_pow_right₀ hE he)
  have hfinal (p : Fin d → ℕ) (l : Fin d) : primeFinal p 0 l=p l := by
    unfold primeFinal
    congr 1
    apply Fin.ext
    simp
  by_cases hjk : j=k
  · have hV : ∀ p ∈ Q, primeFinal p 0 j ∈ shiftDivisiblePrimes N (q^2) := by
      intro p hp
      rw [hfinal]
      apply Finset.mem_filter.mpr
      exact ⟨hU p hp j,by simpa only [ite_eq_left hjk] using hdiv p hp⟩
    have hu : ∀ p ∈ Q, ∀ l, primeFinal p 0 l ∈ Nat.primesLE N := by
      intro p hp l
      simpa only [hfinal] using hU p hp l
    have hh := prime_mass_one_exception (Nat.zero_le d) Q j _ _ hu hV
    have hv0 := shifted_divisor_mass N (pow_pos hq.pos 2)
    have hv : (∑ p ∈ shiftDivisiblePrimes N (q^2), ((p-1 : ℕ) : ℝ)⁻¹) ≤ A^2/((q : ℝ)^2) := by
      have hh : (∑ p ∈ shiftDivisiblePrimes N (q^2), ((p-1 : ℕ) : ℝ)⁻¹) ≤ A/((q : ℝ)^2) := by
        simpa only [A,Nat.cast_pow] using hv0
      exact hh.trans (div_le_div_of_nonneg_right (by nlinarith : A ≤ A^2) (by positivity))
    have hm := mul_le_mul (mul_le_mul hpre hv (by positivity) (by norm_num))
      (hpow (d-0-1) (by omega)) (by positivity) (by positivity)
    exact hh.trans (by simpa only [one_mul,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hm)
  · have hV : ∀ p ∈ Q, primeFinal p 0 j ∈ shiftDivisiblePrimes N q := by
      intro p hp
      rw [hfinal]
      exact Finset.mem_filter.mpr ⟨hU p hp j,(by simpa only [ite_eq_right hjk] using hdiv p hp : q ∣ p j-1 ∧ q ∣ p k-1).1⟩
    have hW : ∀ p ∈ Q, primeFinal p 0 k ∈ shiftDivisiblePrimes N q := by
      intro p hp
      rw [hfinal]
      exact Finset.mem_filter.mpr ⟨hU p hp k,(by simpa only [ite_eq_right hjk] using hdiv p hp : q ∣ p j-1 ∧ q ∣ p k-1).2⟩
    have hu : ∀ p ∈ Q, ∀ l, primeFinal p 0 l ∈ Nat.primesLE N := by
      intro p hp l
      simpa only [hfinal] using hU p hp l
    have hh := prime_mass_two_exceptions (Nat.zero_le d) Q j k hjk _ _ _ hu hV hW
    have hv : (∑ p ∈ shiftDivisiblePrimes N q, ((p-1 : ℕ) : ℝ)⁻¹) ≤ A/(q : ℝ) := shifted_divisor_mass N hq.pos
    have hm := mul_le_mul (mul_le_mul (mul_le_mul hpre hv (by positivity) (by norm_num)) hv
      (by positivity) (by positivity)) (hpow (d-0-2) (by omega)) (by positivity) (by positivity)
    apply hh.trans
    convert hm using 1; dsimp [A]; ring

end TotientAsymptotic

end

end OAI
