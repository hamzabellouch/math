import OAI.NumberTheory.TotientAsymptotic.FordFactorization
import OAI.NumberTheory.TotientAsymptotic.PrimeExtensionCoverage

namespace OAI

/-! Exact removal of the ordered largest primes, including short factorizations. -/
noncomputable section
namespace TotientAsymptotic

lemma fordPrime_pos (n k : ℕ) : 0 < fordPrime n k := by
  by_cases hk : k < n.primeFactorsList.length
  · exact (fordPrime_prime hk).pos
  · unfold fordPrime
    rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
    norm_num

lemma fordCofactor_step (n k : ℕ) :
    fordCofactor n k = fordPrime n k * fordCofactor n (k+1) := by
  by_cases hk : k < n.primeFactorsList.length
  · unfold fordCofactor
    rw [List.drop_eq_getElem_cons (by simpa using hk),List.prod_cons,fordPrime_eq_get hk]
  · have hl : n.primeFactorsList.length ≤ k := Nat.le_of_not_gt hk
    have h0 : n.primeFactorsList.reverse.drop k = [] := List.drop_eq_nil_iff.mpr (by simpa using hl)
    have h1 : n.primeFactorsList.reverse.drop (k+1) = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [List.length_reverse]; omega)
    have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using hl)]
      rfl
    simp only [fordCofactor,h0,h1,List.prod_nil,hp,one_mul]

lemma fordCofactor_zero {n : ℕ} (hn : 0 < n) : fordCofactor n 0=n := by
  simp only [fordCofactor,List.drop_zero,List.prod_reverse,Nat.prod_primeFactorsList hn.ne']

lemma fordCofactor_div (n k : ℕ) :
    fordCofactor n k / fordPrime n k = fordCofactor n (k+1) := by
  conv_lhs => rw [fordCofactor_step n k]
  exact Nat.mul_div_cancel_left _ (fordPrime_pos n k)

lemma ford_first_two_factorization {n : ℕ} (hn : 0 < n) :
    n=fordPrime n 0*fordPrime n 1*fordCofactor n 2 := by
  calc
    n = fordCofactor n 0 := (fordCofactor_zero hn).symm
    _ = _ := by
      rw [fordCofactor_step n 0,fordCofactor_step n 1]
      simp only [Nat.reduceAdd]
      ring

lemma fordCofactor_totient_cases (n k : ℕ) :
    (fordCofactor n k).totient=(fordCofactor n (k+1)).totient ∨
    ((fordPrime n k).Prime ∧
    ((fordCofactor n k).totient=(fordPrime n k-1)*(fordCofactor n (k+1)).totient ∨
     (fordCofactor n k).totient=fordPrime n k*(fordCofactor n (k+1)).totient)) := by
  by_cases hk : k < n.primeFactorsList.length
  · right
    have hp := fordPrime_prime hk
    refine ⟨hp,?_⟩
    have hd : fordPrime n k ∣ fordCofactor n k := by
      rw [fordCofactor_step n k]
      exact dvd_mul_right _ _
    simpa only [fordCofactor_div] using totient_prime_extension_cases hp hd
  · left
    have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
      rfl
    rw [fordCofactor_step n k,hp,one_mul]

lemma fordPrime_le_first (n k : ℕ) : fordPrime n k ≤ fordPrime n 0 := by
  by_cases hk : k < n.primeFactorsList.length
  · exact fordPrime_antitone (by omega) hk (Nat.zero_le k)
  · have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
      rfl
    rw [hp]
    exact fordPrime_pos n 0

lemma fordPrime_le_self {n : ℕ} (hn : 0 < n) (k : ℕ) : fordPrime n k ≤ n := by
  by_cases hk : k < n.primeFactorsList.length
  · exact Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList
      (List.mem_reverse.mp (by rw [fordPrime_eq_get hk]; exact List.getElem_mem _)))
  · have hp : fordPrime n k=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
      rfl
    omega

end TotientAsymptotic

end

end OAI
