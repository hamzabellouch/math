import OAI.NumberTheory.TotientAsymptotic.FirstFailedRow
import OAI.NumberTheory.TotientAsymptotic.FordLargestPrime

namespace OAI

/-! Exact totient factorization at a strict gap in the ordered prime list. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma fordCofactor_largest_exact (n k : ℕ) :
    largestPrimeFactor (fordCofactor n k) = fordPrime n k := by
  rw [← fordPrime_zero_eq_largest,fordCofactor_prime,Nat.add_zero]

theorem strict_cofactor_coprime {n k : ℕ} (hk : 0 < k)
    (hklen : k ≤ n.primeFactorsList.length)
    (hgap : fordPrime n k < fordPrime n (k-1)) :
    (fordCofactor n k).Coprime (∏ i ∈ Finset.range k, fordPrime n i) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro i hi
  have hi := Finset.mem_range.mp hi
  have hip := fordPrime_prime (show i < n.primeFactorsList.length by omega)
  apply Nat.Coprime.symm
  apply hip.coprime_iff_not_dvd.mpr
  intro hd
  have hle := prime_dvd_le_largest hip (fordCofactor_pos n k).ne' hd
  rw [fordCofactor_largest_exact] at hle
  have horder := fordPrime_antitone (show i < n.primeFactorsList.length by omega)
    (show k-1 < n.primeFactorsList.length by omega) (show i ≤ k-1 by omega)
  omega

theorem strict_cofactor_totient {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hklen : k ≤ n.primeFactorsList.length)
    (hgap : fordPrime n k < fordPrime n (k-1)) :
    n.totient = (fordCofactor n k).totient *
      (∏ i ∈ Finset.range k, fordPrime n i).totient := by
  have hcop := strict_cofactor_coprime hk hklen hgap
  conv_lhs => rw [ford_factorization hn hklen]
  exact Nat.totient_mul hcop

theorem first_failed_row_totient {x : ℝ} {n N j : ℕ} (hn : 0 < n) (hj : 0 < j)
    (hprev : fordRowSum N (fordPrimeCoordinate n) (j-1) ≤
      xi x (j-1)*fordPrimeCoordinate n (j-1))
    (hfail : xi x j*fordPrimeCoordinate n j < fordRowSum N (fordPrimeCoordinate n) j) :
    n.totient = (fordCofactor n j).totient *
      (∏ i ∈ Finset.range j, fordPrime n i).totient :=
  strict_cofactor_totient hn hj (failed_row_index hfail).le
    (first_failed_row_prime_separation hj hprev hfail)

lemma fordCofactor_comp (n i j : ℕ) :
    fordCofactor (fordCofactor n i) j = fordCofactor n (i+j) := by
  change ((fordCofactor n i).primeFactorsList.reverse.drop j).prod =
    (n.primeFactorsList.reverse.drop (i+j)).prod
  rw [fordCofactor_primeFactorsList,List.drop_drop]

lemma fordCofactor_length (n i : ℕ) :
    (fordCofactor n i).primeFactorsList.length = n.primeFactorsList.length-i := by
  have hh := congrArg List.length (fordCofactor_primeFactorsList n i)
  simpa only [List.length_reverse,List.length_drop] using hh

/-- The leading prime may have either totient-extension branch. After its
removal, the strict boundary still gives an exact residual-value encoding. -/
theorem strict_gap_residual_totient {n j : ℕ} (hn : 0 < n) (hj : 0 < j)
    (hjlen : j ≤ n.primeFactorsList.length)
    (hgap : fordPrime n j < fordPrime n (j-1)) :
    (n/fordPrime n 0).totient = (fordCofactor n j).totient *
      (∏ i : Fin (j-1), fordPrime n (i.val+1)).totient := by
  have he : n/fordPrime n 0=fordCofactor n 1 := by
    simpa only [fordCofactor_zero hn,Nat.zero_add] using fordCofactor_div n 0
  rw [he]
  by_cases hj1 : j=1
  · subst j
    simp
  · have hk : 0 < j-1 := by omega
    have hklen : j-1 ≤ (fordCofactor n 1).primeFactorsList.length := by
      rw [fordCofactor_length]
      omega
    have hs : fordPrime (fordCofactor n 1) (j-1) <
        fordPrime (fordCofactor n 1) (j-1-1) := by
      simp only [fordCofactor_prime]
      convert hgap using 1 <;> congr 1 <;> omega
    have hh := strict_cofactor_totient (fordCofactor_pos n 1) hk hklen hs
    rw [fordCofactor_comp,show 1+(j-1)=j by omega] at hh
    rw [Fin.prod_univ_eq_prod_range (fun i => fordPrime n (i+1))]
    simpa only [fordCofactor_prime,Nat.add_comm 1] using hh

end TotientAsymptotic

end

end OAI
