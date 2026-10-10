import OAI.NumberTheory.TotientAsymptotic.BandExtraction
import OAI.NumberTheory.TotientAsymptotic.SmoothSuffix

namespace OAI

/-! Canonical finite prime-factor decomposition for the Ford coordinates. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma fordPrime_eq_get {n i : ℕ} (hi : i < n.primeFactorsList.length) :
    fordPrime n i = n.primeFactorsList.reverse[i]'(by simpa using hi) := by
  unfold fordPrime
  rw [show n.primeFactorsList.reverse[i]? = some (n.primeFactorsList.reverse[i]'(by simpa using hi)) from
    List.getElem?_eq_getElem _]
  rfl

lemma fordPrime_prime {n i : ℕ} (hi : i < n.primeFactorsList.length) : (fordPrime n i).Prime := by
  rw [fordPrime_eq_get hi]
  exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.getElem_mem _))

lemma fordPrime_antitone {n i j : ℕ} (hi : i < n.primeFactorsList.length)
    (hj : j < n.primeFactorsList.length) (hij : i ≤ j) : fordPrime n j ≤ fordPrime n i := by
  rw [fordPrime_eq_get hi,fordPrime_eq_get hj]
  exact (Nat.primeFactorsList_sorted n).reverse.getElem_ge_getElem_of_le hij

lemma fordPrime_index_of_doubleLog_pos {n i : ℕ} (h : 0 < primeDoubleLog n i) :
    i < n.primeFactorsList.length := by
  by_contra! hi
  have he : fordPrime n i=1 := by
    unfold fordPrime
    rw [show n.primeFactorsList.reverse[i]? = none from List.getElem?_eq_none (by simpa using hi)]
    rfl
  simp [primeDoubleLog,he] at h

def fordCofactor (n k : ℕ) : ℕ := (n.primeFactorsList.reverse.drop k).prod

lemma fordCofactor_pos (n k : ℕ) : 0 < fordCofactor n k := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.mem_of_mem_drop hp))).pos

lemma ford_prefix_product {n k : ℕ} (hk : k ≤ n.primeFactorsList.length) :
    (n.primeFactorsList.reverse.take k).prod = ∏ i ∈ Finset.range k, fordPrime n i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.prod_take_succ _ _ (by simpa using hk),ih (by omega),Finset.prod_range_succ,
      fordPrime_eq_get (by omega)]

lemma ford_factorization {n k : ℕ} (hn : 0 < n) (hk : k ≤ n.primeFactorsList.length) :
    n=fordCofactor n k*∏ i ∈ Finset.range k, fordPrime n i := by
  rw [← ford_prefix_product hk,fordCofactor,mul_comm,List.prod_take_mul_prod_drop,
    List.prod_reverse,Nat.prod_primeFactorsList hn.ne']

lemma fordCofactor_largest {n j : ℕ} (hj : j < n.primeFactorsList.length) :
    largestPrimeFactor (fordCofactor n (j+1)) ≤ fordPrime n j := by
  let l := n.primeFactorsList.reverse.drop (j+1)
  have hp (i : Fin l.length) : (l[i.val]).Prime :=
    Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.mem_of_mem_drop (List.getElem_mem _)))
  have he : fordCofactor n (j+1) = ∏ i : Fin l.length, l[i.val] :=
    (Fin.prod_univ_getElem l).symm
  rw [he]
  apply largestPrimeFactor_prod_le _ _ (fordPrime_prime hj).one_lt.le
  intro i _
  rw [largestPrimeFactor_prime (hp i)]
  have hi := i.isLt
  have hi' : j+1+i.val < n.primeFactorsList.length := by
    dsimp [l] at hi
    simp only [List.length_drop,List.length_reverse] at hi
    omega
  have hget : l[i.val]=fordPrime n (j+1+i.val) := by
    rw [fordPrime_eq_get hi']
    exact List.getElem_drop
  rw [hget]
  exact fordPrime_antitone hj hi' (by omega)

end TotientAsymptotic

end

end OAI
