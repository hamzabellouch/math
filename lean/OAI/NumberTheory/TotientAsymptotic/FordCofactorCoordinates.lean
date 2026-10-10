import OAI.NumberTheory.TotientAsymptotic.FordCofactorStep

namespace OAI

/-! Removing an ordered prime prefix shifts all remaining Ford coordinates. -/
noncomputable section
namespace TotientAsymptotic

lemma fordCofactor_primeFactorsList (n k : ℕ) :
    (fordCofactor n k).primeFactorsList.reverse = n.primeFactorsList.reverse.drop k := by
  let l := n.primeFactorsList.reverse.drop k
  have hprime : ∀ p ∈ l,p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.mem_of_mem_drop hp))
  have hp := Nat.primeFactorsList_unique (n:=fordCofactor n k) (l:=l) rfl hprime
  have hrev : n.primeFactorsList.reverse.SortedGE := (Nat.primeFactorsList_sorted n).reverse
  have hs : l.SortedGE := (hrev.pairwise.sublist (List.drop_sublist k _)).sortedGE
  have ht := (Nat.primeFactorsList_sorted (fordCofactor n k)).reverse
  exact (hp.trans (List.reverse_perm _).symm).eq_of_sortedGE hs ht |>.symm

lemma fordCofactor_prime (n k i : ℕ) :
    fordPrime (fordCofactor n k) i = fordPrime n (k+i) := by
  unfold fordPrime
  rw [fordCofactor_primeFactorsList,List.getElem?_drop]

lemma fordCofactor_coordinate (n k i : ℕ) :
    fordPrimeCoordinate (fordCofactor n k) i = fordPrimeCoordinate n (k+i) := by
  simp only [fordPrimeCoordinate,primeDoubleLog,fordCofactor_prime]

end TotientAsymptotic

end

end OAI
