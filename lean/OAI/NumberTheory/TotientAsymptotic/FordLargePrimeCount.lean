import OAI.NumberTheory.TotientAsymptotic.FordFactorization
import OAI.NumberTheory.TotientAsymptotic.NormalTotientBands
import OAI.NumberTheory.TotientAsymptotic.SquarefreeCollisionMass

namespace OAI

/-! Ford's ordered prime coordinates give the required number of distinct large primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_prefix_omega_lower {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n.primeFactorsList.length)
    {U : ℝ} (hU : U < (fordPrime n (k-1):ℝ)) :
    k ≤ omegaIn n U n := by
  let l := n.primeFactorsList.reverse
  let P := fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ n)
  have htake : (l.take k).filter P=l.take k := by
    apply List.filter_eq_self.mpr
    intro p hp
    have hpfull : p ∈ n.primeFactorsList :=
      List.mem_reverse.mp (List.mem_of_mem_take hp)
    have hpn : (p:ℝ) ≤ n := by exact_mod_cast Nat.le_of_mem_primeFactorsList hpfull
    apply decide_eq_true
    refine ⟨?_,hpn⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
    have hik : i < k := by
      have hh : (l.take k).length=min k l.length := List.length_take
      omega
    have hin : i < n.primeFactorsList.length := by omega
    have he' : fordPrime n i=p := by
      rw [fordPrime_eq_get hin]
      simpa only [l,List.getElem_take] using he
    rw [← he']
    have hord : fordPrime n (k-1) ≤ fordPrime n i :=
      fordPrime_antitone hin (by omega) (by omega)
    exact hU.trans_le (by exact_mod_cast hord)
  have hsub := (List.take_sublist k l).filter P
  rw [htake] at hsub
  have hh := hsub.length_le
  have hkl : k ≤ l.length := by simpa [l] using hkn
  rw [List.length_take,min_eq_left hkl] at hh
  simpa only [l,P,List.filter_reverse,List.length_reverse,omegaIn] using hh

def distinctPrimesAbove (n : ℕ) (U : ℝ) : Finset ℕ :=
  (partBetween n U n).primeFactors

lemma distinctPrimesAbove_subset {n : ℕ} (hn : 0 < n) (U : ℝ) :
    distinctPrimesAbove n U ⊆ n.primeFactors := by
  intro p hp
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
    (Nat.dvd_of_mem_primeFactors hp).trans (partBetween_dvd hn.ne' U n),hn.ne'⟩

lemma distinctPrimesAbove_large (n : ℕ) (U : ℝ) {p : ℕ}
    (hp : p ∈ distinctPrimesAbove n U) : U < (p:ℝ) := by
  have hp' : p ∈ (partBetween n U n).primeFactorsList := List.mem_toFinset.mp hp
  exact (partBetween_support n U n hp').1

lemma distinctPrimesAbove_card {n : ℕ} (hn : 0 < n) {U : ℝ} (hsq : SquarefreeAbove n U) :
    (distinctPrimesAbove n U).card=omegaIn n U n := by
  rw [distinctPrimesAbove,squarefree_primeFactors_card (partBetween_squarefree hn.ne' hsq),
    partBetween_omega]

lemma ford_prefix_distinct_primes {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ≤ n.primeFactorsList.length) {U : ℝ}
    (hU : U < (fordPrime n (k-1):ℝ)) (hsq : SquarefreeAbove n U) :
    k ≤ (distinctPrimesAbove n U).card := by
  rw [distinctPrimesAbove_card hn hsq]
  exact ford_prefix_omega_lower hk hkn hU

end TotientAsymptotic

end

end OAI
