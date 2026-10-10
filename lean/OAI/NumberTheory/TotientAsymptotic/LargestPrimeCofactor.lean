import OAI.NumberTheory.TotientAsymptotic.NormalityPrimeRemoval
import OAI.NumberTheory.TotientAsymptotic.AbnormalCofactorMass
import OAI.NumberTheory.TotientAsymptotic.NormalitySize

namespace OAI

/-! The actual largest-prime/cofactor decomposition for a nonnormal prime. -/
noncomputable section
namespace TotientAsymptotic

lemma largestPrimeFactor_mem {n : ℕ} (hn : 2 ≤ n) : largestPrimeFactor n ∈ n.primeFactors := by
  have he := (Nat.nonempty_primeFactors).mpr (show 1 < n by omega)
  have hm := Finset.sup_mem_of_nonempty (f:=id) he
  obtain ⟨p,hp,hpmax⟩ := hm
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  unfold largestPrimeFactor
  change p = n.primeFactors.sup id at hpmax
  rw [← hpmax,max_eq_right (show 1 ≤ p by omega)]
  exact hp

lemma nonnormal_largest_cofactor {S : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S)
    {p N : ℕ} (hp : p.Prime) (hpN : p ≤ N) (hbad : ¬IsNormalPrime S p) :
    ∃ b q : ℕ,0 < b ∧ q.Prime ∧ q=largestPrimeFactor (p-1) ∧
      p=b*q+1 ∧ b ≤ N ∧ AbnormalCofactor S N b := by
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    exact hbad (normal_two hS hBS)
  have hpm : 2 ≤ p-1 := by have := hp.two_le; omega
  let q := largestPrimeFactor (p-1)
  have hqm := largestPrimeFactor_mem hpm
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
  have hqd : q ∣ p-1 := Nat.dvd_of_mem_primeFactors hqm
  let b := (p-1)/q
  have hbq : b*q=p-1 := Nat.div_mul_cancel hqd
  have hb0 : 0 < b := by
    by_contra hh
    have hbz : b=0 := Nat.eq_zero_of_not_pos hh
    rw [hbz,zero_mul] at hbq
    omega
  have hpEq : p=b*q+1 := by omega
  have hbN : b ≤ N := by
    have h1 : b ≤ b*q := Nat.le_mul_of_pos_right b hq.pos
    omega
  have hco := nonnormal_prime_cofactor (Nat.ne_of_gt hb0) hq
    (by rwa [← hpEq]) S (by rwa [← hpEq])
  refine ⟨b,q,hb0,hq,rfl,hpEq,hbN,?_⟩
  rcases hco with hs|⟨U,T,hSU,hUT,hT,hh⟩
  · exact Or.inl hs
  · refine Or.inr ⟨U,T,hSU,hUT,hT.trans ?_,hh⟩
    exact_mod_cast (show b*q ≤ N by omega)

end TotientAsymptotic

end

end OAI
