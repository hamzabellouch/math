import OAI.NumberTheory.JointDickman.Amplification.ActualArithmeticLimit

namespace OAI

/-! # Prime-square periodicity of the actual candidate quotient data -/

namespace JointDickman
open Finset Classical

theorem affine_quotient_modEq_prime {a b c m m' n n' p : ℕ}
    (hp : p.Prime) (hsq : Squarefree (a*b))
    (he : a*b*m+b = c*n) (he' : a*b*m'+b = c*n')
    (hn : n ≡ n' [MOD p^2]) : p ∣ m ↔ p ∣ m' := by
  have hab : a*b*m ≡ a*b*m' [MOD p^2] :=
    Nat.ModEq.add_right_cancel' b (by simpa only [he,he'] using hn.mul_left c)
  by_cases hd : p ∣ a*b
  · have hdd : ¬ p^2 ∣ a*b := by
      simpa only [pow_two] using (Nat.squarefree_iff_prime_squarefree.mp hsq p hp)
    rw [← prime_square_product_iff hp hd hdd,← prime_square_product_iff hp hd hdd]
    exact hab.dvd_iff (dvd_refl _)
  · have h := hab.dvd_iff (dvd_pow_self p (by omega : 2 ≠ 0))
    have hna : ¬ p ∣ a := fun ha => hd (dvd_mul_of_dvd_left ha b)
    have hnb : ¬ p ∣ b := fun hb => hd (dvd_mul_of_dvd_right hb a)
    simpa only [hp.dvd_mul,hna,hnb,false_or] using h

theorem coefficientPrimeSet_modEq {B n m : ℕ}
    (h : n ≡ m [MOD auxiliarySquarePeriod B]) :
    coefficientPrimeSet B n = coefficientPrimeSet B m := by
  simpa only [prod_empty,Nat.div_one] using
    coefficientPrimeSet_quotient_modEq (A := ∅) h (empty_subset _) (one_dvd n) (one_dvd m)

theorem blockPrimeSites_modEq {B M u v : ℕ}
    (h : u ≡ v [MOD auxiliarySquarePeriod B]) :
    (fun i : Fin M => coefficientPrimeSet B (u+(i.val+1))) =
      (fun i : Fin M => coefficientPrimeSet B (v+(i.val+1))) := by
  funext i
  exact coefficientPrimeSet_modEq (h.add_right _)

theorem candidateLowHigh_squarefree {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} (hS : ∀ i, S i ⊆ auxiliaryPrimes B)
    {e : BlockCandidateIndex M} (he : e ∈ blockCandidates B L T H M τ C S) :
    Squarefree (candidateHigh e*candidateLow e) := by
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  have hlow := (mem_endpointSplits.mp hs.1).1.trans (hS e.1.1)
  have hhigh := (mem_endpointSplits.mp hs.2).1.trans (hS e.1.2)
  apply (Nat.squarefree_mul ha.2.2.2.2.2.1.symm).mpr
  exact ⟨primeProduct_squarefree _ (fun p hp => auxiliaryPrimes_prime B p (hhigh hp)),
    primeProduct_squarefree _ (fun p hp => auxiliaryPrimes_prime B p (hlow hp))⟩

theorem candidateArithmeticQuotient_modEq {B L T H M u v : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (h : u ≡ v [MOD auxiliarySquarePeriod B])
    {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))) :
    coefficientPrimeSet B (candidateArithmeticQuotient u e) =
      coefficientPrimeSet B (candidateArithmeticQuotient v e) := by
  have hs := blockPrimeSites_modEq (M := M) h
  have he' := he
  rw [hs] at he'
  have hsq := candidateLowHigh_squarefree (fun _ => filter_subset _ _) he
  have heq := candidateArithmeticQuotient_equation hT he
  have heq' := candidateArithmeticQuotient_equation hT he'
  ext p
  by_cases hp : p ∈ auxiliaryPrimes B
  · have hprime := auxiliaryPrimes_prime B p hp
    have hn := (h.add_right (e.1.1.val+1)).of_dvd (auxiliarySquare_dvd_period hp)
    simp only [coefficientPrimeSet,mem_filter,hp,true_and]
    exact affine_quotient_modEq_prime hprime hsq heq heq' hn
  · simp [coefficientPrimeSet,hp]

end JointDickman

end OAI
