import OAI.NumberTheory.Jacobsthal.Sieve.AlignedCofactorSplit

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def hitNumerator (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) : ℤ :=
  (r.den : ℤ)*(cofactorHit qf a : ℤ)-r.num

theorem prime_dvd_hitNumerator_iff (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : p ∈ qf.primeFactors) :
    (p : ℤ) ∣ hitNumerator a r qf ↔ aligns (fun t => (a t : ℤ)) r p := by
  have hclass : (cofactorHit qf a : ZMod p) = (a p : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((cofactorHit_spec qf hq a).2.2 p hp)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [hitNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast,hclass,sub_eq_zero,aligns]

theorem alignedCofactor_dvd_hitNumerator (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ) ∣ hitNumerator a r qf := by
  apply Int.natCast_dvd.mpr
  rw [alignedCofactor_eq_product _ r qf hq]
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
  · intro p hp
    obtain ⟨hpf,halign⟩ := Finset.mem_filter.mp hp
    exact Int.natCast_dvd.mp ((prime_dvd_hitNumerator_iff a r qf hq p hpf).mpr halign)

theorem hitNumerator_coprime_den (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) :
    (hitNumerator a r qf).natAbs.Coprime r.den := by
  apply Nat.coprime_of_dvd
  intro p hp hpN hpD
  have hD0 : (r.den : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpD
  have hN0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natCast_dvd.mpr hpN)
  have hA0 : (r.num : ZMod p) = 0 := by
    simpa only [hitNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast,hD0,zero_mul,zero_sub,neg_eq_zero]
      using hN0
  have hpA : p ∣ r.num.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA0)
  have hdiv := Nat.dvd_gcd hpA hpD
  rw [r.reduced.gcd_eq_one] at hdiv
  exact hp.not_dvd_one hdiv

theorem hitNumerator_coprime_bad (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (hitNumerator a r qf).natAbs.Coprime (badPrimeProduct (fun t => (a t : ℤ)) r qf) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨hpf,hnon⟩ := Finset.mem_filter.mp hp
  apply Nat.Coprime.symm
  apply (Nat.prime_of_mem_primeFactors hpf).coprime_iff_not_dvd.mpr
  intro hdiv
  exact hnon ((prime_dvd_hitNumerator_iff a r qf hq p hpf).mp (Int.natCast_dvd.mpr hdiv))

end ErdosVarianceEffective

end

end Erdos970

end OAI
