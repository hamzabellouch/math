import OAI.NumberTheory.Jacobsthal.Sieve.TagUnitSieveLower

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open ErdosUnitLifts Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

lemma actual_bad_iff (D t : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (p : ℕ)
    (ht : t.Prime) (htD : ¬t∣D) (hint : (D:ℤ)∣A+B*p) :
    (actualN D A B p:ZMod t)=residue t ↔
      (B:ZMod t)*(p:ZMod t)=(D:ZMod t)*(residue t)-A := by
  have hn : (D:ℤ)*actualN D A B p=A+B*p := by
    unfold actualN
    rw [mul_comm]
    exact Int.ediv_mul_cancel hint
  have hh := congrArg (fun z : ℤ => (z:ZMod t)) hn
  simp only [Int.cast_mul,Int.cast_add,Int.cast_natCast] at hh
  have hu : IsUnit (D:ZMod t) := (ZMod.isUnit_iff_coprime _ _).mpr
    (ht.coprime_iff_not_dvd.mpr htD).symm
  constructor
  · intro he
    rw [he] at hh
    linear_combination -hh
  · intro he
    apply hu.mul_left_cancel
    rw [hh,he]
    ring

lemma mul_forbidden_iff (D t : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (p : ℕ)
    (hB : IsUnit (B:ZMod t)) :
    (B:ZMod t)*(p:ZMod t)=(D:ZMod t)*(residue t)-A ↔
      (p:ZMod t)=forbiddenClass D A B residue t := by
  have hh := affine_eq_iff t 0 B ((D:ℤ)*(residue t)-A) hB (p:ZMod t)
  simpa only [Int.cast_zero,zero_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast,sub_zero,forbiddenClass] using hh

lemma prime_cast_ne_zero_of_large (P : ℝ) (p t : ℕ) (hp : p.Prime) (hPp : P ≤ (p:ℝ))
    (ht : t∈smallPrimeSet P) : (p:ZMod t)≠0 := by
  obtain ⟨htp,htP⟩ := (mem_smallPrimeSet P t).mp ht
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff p t).mp hz
  rcases hp.eq_one_or_self_of_dvd t hd with he | he
  · exact htp.ne_one he
  · have her : (t:ℝ)=p := by exact_mod_cast he
    linarith

theorem all_small_avoidance_iff (P : ℝ) (D : ℕ) (hD : 0 < D) (hDP : (D:ℝ)<P)
    (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ) (hd0 : 0 < d0)
    (hsupport : ∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0)
    (p : ℕ) (hp : p.Prime) (hPp : P ≤ (p:ℝ)) (hint : (D:ℤ)∣A+B*p) :
    (∀ t∈smallPrimeSet P,(actualN D A B p:ZMod t)≠residue t) ↔
      (∀ t∈D.primeFactors,(actualN D A B p:ZMod t)≠residue t) ∧
      (∀ t∈restrictedPrimes P D A residue d0,(p:ZMod t)≠forbiddenClass D A B residue t) := by
  constructor
  · intro h
    constructor
    · intro t ht
      have htP : (t:ℝ)<P := (show (t:ℝ) ≤ D by exact_mod_cast Nat.le_of_dvd hD (Nat.dvd_of_mem_primeFactors ht)).trans_lt hDP
      exact h t ((mem_smallPrimeSet P t).mpr ⟨Nat.prime_of_mem_primeFactors ht,htP⟩)
    · intro t ht he
      have htE := (Finset.mem_filter.mp ht).1
      obtain ⟨htS,htD,_⟩ := Finset.mem_filter.mp htE
      have htP := ((mem_smallPrimeSet P t).mp htS).1
      have hBunit := restricted_coefficient_unit P D A B residue d0 hprofile t ht
      exact h t htS ((actual_bad_iff D t A B residue p htP htD hint).mpr
        ((mul_forbidden_iff D t A B residue p hBunit).mpr he))
  · rintro ⟨hDen,hRest⟩ t htS hbad
    have htp := ((mem_smallPrimeSet P t).mp htS).1
    by_cases htD : t∣D
    · exact hDen t (Nat.mem_primeFactors.mpr ⟨htp,htD,hD.ne'⟩) hbad
    have hmul := (actual_bad_iff D t A B residue p htp htD hint).mp hbad
    by_cases hrhs : (D:ZMod t)*(residue t)-A=0
    · have hnot : ¬t∣d0 := by
        intro hd
        have hE := hsupport t (Nat.mem_primeFactors.mpr ⟨htp,hd,hd0.ne'⟩)
        exact (Finset.mem_filter.mp hE).2.2 hrhs
      have hBunit := coefficient_unit_of_not_dvd htp B (hprofile t htS) hnot
      let _ : Fact t.Prime := ⟨htp⟩
      have hp0 := prime_cast_ne_zero_of_large P p t hp hPp htS
      have hB0 : (B:ZMod t)≠0 := isUnit_iff_ne_zero.mp hBunit
      rw [hrhs] at hmul
      exact mul_ne_zero hB0 hp0 hmul
    · have htE : t∈unalignedPrimes P D A residue := Finset.mem_filter.mpr ⟨htS,htD,hrhs⟩
      by_cases htd : t∣d0
      · have hB0 := coefficient_cast_zero (hprofile t htS) htd
        rw [hB0,zero_mul] at hmul
        exact hrhs hmul.symm
      · have htR : t∈restrictedPrimes P D A residue d0 := Finset.mem_filter.mpr ⟨htE,htd⟩
        have hBunit := restricted_coefficient_unit P D A B residue d0 hprofile t htR
        exact hRest t htR ((mul_forbidden_iff D t A B residue p hBunit).mp hmul)

theorem local_survivor_conditions (P : ℝ) (D : ℕ) (hD : 0 < D) (hDP : (D:ℝ)<P)
    (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ) (hd0 : 0 < d0)
    (hsupport : ∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0)
    (p : ℕ) (hp : p.Prime) (hPp : P ≤ (p:ℝ)) :
    ((D:ℤ)∣A+B*p ∧ ∀ t∈smallPrimeSet P,(actualN D A B p:ZMod t)≠residue t) ↔
      (p%(D*radical D)∈actualClasses D A B residue ∧
        ∀ t∈restrictedPrimes P D A residue d0,(p:ZMod t)≠forbiddenClass D A B residue t) := by
  rw [mem_actualClasses_mod_iff D hD A B residue p]
  constructor
  · rintro ⟨hint,h⟩
    have hh := (all_small_avoidance_iff P D hD hDP A B residue d0 hd0 hsupport hprofile p hp hPp hint).mp h
    exact ⟨⟨hint,hh.1⟩,hh.2⟩
  · rintro ⟨⟨hint,hDen⟩,hRest⟩
    exact ⟨hint,(all_small_avoidance_iff P D hD hDP A B residue d0 hd0 hsupport hprofile p hp hPp hint).mpr ⟨hDen,hRest⟩⟩

noncomputable def actualSurvivorPrimes (P R V : ℝ) (D : ℕ) (A B : ℤ) (residue : ℕ → ℤ) : Finset ℕ :=
  (intervalPrimes R V 1 0).filter (fun p => (D:ℤ)∣A+B*p ∧
    ∀ t∈smallPrimeSet P,(actualN D A B p:ZMod t)≠residue t)

theorem actualSurvivorPrimes_eq_sieve (P R V : ℝ) (hPR : P ≤ R)
    (D : ℕ) (hD : 0 < D) (hDP : (D:ℝ)<P) (A B : ℤ) (residue : ℕ → ℤ)
    (d0 : ℕ) (hd0 : 0 < d0)
    (hsupport : ∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0) :
    actualSurvivorPrimes P R V D A B residue=
      survivorPrimes R V (D*radical D) (restrictedPrimes P D A residue d0)
        (actualClasses D A B residue) (forbiddenClass D A B residue) := by
  ext p
  simp only [actualSurvivorPrimes,survivorPrimes,basePrimes,Finset.mem_filter]
  by_cases hp : p∈intervalPrimes R V 1 0
  · simp only [hp,true_and]
    have h := (mem_intervalPrimes R V 1 0 p).mp hp
    exact local_survivor_conditions P D hD hDP A B residue d0 hd0 hsupport hprofile p h.1 (hPR.trans h.2.1.le)
  · simp only [hp,false_and]

end ErdosStoppedTagSieve


end Erdos970

end OAI
