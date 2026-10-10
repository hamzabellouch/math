import OAI.NumberTheory.Jacobsthal.Estimates.ActualUnitClasses

namespace OAI

namespace Erdos970


namespace ErdosStoppedTagSieve
open ErdosUnitLifts

lemma integral_mod_lift_iff (D : ℕ) (A B : ℤ) (p : ℕ) :
    (D:ℤ) ∣ A+B*(p%(D*radical D):ℕ) ↔ (D:ℤ) ∣ A+B*p := by
  have hp : ((p%(D*radical D):ℕ):ZMod D)=(p:ZMod D) := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    exact Nat.mod_mod_of_dvd p (dvd_mul_right D (radical D))
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast]
  rw [hp]

lemma actualN_mod_lift (D : ℕ) (hD : 0 < D) (A B : ℤ) (p t : ℕ)
    (ht : t∈D.primeFactors) :
    (actualN D A B (p%(D*radical D)):ZMod t)=(actualN D A B p:ZMod t) := by
  have he : p%(D*radical D)+D*(radical D*(p/(D*radical D)))=p := by
    simpa only [Nat.mul_assoc] using Nat.mod_add_div p (D*radical D)
  have hn := actualN_lift D hD A B (p%(D*radical D)) (radical D*(p/(D*radical D)))
  rw [he] at hn
  have htr : t∣radical D := Finset.dvd_prod_of_mem (fun t => t) ht
  have hz : (radical D:ZMod t)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr htr
  rw [hn]
  push_cast
  simp [hz]

theorem mem_actualClasses_mod_iff (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ) (p : ℕ) :
    p%(D*radical D)∈actualClasses D A B a ↔
      (D:ℤ)∣A+B*p ∧ ∀ t∈D.primeFactors,(actualN D A B p:ZMod t)≠a t := by
  have hQ : 0 < D*radical D := Nat.mul_pos hD (radical_pos D)
  simp only [actualClasses,Finset.mem_filter,Finset.mem_range,Nat.mod_lt p hQ,true_and,
    integral_mod_lift_iff]
  apply and_congr_right
  intro _h
  constructor <;> intro h t ht
  · simpa only [actualN_mod_lift D hD A B p t ht] using h t ht
  · simpa only [actualN_mod_lift D hD A B p t ht] using h t ht

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve
open ErdosUnitLifts
attribute [local instance] Classical.propDecidable

noncomputable def smallPrimeSet (P : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊P⌋₊).filter (fun t => (t:ℝ)<P)

lemma mem_smallPrimeSet (P : ℝ) (t : ℕ) : t∈smallPrimeSet P ↔ t.Prime ∧ (t:ℝ)<P := by
  simp only [smallPrimeSet,Finset.mem_filter,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_,ht⟩,hP⟩
    exact ⟨ht,hP⟩
  · rintro ⟨ht,hP⟩
    have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
    exact ⟨⟨(Nat.le_floor_iff (by linarith)).mpr hP.le,ht⟩,hP⟩

noncomputable def unalignedPrimes (P : ℝ) (D : ℕ) (A : ℤ) (residue : ℕ → ℤ) : Finset ℕ :=
  (smallPrimeSet P).filter (fun t => ¬t∣D ∧ (D:ZMod t)*(residue t)-A≠0)
noncomputable def restrictedPrimes (P : ℝ) (D : ℕ) (A : ℤ) (residue : ℕ → ℤ) (d0 : ℕ) : Finset ℕ :=
  (unalignedPrimes P D A residue).filter (fun t => ¬t∣d0)
noncomputable def forbiddenClass (D : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (t : ℕ) : ZMod t :=
  (B:ZMod t)⁻¹*((D:ZMod t)*(residue t)-A)

lemma coefficient_cast_zero {t d0 : ℕ} {B : ℤ}
    (hprofile : t∣B.natAbs ↔ t∣d0) (ht : t∣d0) : (B:ZMod t)=0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd B t).mpr (Int.natCast_dvd.mpr (hprofile.mpr ht))

lemma coefficient_unit_of_not_dvd {t d0 : ℕ} (ht : t.Prime) (B : ℤ)
    (hprofile : t∣B.natAbs ↔ t∣d0) (hnot : ¬t∣d0) : IsUnit (B:ZMod t) :=
  intCast_isUnit_of_natAbs_coprime t B
    ((ht.coprime_iff_not_dvd.mpr (fun hd => hnot (hprofile.mp hd))).symm)

theorem signed_coefficient_profile (P : ℝ) (q d0 ell : ℕ) (m : ℤ)
    (hq : ∀ t∈smallPrimeSet P,q.Coprime t) (hell : ell.Prime) (hellP : P<(ell:ℝ))
    (hm : m.natAbs=d0*ell) :
    ∀ t∈smallPrimeSet P,t∣((q:ℤ)*m).natAbs ↔ t∣d0 := by
  intro t ht
  obtain ⟨htp,htP⟩ := (mem_smallPrimeSet P t).mp ht
  have htq : ¬t∣q := htp.coprime_iff_not_dvd.mp (hq t ht).symm
  have hte : ¬t∣ell := by
    intro hd
    rcases hell.eq_one_or_self_of_dvd t hd with he | he
    · exact htp.ne_one he
    · have her : (t:ℝ)=ell := by exact_mod_cast he
      linarith
  simp only [Int.natAbs_mul,Int.natAbs_natCast,hm,htp.dvd_mul,htq,hte,false_or,or_false]

theorem denominator_coefficient_coprime (P : ℝ) (D : ℕ) (hD : 0 < D) (hDP : (D:ℝ)<P)
    (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ) (hd0 : 0 < d0)
    (hsupport : ∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0) : B.natAbs.Coprime D := by
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro t htp htD htB
  have htR : (t:ℝ) ≤ D := by exact_mod_cast Nat.le_of_dvd hD htD
  have htS : t∈smallPrimeSet P := (mem_smallPrimeSet P t).mpr ⟨htp,htR.trans_lt hDP⟩
  have htd0 := (hprofile t htS).mp htB
  have he := hsupport t (Nat.mem_primeFactors.mpr ⟨htp,htd0,hd0.ne'⟩)
  exact (Finset.mem_filter.mp he).2.1 htD

lemma restricted_coefficient_unit (P : ℝ) (D : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0)
    (t : ℕ) (ht : t∈restrictedPrimes P D A residue d0) : IsUnit (B:ZMod t) := by
  obtain ⟨htE,htd⟩ := Finset.mem_filter.mp ht
  have htS := (Finset.mem_filter.mp htE).1
  exact coefficient_unit_of_not_dvd ((mem_smallPrimeSet P t).mp htS).1 B (hprofile t htS) htd

lemma forbiddenClass_ne_zero (P : ℝ) (D : ℕ) (A B : ℤ) (residue : ℕ → ℤ) (d0 : ℕ)
    (hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0)
    (t : ℕ) (ht : t∈restrictedPrimes P D A residue d0) : forbiddenClass D A B residue t≠0 := by
  have htE := (Finset.mem_filter.mp ht).1
  obtain ⟨htS,_,hrhs⟩ := Finset.mem_filter.mp htE
  let _ : Fact t.Prime := ⟨((mem_smallPrimeSet P t).mp htS).1⟩
  have hB := restricted_coefficient_unit P D A B residue d0 hprofile t ht
  exact mul_ne_zero (inv_ne_zero (isUnit_iff_ne_zero.mp hB)) hrhs

end ErdosStoppedTagSieve


end Erdos970

end OAI
