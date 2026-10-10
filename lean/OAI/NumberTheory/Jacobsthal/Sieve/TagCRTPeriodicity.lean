import OAI.NumberTheory.Jacobsthal.Primes.TagSmallPrimeData

namespace OAI

namespace Erdos970


namespace ErdosStoppedTagSieve
open scoped BigOperators
attribute [local instance] Classical.decEq

abbrev IntersectionIndex (T : Finset ℕ) := {t // t∈T}
def intersectionModuli (Q : ℕ) (T : Finset ℕ) : Option (IntersectionIndex T) → ℕ
  | none => Q
  | some t => t.val

lemma intersection_moduli_product (Q : ℕ) (T : Finset ℕ) :
    (∏ i,intersectionModuli Q T i)=Q*(∏ t∈T,t) := by
  rw [Fintype.prod_option]
  simp only [intersectionModuli]
  congr 1
  exact Finset.prod_coe_sort T (fun t : ℕ => t)

lemma intersection_moduli_pairwise (Q : ℕ) (T : Finset ℕ)
    (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t) :
    Pairwise (fun i j => Nat.Coprime (intersectionModuli Q T i) (intersectionModuli Q T j)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some t => exact hQT t.val t.property
  | some t =>
    cases j with
    | none => exact (hQT t.val t.property).symm
    | some u =>
      apply (hT t.val t.property).coprime_iff_not_dvd.mpr
      intro hd
      rcases (hT u.val u.property).eq_one_or_self_of_dvd t.val hd with he | he
      · exact (hT t.val t.property).ne_one he
      · exact hij (congrArg Option.some (Subtype.ext he))

noncomputable def baseClasses (Q : ℕ) (A : Finset ℕ) : Finset (ZMod Q) :=
  A.image (fun a : ℕ => (a:ZMod Q))

lemma baseClasses_card (Q : ℕ) (A : Finset ℕ) (hA : ∀ a∈A,a<Q) :
    (baseClasses Q A).card=A.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb he
  have hh := (ZMod.natCast_eq_natCast_iff' a b Q).mp he
  simpa only [Nat.mod_eq_of_lt (hA a ha),Nat.mod_eq_of_lt (hA b hb)] using hh

lemma mem_baseClasses (Q : ℕ) (A : Finset ℕ) (hA : ∀ a∈A,a<Q) (p : ℕ) :
    (p:ZMod Q)∈baseClasses Q A ↔ p%Q∈A := by
  constructor
  · rintro h
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
    have hh := (ZMod.natCast_eq_natCast_iff' a p Q).mp he
    rw [Nat.mod_eq_of_lt (hA a ha)] at hh
    exact hh ▸ ha
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨p%Q,hp,?_⟩
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    exact Nat.mod_mod p Q

noncomputable def intersectionClasses (Q : ℕ) (T : Finset ℕ) (A : Finset ℕ) (rho : (t : ℕ) → ZMod t) :
    (i : Option (IntersectionIndex T)) → Finset (ZMod (intersectionModuli Q T i))
  | none => baseClasses Q A
  | some t => {rho t.val}

noncomputable def intersectionResidues (Q : ℕ) (T : Finset ℕ) (A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t) : Finset ℕ :=
  ErdosUnitLifts.crtNat (intersectionModuli Q T) (intersection_moduli_pairwise Q T hT hQT)
    (intersectionClasses Q T A rho)

lemma intersection_moduli_pos (Q : ℕ) (hQ : 0 < Q) (T : Finset ℕ) (hT : ∀ t∈T,t.Prime) :
    0 < ∏ i,intersectionModuli Q T i := by
  rw [intersection_moduli_product]
  exact Nat.mul_pos hQ (Finset.prod_pos (fun t ht => (hT t ht).pos))

theorem mem_intersectionResidues (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) (p : ℕ) :
    p∈intersectionResidues Q T A rho hT hQT ↔
      p<Q*(∏ t∈T,t) ∧ p%Q∈A ∧ ∀ t∈T,(p:ZMod t)=rho t := by
  rw [intersectionResidues,ErdosUnitLifts.mem_crtNat _ _ _ (intersection_moduli_pos Q hQ T hT),
    intersection_moduli_product]
  apply and_congr_right
  intro _hp
  constructor
  · intro h
    refine ⟨(mem_baseClasses Q A hA p).mp (h none),?_⟩
    intro t ht
    exact Finset.mem_singleton.mp (h (some ⟨t,ht⟩))
  · rintro ⟨hp,h⟩ i
    cases i with
    | none => exact (mem_baseClasses Q A hA p).mpr hp
    | some t => exact Finset.mem_singleton.mpr (h t.val t.property)

theorem intersectionResidues_card (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) : (intersectionResidues Q T A rho hT hQT).card=A.card := by
  rw [intersectionResidues,ErdosUnitLifts.crtNat_card _ _ _ (intersection_moduli_pos Q hQ T hT),Fintype.prod_option]
  change (baseClasses Q A).card*(∏ i : IntersectionIndex T,(intersectionClasses Q T A rho (some i)).card)=A.card
  have hp : (∏ i : IntersectionIndex T,(intersectionClasses Q T A rho (some i)).card)=1 := by
    apply Finset.prod_eq_one
    intro i _hi
    rfl
  rw [hp,mul_one]
  exact baseClasses_card Q A hA

theorem intersectionResidues_reduced (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) (hAc : ∀ a∈A,a.Coprime Q) (hrho : ∀ t∈T,rho t≠0)
    (p : ℕ) (hp : p∈intersectionResidues Q T A rho hT hQT) :
    p<Q*(∏ t∈T,t) ∧ p.Coprime (Q*(∏ t∈T,t)) := by
  obtain ⟨hpM,hpA,hpT⟩ := (mem_intersectionResidues Q hQ T A rho hT hQT hA p).mp hp
  refine ⟨hpM,Nat.coprime_mul_iff_right.mpr ⟨?_,?_⟩⟩
  · have hu : IsUnit ((p%Q:ℕ):ZMod Q) := (ZMod.isUnit_iff_coprime _ _).mpr (hAc _ hpA)
    have he : ((p%Q:ℕ):ZMod Q)=(p:ZMod Q) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (Nat.mod_mod p Q)
    rw [he] at hu
    exact (ZMod.isUnit_iff_coprime _ _).mp hu
  · apply Nat.coprime_prod_right_iff.mpr
    intro t ht
    let _ : Fact t.Prime := ⟨hT t ht⟩
    apply (ZMod.isUnit_iff_coprime _ _).mp
    rw [hpT t ht]
    exact isUnit_iff_ne_zero.mpr (hrho t ht)

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve
open scoped BigOperators

theorem mod_mem_intersectionResidues (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) (p : ℕ) :
    p%(Q*(∏ t∈T,t))∈intersectionResidues Q T A rho hT hQT ↔
      p%Q∈A ∧ ∀ t∈T,(p:ZMod t)=rho t := by
  let M := Q*(∏ t∈T,t)
  have hM : 0 < M := Nat.mul_pos hQ (Finset.prod_pos (fun t ht => (hT t ht).pos))
  have hQd : Q∣M := dvd_mul_right Q _
  have hmodQ : (p%M)%Q=p%Q := Nat.mod_mod_of_dvd p hQd
  have htmod (t : ℕ) (ht : t∈T) : ((p%M:ℕ):ZMod t)=(p:ZMod t) := by
    have htd : t∣M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun t => t) ht) Q
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (Nat.mod_mod_of_dvd p htd)
  rw [mem_intersectionResidues Q hQ T A rho hT hQT hA]
  change p%M<M ∧ (p%M)%Q∈A ∧ (∀ t∈T,((p%M:ℕ):ZMod t)=rho t) ↔ _
  simp only [Nat.mod_lt p hM,true_and,hmodQ]
  apply and_congr_right
  intro _h
  constructor <;> intro h t ht
  · simpa only [htmod t ht] using h t ht
  · simpa only [htmod t ht] using h t ht

lemma totient_prime_product (T : Finset ℕ) (hT : ∀ t∈T,t.Prime) :
    (∏ t∈T,t).totient=∏ t∈T,(t-1) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert t T ht ih =>
    have htp : t.Prime := hT t (Finset.mem_insert_self _ _)
    have hTp : ∀ p∈T,p.Prime := fun p hp => hT p (Finset.mem_insert_of_mem hp)
    have hc : t.Coprime (∏ p∈T,p) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro p hp
      apply htp.coprime_iff_not_dvd.mpr
      intro hd
      rcases (hTp p hp).eq_one_or_self_of_dvd t hd with he | he
      · exact htp.ne_one he
      · exact ht (he.symm ▸ hp)
    rw [Finset.prod_insert ht,Nat.totient_mul hc,Nat.totient_prime htp,ih hTp,Finset.prod_insert ht]

theorem totient_intersection_modulus (Q : ℕ) (T : Finset ℕ)
    (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t) :
    (Q*(∏ t∈T,t)).totient=Q.totient*(∏ t∈T,(t-1)) := by
  rw [Nat.totient_mul (Nat.coprime_prod_right_iff.mpr hQT),totient_prime_product T hT]

end ErdosStoppedTagSieve


end Erdos970

end OAI
