import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.CongruenceTorsion

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

lemma gl_eq_one_of_prime_to_residue_order [IsDomain R] [IsNoetherianRing R]
    (I : Ideal R) [I.IsMaximal] (g : GL n R) (q : ℕ) (hq : (q:R)∉I)
    (hpow : g^q=1) (hmod : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g=1) :
    g=1 := by
  apply Units.ext
  apply eq_one_of_prime_to_residue_order I g.val q hq
  · exact congrArg Units.val hpow
  · intro i j
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := congrArg (fun M : GL n (R ⧸ I) => M i j) hmod
    rw [Matrix.GeneralLinearGroup.map_apply] at he
    have he1 : (Ideal.Quotient.mk I) ((1 : Matrix n n R) i j)=(1 : Matrix n n (R ⧸ I)) i j := by
      by_cases h : i=j <;> simp [Matrix.one_apply,h]
    change (Ideal.Quotient.mk I) (g.val i j-(1 : Matrix n n R) i j)=0
    rw [map_sub,he1,he]
    simp

lemma eq_one_of_no_prime_order {G : Type*} [Group G]
    (h : ∀ (g : G) (p : ℕ), p.Prime → g^p=1 → g=1)
    (g : G) (hg : IsOfFinOrder g) : g=1 := by
  by_contra hne
  have ho : orderOf g≠1 := by simpa using hne
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd ho
  let y := g^(orderOf g/p)
  have hyord : orderOf y=p := orderOf_pow_orderOf_div hg.orderOf_pos.ne' hpd
  have hy : y^p=1 := hyord ▸ pow_orderOf_eq_one y
  have he := h y p hp hy
  have he1 : p=1 := by simpa [he] using hyord.symm
  exact hp.ne_one he1

theorem exists_finiteIndex_no_finite_order [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] :
    ∃ H : Subgroup (GL n R), H.Normal ∧ H.FiniteIndex ∧
      ∀ h : H, IsOfFinOrder h → h=1 := by
  let : IsJacobsonRing ℤ := int_isJacobsonRing
  let : IsJacobsonRing R := isJacobsonRing_of_finiteType (A:=ℤ) (B:=R)
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let : I.IsMaximal := hI
  let := Ideal.Quotient.field I
  let : Finite (R ⧸ I) := finite_residue_of_finiteType_int I
  let p := ringChar (R ⧸ I)
  have hp : p.Prime := CharP.char_is_prime (R ⧸ I) p
  obtain ⟨J,hJ,hpJ⟩ := exists_maximal_avoiding (p:R) (Nat.cast_ne_zero.mpr hp.ne_zero)
  let : J.IsMaximal := hJ
  let : Finite (R ⧸ J) := finite_residue_of_finiteType_int J
  let f := (Matrix.GeneralLinearGroup.map (n:=n) (Ideal.Quotient.mk I)).prod
    (Matrix.GeneralLinearGroup.map (n:=n) (Ideal.Quotient.mk J))
  let H := f.ker
  refine ⟨H,inferInstance,Subgroup.finiteIndex_ker f,?_⟩
  apply eq_one_of_no_prime_order
  intro g q hq hpow
  have hmods := g.property
  change (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g.val,
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) g.val)=(1,1) at hmods
  apply Subtype.ext
  change g.val=1
  have hpow' : g.val^q=1 := congrArg Subtype.val hpow
  by_cases hqp : q=p
  · subst q
    exact gl_eq_one_of_prime_to_residue_order J g.val p hpJ hpow' (congrArg Prod.snd hmods)
  · have hqI : (q:R)∉I := by
      intro hm
      have hc : (q:R ⧸ I)=0 := by simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hm
      have hd : p∣q := (CharP.cast_eq_zero_iff (R ⧸ I) p q).mp hc
      rcases (Nat.dvd_prime hq).mp hd with he|he
      · exact hp.ne_one he
      · exact hqp he.symm
    exact gl_eq_one_of_prime_to_residue_order I g.val q hqI hpow' (congrArg Prod.fst hmods)

end CriticalPercolation.LinearGrowth
end
end

end OAI
