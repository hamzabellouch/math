import Mathlib
import OAI.Algebra.GroupRing.RelationArea
import OAI.Algebra.GroupRing.CellNorm

namespace OAI



section
namespace TorsionFreeZeroDivisors.RelationTorsion
open scoped Classical BigOperators
open AlgebraicPictures CellModule RelationArea
noncomputable section
variable {A I : Type} (rel : I→List (A×Bool))
lemma fox_pow (w : FreeGroup A) (n : ℕ) : fox (q rel) (w^n)=
    ∑k∈Finset.range n,translate (q rel w^k) (fox (q rel) w) := by
  induction n with
  | zero=>simp [fox_one]
  | succ n ih=>rw [pow_succ,fox_mul,ih,Finset.sum_range_succ,map_pow]
local instance zpowersCommGroup (g : G rel) : CommGroup (Subgroup.zpowers g) := IsCyclic.commGroup
lemma norm_zpowers {J : Type} (g : G rel) (hg : IsOfFinOrder g)
    [Fintype (Subgroup.zpowers g)] (x : CellModule.Module (G rel) J) :
    CellNorm.norm (Subgroup.zpowers g).subtype x=
      ∑k∈Finset.range (orderOf g),translate (g^k) x := by
  rw [CellNorm.norm,←(finEquivZPowers hg).sum_comp]
  simp only [finEquivZPowers_apply,Subgroup.subtype_apply]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ=>translate (g^k) x) (orderOf g)

/-- The translated integral relation-area identity rules out actual finite-order
quotient elements, via the exact cyclic norm complex on free integral modules. -/
theorem torsion_free
    (hz : ∀ts : List (Term (A:=A) (I:=I)),FreeGroup.mk (word rel ts)=1→total rel ts=0) :
    ∀ (g : G rel) (n : ℕ), 0 < n → g ^ n = 1 → g = 1 := by
  intro g n hn hgn
  by_contra hgne
  have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hgn⟩
  let H := Subgroup.zpowers g
  let : Fintype H := Fintype.ofEquiv (Fin (orderOf g)) (finEquivZPowers hfin)
  let : CommGroup H := IsCyclic.commGroup
  let a : H := ⟨g,Subgroup.mem_zpowers g⟩
  have ha : ∀x : H,x∈Subgroup.zpowers a := by
    intro x
    obtain ⟨z,hz⟩ := x.property
    exact ⟨z,Subtype.ext hz⟩
  have hcard : 1<Fintype.card H := by
    rw [Fintype.card_congr (finEquivZPowers hfin).symm,Fintype.card_fin]
    have hp := hfin.orderOf_pos
    have he : orderOf g≠1 := fun h=>hgne (orderOf_eq_one_iff.mp h)
    omega
  obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (N rel) g
  change q rel w=g at hw
  let r : N rel := ⟨w^orderOf g,PresentedGroup.mk_eq_one_iff.mp (by rw [map_pow,hw,pow_orderOf_eq_one])⟩
  have hr : conjugate rel w r=r := by
    apply Subtype.ext
    change w*w^orderOf g*w⁻¹=w^orderOf g
    rw [←pow_succ',pow_succ,mul_inv_cancel_right]
  have hinv : translate g (area rel r)=area rel r := by
    rw [←hw,←area_conjugate rel hz,hr]
  obtain ⟨E,hE⟩ := CellNorm.invariant_norm H.subtype Subtype.val_injective a ha (area rel r) hinv
  have hnorm : CellNorm.norm H.subtype (fox (q rel) w-d₂ rel E)=0 := by
    rw [CellNorm.norm_sub,←CellNorm.equivariance H.subtype A (d₂ rel) (d₂_translate rel),hE,d₂_area]
    change CellNorm.norm H.subtype (fox (q rel) w)-fox (q rel) (w^orderOf g)=0
    rw [norm_zpowers rel g hfin,fox_pow,hw,sub_self]
  obtain ⟨F,hF⟩ := CellNorm.kernel_norm H.subtype Subtype.val_injective a ha _ hnorm
  have hbd : translate g (boundary (q rel) F)-boundary (q rel) F=
      Finsupp.single (g,PUnit.unit) 1-Finsupp.single (1,PUnit.unit) 1 := by
    change translate g F-F=fox (q rel) w-d₂ rel E at hF
    have h := congrArg (boundary (q rel)) hF
    simpa only [map_sub,boundary_translate,boundary_fox,hw,boundary_d₂,sub_zero] using h
  let x : CellModule.Module (G rel) PUnit := Finsupp.single (1,PUnit.unit) 1-boundary (q rel) F
  have hx : translate g x=x := by
    dsimp only [x]
    rw [map_sub,translate_single,mul_one]
    apply sub_eq_sub_iff_add_eq_add.mpr
    have he := sub_eq_sub_iff_add_eq_add.mp hbd
    simpa only [add_comm] using he.symm
  have hdvd := CellNorm.invariant_augmentation H.subtype Subtype.val_injective a ha x hx
  have haug : CellNorm.augmentation x=1 := by
    dsimp only [x]
    rw [map_sub,CellNorm.augmentation_single,CellNorm.augmentation_boundary,sub_zero]
  rw [haug] at hdvd
  have hc : Fintype.card H∣1 := Int.natCast_dvd_natCast.mp hdvd
  have := Nat.eq_one_of_dvd_one hc
  omega
end
end TorsionFreeZeroDivisors.RelationTorsion

end


end OAI
