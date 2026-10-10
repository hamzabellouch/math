import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.NormalClosureGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative commutatorElement

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A]

omit [DecidableEq A] in
lemma isMulCommutative_of_generators (S : Set A) (hgen : Subgroup.closure S=⊤)
    (hcomm : ∀ x∈S, ∀ y∈S, x*y=y*x) : IsMulCommutative A := by
  have hc := Subgroup.isMulCommutative_closure
    (fun left hleft right hright _ => hcomm left hleft right hright)
  rw [hgen] at hc
  let _ := hc
  exact ⟨⟨fun x y => congrArg Subtype.val
    (mul_comm' (⟨x,Subgroup.mem_top x⟩ : (⊤ : Subgroup A))
      (⟨y,Subgroup.mem_top y⟩ : (⊤ : Subgroup A)))⟩⟩

lemma commutator_eq_normalClosure_generators (S : Finset A)
    (hgen : Subgroup.closure (S : Set A)=⊤) :
    commutator A = Subgroup.normalClosure
      (((S.product S).image (fun p : A×A => ⁅p.1,p.2⁆)) : Set A) := by
  let F := (S.product S).image (fun p : A×A => ⁅p.1,p.2⁆)
  let N := Subgroup.normalClosure (F : Set A)
  change commutator A=N
  apply le_antisymm
  · apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    let q := QuotientGroup.mk' N
    apply isMulCommutative_of_generators (q '' (S : Set A))
    · rw [←MonoidHom.map_closure,hgen,←MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      apply (QuotientGroup.eq_one_iff ⁅x,y⁆).mpr
      apply Subgroup.subset_normalClosure
      exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_image.mp hx
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)

theorem HasPolynomialDegree.commutator_fg {d : ℕ} (h : HasPolynomialDegree A d) :
    (commutator A).FG := by
  obtain ⟨S,h1,hsym,hgen,hg⟩ := (hasPolynomialDegree_iff d).mp h
  rw [commutator_eq_normalClosure_generators S hgen]
  exact normalClosure_fg_of_sparse_growth S _ h1 hsym hgen d hg

omit [DecidableEq A] in
lemma subgroup_fg_map {H : Subgroup A} (hH : H.FG) (f : A →* B) : (H.map f).FG := by
  classical
  obtain ⟨S,hS⟩ := hH
  refine ⟨S.image f,?_⟩
  rw [Finset.coe_image,←MonoidHom.map_closure,hS]

theorem HasPolynomialDegree.derivedSeries_fg {d : ℕ} (h : HasPolynomialDegree A d)
    (n : ℕ) : (derivedSeries A n).FG := by
  induction n with
  | zero => exact h.fg.out
  | succ n ih =>
    let H := derivedSeries A n
    let _ : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr ih
    have hH : HasPolynomialDegree H d := h.of_injective H.subtype Subtype.val_injective
    have hc := subgroup_fg_map hH.commutator_fg H.subtype
    rw [Subgroup.map_subtype_commutator] at hc
    exact hc

omit [DecidableEq A] in
lemma finite_of_fg_torsion_finite_commutator [Group.FG A]
    (ht : IsMulTorsion A) [Finite (commutator A)] : Finite A := by
  let N := commutator A
  let _ : IsMulCommutative (A ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let _ : Finite (A ⧸ N) := CommGroup.finite_of_fg_isMulTorsion _
    (IsMulTorsion.of_surjective (QuotientGroup.mk'_surjective N) ht)
  exact Finite.of_subgroup_quotient N

omit [DecidableEq A] in
lemma map_derivedSeries_commutator (n : ℕ) :
    (derivedSeries (commutator A) n).map (commutator A).subtype =
      derivedSeries A (n+1) := by
  induction n with
  | zero =>
    change (⊤ : Subgroup (commutator A)).map (commutator A).subtype=commutator A
    rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
  | succ n ih =>
    change (⁅derivedSeries (commutator A) n,derivedSeries (commutator A) n⁆).map _=_
    rw [Subgroup.map_commutator,ih]
    rfl

theorem finite_of_torsion_derivedSeries_eq_bot (n : ℕ) :
    ∀ (A : Type*) [Group A] [DecidableEq A], ∀ d : ℕ,
      HasPolynomialDegree A d → IsMulTorsion A → derivedSeries A n=⊥ → Finite A := by
  induction n with
  | zero =>
    intro A _ _ d hg ht hz
    have hsub : Subsingleton A := by
      constructor
      intro x y
      have hx : x=1 := by
        have hm : x∈derivedSeries A 0 := Subgroup.mem_top x
        simpa only [hz,Subgroup.mem_bot] using hm
      have hy : y=1 := by
        have hm : y∈derivedSeries A 0 := Subgroup.mem_top y
        simpa only [hz,Subgroup.mem_bot] using hm
      exact hx.trans hy.symm
    exact Finite.of_subsingleton
  | succ n ih =>
    intro A _ _ d hg ht hz
    let _ := hg.fg
    let H := commutator A
    let _ : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hg.commutator_fg
    have hH : HasPolynomialDegree H d := hg.of_injective H.subtype Subtype.val_injective
    have htH := ht.subgroup H
    have hzH : derivedSeries H n=⊥ := by
      apply Subgroup.map_injective (f := H.subtype) Subtype.val_injective
      rw [Subgroup.map_bot,map_derivedSeries_commutator,hz]
    let _ : Finite H := ih H d hH htH hzH
    exact finite_of_fg_torsion_finite_commutator ht

omit [DecidableEq A] in
theorem finite_of_torsion_solvable_sparse_growth {d : ℕ} (hg : HasPolynomialDegree A d)
    (ht : IsMulTorsion A) [Group.IsSolvable A] : Finite A := by
  classical
  obtain ⟨n,hn⟩ := Group.IsSolvable.solvable (G := A)
  exact finite_of_torsion_derivedSeries_eq_bot n A d hg ht hn

end CriticalPercolation.SparseGrowth
end
end

end OAI
