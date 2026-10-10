import OAI.GroupTheory.UniversalGroup.Benign

namespace OAI

universe u v w x

namespace Higman.HNN
open Monoid Coprod Multiplicative
variable {G : Type u} [Group G] {A B : Subgroup G} (φ : A ≃* B)

def relation (a : A) : G ∗ Multiplicative ℤ :=
  (inr (ofAdd 1) * inl (a : G)) * (inl (φ a : G) * inr (ofAdd 1))⁻¹

theorem con_finitelyNormallyGenerated (hA : A.FG) :
    (HNNExtension.con G A B φ).subgroup.IsFinitelyNormallyGenerated := by
  classical
  have : Group.FG A := (Group.fg_iff_subgroup_fg A).mpr hA
  obtain ⟨S,hS⟩ := (Group.FG.out : (⊤ : Subgroup A).FG)
  let C := HNNExtension.con G A B φ
  let N : Subgroup (G ∗ Multiplicative ℤ) :=
    Subgroup.normalClosure (relation φ '' (S : Set A))
  let Q := (G ∗ Multiplicative ℤ) ⧸ N
  let q : G ∗ Multiplicative ℤ →* Q := QuotientGroup.mk' N
  let f : G →* Q := q.comp inl
  let t : Q := q (inr (ofAdd 1))
  let f₀ : A →* Q := (MulAut.conj t).toMonoidHom.comp (f.comp A.subtype)
  let f₁ : A →* Q := f.comp (B.subtype.comp φ.toMonoidHom)
  have hgen : (S : Set A) ⊆ f₀.eqLocus f₁ := by
    intro a ha
    have hr : q (relation φ a) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨a,ha,rfl⟩)
    have he : t * f a = f (φ a) * t := mul_inv_eq_one.mp hr
    change t * f a * t⁻¹ = f (φ a)
    rw [he,mul_inv_cancel_right]
  have heq : f₀ = f₁ := by
    apply MonoidHom.ext
    intro a
    have hh : (⊤ : Subgroup A) ≤ f₀.eqLocus f₁ := by
      rw [← hS]
      exact (Subgroup.closure_le _).mpr hgen
    exact hh (Subgroup.mem_top a)
  have hC : C ≤ Con.ker q := by
    apply Con.conGen_le.mpr
    rintro _ _ ⟨a,rfl,rfl⟩
    change t * f a = f (φ a) * t
    have he : t * f a * t⁻¹ = f (φ a) := DFunLike.congr_fun heq a
    rw [← he, inv_mul_cancel_right]
  refine ⟨relation φ '' (S : Set A), S.finite_toSet.image _, ?_⟩
  change N = C.subgroup
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨a,_,rfl⟩
    have hr : C (inr (ofAdd 1) * inl (a : G))
        (inl (φ a : G) * inr (ofAdd 1)) := ConGen.Rel.of _ _ ⟨a,rfl,rfl⟩
    change C (relation φ a) 1
    have hh := C.mul hr (C.refl (inl (φ a : G) * inr (ofAdd 1))⁻¹)
    simpa only [relation, mul_inv_cancel] using hh
  · intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    exact (hC hx).trans (map_one q)

theorem finitelyPresented [Group.IsFinitelyPresented G] (hA : A.FG) :
    Group.IsFinitelyPresented (HNNExtension G A B φ) := by
  let C := HNNExtension.con G A B φ
  have hfp := Group.IsFinitelyPresented.quotient C.subgroup
    (con_finitelyNormallyGenerated φ hA)
  change Group.IsFinitelyPresented C.Quotient
  rw [← QuotientGroup.con_subgroup C]
  exact hfp

end Higman.HNN

namespace Higman

structure PartialIso (G : Type u) [Group G] where
  source : Subgroup G
  target : Subgroup G
  equiv : source ≃* target

namespace PartialIso
variable {G : Type u} [Group G] {K : Type u} [Group K]

noncomputable def map (p : PartialIso G) (i : G →* K) (hi : Function.Injective i) :
    PartialIso K where
  source := p.source.map i
  target := p.target.map i
  equiv := ((p.source.equivMapOfInjective i hi).symm.trans p.equiv).trans
    (p.target.equivMapOfInjective i hi)

@[simp] theorem map_equiv (p : PartialIso G) (i : G →* K) (hi : Function.Injective i)
    (a : p.source) :
    ((p.map i hi).equiv (p.source.equivMapOfInjective i hi a) : K) = i (p.equiv a) := by
  change i (p.equiv ((p.source.equivMapOfInjective i hi).symm
    (p.source.equivMapOfInjective i hi a))) = i (p.equiv a)
  rw [MulEquiv.symm_apply_apply]

def Invariant (p : PartialIso G) (R : Subgroup G) : Prop :=
  ∀ a : p.source, (p.equiv a : G) ∈ R ↔ (a : G) ∈ R

theorem invariant_map (p : PartialIso G) (i : G →* K) (hi : Function.Injective i)
    (R : Subgroup G) (S : Subgroup K) (he : S.comap i = R) (h : p.Invariant R) :
    (p.map i hi).Invariant S := by
  intro a
  obtain ⟨b,rfl⟩ := (p.source.equivMapOfInjective i hi).surjective a
  rw [map_equiv]
  change (p.equiv b : G) ∈ S.comap i ↔ (b : G) ∈ S.comap i
  rw [he]
  exact h b

end PartialIso
namespace FiniteHNN
variable {G : Type u} [Group G] [Group.IsFinitelyPresented G]

theorem realization (ps : List (PartialIso G))
    (hfg : ∀ p ∈ ps, p.source.FG) (R : Subgroup G)
    (hinv : ∀ p ∈ ps, p.Invariant R) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : G →* K), Function.Injective i ∧
      ∃ T : Set K, T.Finite ∧
        (Subgroup.closure (i '' (R : Set G) ∪ T)).comap i = R ∧
        ∀ p ∈ ps, ∃ t ∈ T, ∀ a : p.source,
          i (p.equiv a) = t * i a * t⁻¹ := by
  induction ps with
  | nil =>
    refine ⟨G,inferInstance,inferInstance,MonoidHom.id G,Function.injective_id,
      ∅,Set.finite_empty,?_,?_⟩
    · simp
    · simp
  | cons p ps ih =>
    obtain ⟨K,_,_,i,hi,T,hT,hR,hrel⟩ := ih
      (fun q hq ↦ hfg q (List.mem_cons_of_mem p hq))
      (fun q hq ↦ hinv q (List.mem_cons_of_mem p hq))
    let q := p.map i hi
    let E := HNNExtension K q.source q.target q.equiv
    let j : K →* E := HNNExtension.of
    let i' := j.comp i
    let C := Subgroup.closure (i '' (R : Set G) ∪ T)
    let T' : Set E := j '' T ∪ {HNNExtension.t}
    have hqfg : q.source.FG := by
      obtain ⟨S,hS⟩ := hfg p (List.mem_cons_self)
      refine (Subgroup.fg_iff _).mpr ⟨i '' (S : Set G),?_,S.finite_toSet.image i⟩
      rw [← MonoidHom.map_closure,hS]
      rfl
    have hCinv : q.Invariant C :=
      p.invariant_map i hi R C hR (hinv p (List.mem_cons_self))
    have hC : (Subgroup.closure (j '' (C : Set K) ∪ {HNNExtension.t})).comap j = C :=
      HNNSubgroup.closure_comap_of q.equiv C hCinv
    have hclosure : Subgroup.closure (i' '' (R : Set G) ∪ T') =
        Subgroup.closure (j '' (C : Set K) ∪ {HNNExtension.t}) := by
      conv_rhs => rw [Subgroup.closure_union,← MonoidHom.map_closure j (C : Set K),Subgroup.closure_eq]
      change Subgroup.closure (i' '' (R : Set G) ∪ T') =
        C.map j ⊔ Subgroup.closure {HNNExtension.t}
      rw [show C.map j = Subgroup.closure (j '' (i '' (R : Set G) ∪ T)) from
        MonoidHom.map_closure j _]
      rw [← Subgroup.closure_union]
      congr 1
      simp only [T',Set.image_union,Set.image_image,Set.union_assoc,i',MonoidHom.coe_comp]
      rfl
    refine ⟨E,inferInstance,HNN.finitelyPresented q.equiv hqfg,i',
      (HNNExtension.of_injective (φ := q.equiv)).comp hi,T',
      (hT.image j).union (Set.finite_singleton _),?_,?_⟩
    · rw [hclosure]
      change ((Subgroup.closure (j '' (C : Set K) ∪ {HNNExtension.t})).comap j).comap i = R
      rw [hC]
      exact hR
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · refine ⟨HNNExtension.t,Or.inr rfl,?_⟩
        intro b
        have he := HNNExtension.equiv_eq_conj (φ := q.equiv)
          (a.source.equivMapOfInjective i hi b)
        simpa only [q,PartialIso.map_equiv,i',j,MonoidHom.comp_apply,
          Subgroup.coe_equivMapOfInjective_apply] using he
      · obtain ⟨t,ht,he⟩ := hrel a ha
        refine ⟨j t,Or.inl ⟨t,ht,rfl⟩,?_⟩
        intro b
        simpa only [i',MonoidHom.comp_apply,map_mul,map_inv] using congrArg j (he b)

end FiniteHNN

namespace PartialIso
variable {G : Type u} [Group G]

theorem invariant_sInf (p : PartialIso G) (C : Set (Subgroup G))
    (hC : ∀ S ∈ C, p.Invariant S) : p.Invariant (sInf C) := by
  intro a
  simp only [Subgroup.mem_sInf]
  exact forall₂_congr fun S hS ↦ hC S hS a

end PartialIso
namespace Orbit
variable {G : Type u} [Group G]

def subgroup (ps : List (PartialIso G)) (S : Set G) : Subgroup G :=
  sInf {R | S ⊆ R ∧ ∀ p ∈ ps, p.Invariant R}

theorem subset (ps : List (PartialIso G)) (S : Set G) :
    S ⊆ subgroup ps S := by
  intro x hx
  exact Subgroup.mem_sInf.mpr (fun R hR ↦ hR.1 hx)

theorem invariant (ps : List (PartialIso G)) (S : Set G) (p : PartialIso G)
    (hp : p ∈ ps) : p.Invariant (subgroup ps S) :=
  p.invariant_sInf _ (fun _ hR ↦ hR.2 p hp)

theorem minimal (ps : List (PartialIso G)) (S : Set G) (R : Subgroup G)
    (hS : S ⊆ R) (hR : ∀ p ∈ ps, p.Invariant R) : subgroup ps S ≤ R :=
  sInf_le ⟨hS,hR⟩

theorem benign [Group.IsFinitelyPresented G] (ps : List (PartialIso G))
    (hfg : ∀ p ∈ ps, p.source.FG) (S : Set G) (hS : S.Finite) :
    IsBenign (subgroup ps S) := by
  let R := subgroup ps S
  obtain ⟨K,_,_,i,hi,T,hT,hR,hrel⟩ := FiniteHNN.realization ps hfg R
    (fun p hp ↦ invariant ps S p hp)
  let B := Subgroup.closure (i '' S ∪ T)
  have hB : B.FG := (Subgroup.fg_iff _).mpr ⟨i '' S ∪ T, rfl, (hS.image i).union hT⟩
  refine ⟨K,inferInstance,inferInstance,i,hi,B,hB,?_⟩
  apply le_antisymm
  · calc
      B.comap i ≤ (Subgroup.closure (i '' (R : Set G) ∪ T)).comap i :=
        Subgroup.comap_mono (Subgroup.closure_mono
          (Set.union_subset_union_left _ (Set.image_mono (subset ps S))))
      _ = R := hR
  · apply minimal ps S (B.comap i)
    · intro x hx
      exact Subgroup.subset_closure (Or.inl ⟨x,hx,rfl⟩)
    · intro p hp a
      obtain ⟨t,ht,he⟩ := hrel p hp
      have htB : t ∈ B := Subgroup.subset_closure (Or.inr ht)
      change i (p.equiv a) ∈ B ↔ i a ∈ B
      rw [he a]
      constructor
      · intro ha
        have hh := B.mul_mem (B.mul_mem (B.inv_mem htB) ha) htB
        simpa only [inv_mul_cancel_left,mul_assoc,inv_mul_cancel,mul_one] using hh
      · intro ha
        exact B.mul_mem (B.mul_mem htB ha) (B.inv_mem htB)

end Orbit
end Higman

end OAI
