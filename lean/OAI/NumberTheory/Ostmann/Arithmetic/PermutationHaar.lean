import OAI.NumberTheory.Ostmann.Arithmetic.BipartiteHaar
import OAI.NumberTheory.Ostmann.Conclusion.OverlapComponents

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.PermutationHaar
open IncidenceHaar

variable {r m : ℕ} {G : Type*} [CommGroup G]

abbrev source (_σ : Equiv.Perm (Fin r × Fin m)) (e : Fin r × Fin m) : Fin r ⊕ Fin r :=
  Sum.inl e.1
abbrev target (σ : Equiv.Perm (Fin r × Fin m)) (e : Fin r × Fin m) : Fin r ⊕ Fin r :=
  Sum.inr (σ e).1

theorem edge_path (σ : Equiv.Perm (Fin r × Fin m)) (e : Fin r × Fin m) :
    Relation.EqvGen (edgeRelation (source σ) (target σ))
      (Sum.inl e.1) (Sum.inr (σ e).1) :=
  Relation.EqvGen.rel _ _ ⟨e,rfl,rfl⟩

theorem left_path (σ : Equiv.Perm (Fin r × Fin m)) {a b : Fin r}
    (h : Conclusion.leftComponent σ a = Conclusion.leftComponent σ b) :
    Relation.EqvGen (edgeRelation (source σ) (target σ)) (Sum.inl a) (Sum.inl b) := by
  have hp : Relation.EqvGen (Conclusion.overlapRelation σ) a b := Quotient.exact h
  clear h
  induction hp with
  | rel a b h =>
      obtain ⟨u,v,h⟩ := h
      have hright := edge_path σ (b,v)
      rw [← h] at hright
      exact Relation.EqvGen.trans _ _ _ (edge_path σ (a,u))
        (Relation.EqvGen.symm _ _ hright)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def label (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m) :
    Fin r ⊕ Fin r → Conclusion.OverlapComponent σ :=
  Sum.elim (Conclusion.leftComponent σ) (Conclusion.rightComponent σ hm)

def root (σ : Equiv.Perm (Fin r × Fin m)) (c : Conclusion.OverlapComponent σ) :
    Fin r ⊕ Fin r := Sum.inl c.out

theorem label_root (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m)
    (c : Conclusion.OverlapComponent σ) : label σ hm (root σ c) = c := Quotient.out_eq c

theorem path_root (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m)
    (v : Fin r ⊕ Fin r) :
    Relation.EqvGen (edgeRelation (source σ) (target σ)) v (root σ (label σ hm v)) := by
  cases v with
  | inl a =>
      exact left_path σ (Quotient.out_eq (Conclusion.leftComponent σ a)).symm
  | inr b =>
      let e := σ.symm (b,⟨0,hm⟩)
      have he : Relation.EqvGen (edgeRelation (source σ) (target σ))
          (Sum.inl e.1) (Sum.inr b) := by simpa [e] using edge_path σ e
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ he)
        (left_path σ (Quotient.out_eq (Conclusion.leftComponent σ e.1)).symm)

def coupled (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m) :
    Subgroup ((Fin r → G) × (Fin r → G)) where
  carrier := {x | ∀ c : Conclusion.OverlapComponent σ,
    fiberProduct (Conclusion.leftComponent σ) c x.1 =
      fiberProduct (Conclusion.rightComponent σ hm) c x.2}
  one_mem' := by intro c; simp
  mul_mem' hx hy := by intro c; simp only [Prod.fst_mul,Prod.snd_mul,map_mul,hx c,hy c]
  inv_mem' hx := by intro c; simp only [Prod.fst_inv,Prod.snd_inv,map_inv,hx c]

def products (σ : Equiv.Perm (Fin r × Fin m)) :
    (Fin r × Fin m → G) →* ((Fin r → G) × (Fin r → G)) :=
  BipartiteHaar.slotProducts Prod.fst (fun e => (σ e).1)

theorem products_range (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m) :
    (products (G:=G) σ).range = coupled σ hm := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    intro c
    have h := fiberProduct_boundary (source σ) (target σ) (label σ hm)
      (Conclusion.slot_component σ hm) c y
    rw [← BipartiteHaar.signed_slotProducts] at h
    change fiberProduct (Sum.elim (Conclusion.leftComponent σ)
      (Conclusion.rightComponent σ hm)) c
      (BipartiteHaar.signedEquiv (products σ y)) = 1 at h
    rw [BipartiteHaar.fiberProduct_signed,div_eq_one] at h
    exact h
  · intro hx
    have hb : BipartiteHaar.signedEquiv x ∈ (boundary (source σ) (target σ)).range := by
      apply mem_range_of_component_products (source σ) (target σ) (label σ hm)
        (root σ) (label_root σ hm) (path_root σ hm)
      intro c
      change fiberProduct (Sum.elim (Conclusion.leftComponent σ)
        (Conclusion.rightComponent σ hm)) c (BipartiteHaar.signedEquiv x) = 1
      rw [BipartiteHaar.fiberProduct_signed,div_eq_one]
      exact hx c
    obtain ⟨y,hy⟩ := hb
    refine ⟨y,BipartiteHaar.signedEquiv.injective ?_⟩
    exact (BipartiteHaar.signed_slotProducts _ _ y).trans hy

def toCoupled (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m) :
    (Fin r × Fin m → G) →* coupled (G:=G) σ hm :=
  (products σ).codRestrict (coupled σ hm) (fun x => by
    rw [← products_range]
    exact ⟨x,rfl⟩)

theorem toCoupled_surjective (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m) :
    Function.Surjective (toCoupled (G:=G) σ hm) := by
  intro x
  have hx : x.val ∈ (products σ).range := by rw [products_range]; exact x.property
  obtain ⟨y,hy⟩ := hx
  exact ⟨y,Subtype.ext hy⟩

instance coupledFintype [Fintype G] (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m) :
    Fintype (coupled (G:=G) σ hm) := Fintype.ofFinite _

theorem products_uniform [Fintype G] (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m)
    (F : coupled (G:=G) σ hm → ℂ) :
    ResidueHaar.average (fun x => F (toCoupled σ hm x)) = ResidueHaar.average F :=
  GroupHaarImage.average_surjective _ (toCoupled_surjective σ hm) F

end Ostmann.Arithmetic.PermutationHaar

end

end OAI
