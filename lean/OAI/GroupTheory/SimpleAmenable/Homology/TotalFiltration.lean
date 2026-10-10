import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ConcreteHomology
import OAI.GroupTheory.SimpleAmenable.Homology.TotalProjection

namespace OAI

section

section

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma projection_eq_zero (p q n : ℕ) (h : p+q≠n) : projection K p q n = 0 := by
  apply total.hom_ext
  intro i j hij
  rw [inclusion_projection_of_ne]
  · simp
  · intro h'
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj h'
    exact h hij

lemma element_ext {n : ℕ} {x y : (K.total c).X n}
    (h : ∀ i : Index n,proj K n i x = proj K n i y) : x=y := by
  have hx := congrArg (fun f : (K.total c).X n ⟶ (K.total c).X n => f x)
    (sum_projection_inclusion K n)
  have hy := congrArg (fun f : (K.total c).X n ⟶ (K.total c).X n => f y)
    (sum_projection_inclusion K n)
  simp only [ModuleCat.hom_sum,LinearMap.sum_apply,ModuleCat.comp_apply,ModuleCat.id_apply] at hx hy
  rw [←hx,←hy]
  exact Finset.sum_congr rfl (fun i _ => congrArg (inclusion K n i) (h i))

def filtration (n : ℕ) (p : ℤ) : Submodule R ((K.total c).X n) where
  carrier := { x | ∀ i : Index n, p ≤ (i.val.1:ℤ) → proj K n i x=0 }
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [map_add,hx i hi,hy i hi]
  smul_mem' := by intro r x hx i hi; simp [map_smul,hx i hi]

lemma filtration_mono (n : ℕ) : Monotone (filtration K n) := by
  intro p q hpq x hx i hi
  exact hx i (hpq.trans hi)

lemma filtration_zero (n : ℕ) : filtration K n 0=⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply (Submodule.mem_bot R).mpr
  apply element_ext K
  intro i
  simpa using hx i (by omega)

lemma filtration_top (n : ℕ) : filtration K n (n+1)=⊤ := by
  apply top_unique
  intro x _ i hi
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp i.property
  omega

lemma entry_zero {n p q : ℕ} {k : ℤ} {x : (K.total c).X n}
    (hx : x∈filtration K n k) (hp : k≤(p:ℤ)) : projection K p q n x=0 := by
  by_cases h : p+q=n
  · exact hx ⟨(p,q),Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩ hp
  · rw [projection_eq_zero K p q n h]; rfl

lemma inclusion_mem {p q n : ℕ} (h : p+q=n) (x : (K.X p).X q) {k : ℤ}
    (hp : (p:ℤ)<k) : K.ιTotal c p q n h x ∈ filtration K n k := by
  intro i hi
  have he := inclusion_projection_of_ne K p q i.val.1 i.val.2 n h (by
    intro h'
    have he := congrArg Prod.fst h'
    dsimp at he
    omega)
  exact congrArg (fun f : (K.X p).X q ⟶ (K.X i.val.1).X i.val.2 => f x) he

lemma d_filtration {n m : ℕ} {k : ℤ} {x : (K.total c).X n}
    (hx : x∈filtration K n k) : (K.total c).d n m x∈filtration K m k := by
  by_cases h : m+1=n
  · subst n
    intro i hi
    obtain ⟨⟨p,q⟩,hpq⟩ := i
    have hpq' : p+q=m := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    subst m
    have hd := congrArg (fun f : (K.total c).X (p+q+1) ⟶ (K.X p).X q => f x)
      (d_projection K p q)
    change projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) x)=0
    simp only [ModuleCat.comp_apply] at hd
    rw [hd]
    change (projection K (p+1) q (p+q+1) ≫ (K.d (p+1) p).f q +
      ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+q+1) ≫ (K.X p).d (q+1) q)).hom x=0
    simp only [ModuleCat.hom_add,LinearMap.add_apply,ModuleCat.hom_comp,LinearMap.comp_apply,Units.smul_def,ModuleCat.hom_zsmul,LinearMap.smul_apply,
      entry_zero K hx (by dsimp at hi; omega : k≤((p+1:ℕ):ℤ)),entry_zero K hx hi,map_zero,smul_zero,add_zero]
  · rw [(K.total c).shape n m (by exact h)]
    exact (filtration K m k).zero_mem

noncomputable def filteredData (n : ℕ) : FilteredFiniteness.Data
    (R:=R) (A:=(K.total c).X (n+1)) (B:=(K.total c).X n) (C:=(K.total c).X (n-1)) where
  d := ((K.total c).d (n+1) n).hom
  e := ((K.total c).d n (n-1)).hom
  de := by exact ModuleCat.hom_ext_iff.mp ((K.total c).d_comp_d (n+1) n (n-1))
  FA := filtration K (n+1)
  FB := filtration K n
  FC := filtration K (n-1)
  monoB := filtration_mono K n

end TotalProjection

end

section

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma d_entry (p q : ℕ) (x : (K.total c).X (p+q+1)) :
    projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) x) =
      (K.d (p+1) p).f q (projection K (p+1) q (p+q+1) x) +
      ((-1 : ℤˣ)^p) • (K.X p).d (q+1) q (projection K p (q+1) (p+q+1) x) := by
  have h := congrArg (fun f : (K.total c).X (p+q+1) ⟶ (K.X p).X q => f.hom x)
    (d_projection K p q)
  simpa only [ModuleCat.hom_add,ModuleCat.hom_comp,LinearMap.comp_apply,LinearMap.add_apply,
    Units.smul_def,ModuleCat.hom_zsmul,LinearMap.smul_apply] using h

lemma d_entry' (p q n m : ℕ) (hn : p+q+1=n) (hm : p+q=m) (x : (K.total c).X n) :
    projection K p q m ((K.total c).d n m x) =
      (K.d (p+1) p).f q (projection K (p+1) q n x) +
      ((-1 : ℤˣ)^p) • (K.X p).d (q+1) q (projection K p (q+1) n x) := by
  subst n; subst m; exact d_entry K p q x

lemma z₂_top_cycle (p q : ℕ) (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1)) :
    (K.X p).d q (q-1) (projection K p q (p+q) x)=0 := by
  cases q with
  | zero => rw [(K.X p).shape 0 (0-1) (by decide)]; rfl
  | succ q =>
    rw [show q+1-1=q by omega]
    have hd := d_entry K p q x.val
    have hz : projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) x.val)=0 := by
      apply entry_zero K x.property.2
      omega
    have hf : projection K (p+1) q (p+q+1) x.val=0 := entry_zero K x.property.1 (by omega)
    rw [hz,hf,map_zero,zero_add] at hd
    have hs : ((-1 : ℤˣ)^p) • (K.X p).d (q+1) q (projection K p (q+1) (p+q+1) x.val)=0 := hd.symm
    have hh := congrArg (fun z => (((-1 : ℤˣ)^p)⁻¹) • z) hs
    rw [inv_smul_smul,smul_zero] at hh
    exact hh

noncomputable def topCycle (p q : ℕ) : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) →ₗ[R]
    ConcreteHomology.Cycles (K.X p) q :=
  ((projection K p q (p+q)).hom.comp ((filteredData K (p+q)).Z₂ ((p:ℤ)+1)).subtype).codRestrict
    _ (z₂_top_cycle K p q)

noncomputable def row (q : ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((ConcreteHomology.functor q).mapHomologicalComplex c).obj K

lemma z₂_top_horizontal (p q : ℕ) (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1)) :
    (row K q).d p (p-1) (ConcreteHomology.π (K.X p) q (topCycle K p q x))=0 := by
  cases p with
  | zero => rw [(row K q).shape 0 (0-1) (by decide)]; rfl
  | succ p =>
    change ((ConcreteHomology.functor q).map (K.d (p+1) p)).hom
      (ConcreteHomology.π (K.X (p+1)) q (topCycle K (p+1) q x))=0
    rw [ConcreteHomology.map_π]
    apply (ConcreteHomology.π_eq_zero (K.X p) q _).mpr
    have hd := d_entry' K p q (p+1+q) (p+1+q-1) (by omega) (by omega) x.val
    have hz : projection K p q (p+1+q-1) ((K.total c).d (p+1+q) (p+1+q-1) x.val)=0 := by
      apply entry_zero K x.property.2
      omega
    rw [hz] at hd
    refine ⟨- ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+1+q) x.val),?_⟩
    apply Subtype.ext
    rw [ConcreteHomology.cyclesMap_val]
    change (K.X p).d (q+1) q (- ((-1 : ℤˣ)^p) • (projection K p (q+1) (p+1+q) x.val))=
      (K.d (p+1) p).f q (projection K (p+1) q (p+1+q) x.val)
    simp only [Units.smul_def,map_zsmul,Units.val_neg,neg_smul,map_neg]
    simpa only [Units.smul_def] using (eq_neg_of_add_eq_zero_left hd.symm).symm

noncomputable def topRowCycle (p q : ℕ) : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) →ₗ[R]
    ConcreteHomology.Cycles (row K q) p :=
  ((ConcreteHomology.π (K.X p) q).comp (topCycle K p q)).codRestrict _ (z₂_top_horizontal K p q)

noncomputable def lead (p q : ℕ) : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) →ₗ[R]
    ConcreteHomology.H (row K q) p :=
  (ConcreteHomology.π (row K q) p).comp (topRowCycle K p q)

end E2Leading

end

end

end OAI
