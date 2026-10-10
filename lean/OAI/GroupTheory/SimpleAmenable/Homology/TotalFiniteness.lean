import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.EilenbergZilber
import OAI.GroupTheory.SimpleAmenable.Homology.E2Boundary

namespace OAI

section

section

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalFiniteness

universe u
variable {R : Type u} [CommRing R]
abbrev c := ComplexShape.down ℕ
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

noncomputable def row (q : ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((homologyFunctor (ModuleCat.{u} R) c q).mapHomologicalComplex c).obj K

noncomputable def rowIso (q : ℕ) : row K q ≅ E2Leading.row K q :=
  (NatIso.mapHomologicalComplex (ConcreteHomology.naturalIso q) c).app K

noncomputable def rowHomologyIso (p q : ℕ) : (row K q).homology p ≅
    ModuleCat.of R (ConcreteHomology.H (E2Leading.row K q) p) :=
  (homologyFunctor _ c p).mapIso (rowIso K q) ≪≫ ConcreteHomology.iso _ _

lemma finite [IsNoetherianRing R] (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite R ((row K q).homology p)) :
    Module.Finite R ((K.total c).homology n) := by
  apply E2Leading.finite_total K n
  intro p q hpq
  have := hfinite p q hpq
  exact Module.Finite.equiv (rowHomologyIso K p q).toLinearEquiv

end TotalFiniteness

namespace EilenbergZilber
open DiagonalResolution ModelAssembly
variable (X : Dᵒᵖ ⥤ Type)

lemma finite_diagonal (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite ℤ
      ((TotalFiniteness.row (twoComplex X) q).homology p)) :
    Module.Finite ℤ (SSet.homology (C := A) (diag ⋙ X) Z n) := by
  have := TotalFiniteness.finite (twoComplex X) n hfinite
  exact Module.Finite.equiv (homologyIso X n).symm.toLinearEquiv

end EilenbergZilber

end

section

namespace FilteredFiniteness.Data

universe u
variable {R : Type u} [CommRing R]
variable {A B C : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
variable (K : FilteredFiniteness.Data (R:=R) (A:=A) (B:=B) (C:=C))

lemma subsingleton_H (N : ℕ) (hzero : K.FB 0=⊥) (htop : K.FB (N+1)=⊤)
    (hzeroE : ∀ p : ℕ, p≤N → Subsingleton (K.E₂ (p+1))) : Subsingleton K.H := by
  have hz : K.filtration 0=⊥ := by
    apply le_antisymm _ bot_le
    rintro y ⟨x,rfl⟩
    have hx : x=0 := by
      apply Subtype.ext; apply Subtype.ext
      exact (Submodule.mem_bot R).mp (hzero ▸ x.property)
    rw [hx,map_zero]
    exact Submodule.zero_mem _
  have hf : ∀ p : ℕ, p≤N+1 → K.filtration p=⊥ := by
    intro p hp
    induction p with
    | zero => exact hz
    | succ p ih =>
      have hl := ih (by omega)
      have := hzeroE p (by omega)
      apply le_antisymm _ bot_le
      rintro y ⟨x,rfl⟩
      have he : K.lead ((p:ℤ)+1) x=0 := Subsingleton.elim _ _
      have hh := K.lower_of_lead_zero x he
      change K.π x.val∈K.filtration (((p+1:ℕ):ℤ)-1) at hh
      have hidx : ((p+1:ℕ):ℤ)-1=(p:ℤ) := by omega
      rw [hidx,hl] at hh
      exact hh
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.dCycles) y
  have hy : K.π z∈K.filtration ((N+1:ℕ):ℤ) := by
    refine ⟨⟨z,?_⟩,rfl⟩
    change z.val∈K.FB ((N+1:ℕ):ℤ)
    rw [Nat.cast_add,Nat.cast_one,htop]; trivial
  rw [hf (N+1) le_rfl] at hy
  exact hy
end FilteredFiniteness.Data

open CategoryTheory HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma subsingleton_E₂ (p q : ℕ) [Subsingleton (ConcreteHomology.H (row K q) p)] :
    Subsingleton ((filteredData K (p+q)).E₂ ((p:ℤ)+1)) := by
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective _ y
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (lead_zero_boundary K p q x (Subsingleton.elim _ _))

lemma subsingleton_total_concrete (n : ℕ)
    (hzero : ∀ p q, p+q=n → Subsingleton (ConcreteHomology.H (row K q) p)) :
    Subsingleton (ConcreteHomology.H (K.total c) n) := by
  change Subsingleton (filteredData K n).H
  apply FilteredFiniteness.Data.subsingleton_H _ n (filtration_zero K n) (filtration_top K n)
  intro p hp
  have hn : p+(n-p)=n := Nat.add_sub_of_le hp
  have := hzero p (n-p) hn
  have h := subsingleton_E₂ K p (n-p)
  rwa [hn] at h
end E2Leading

namespace TotalFiniteness

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma subsingleton (n : ℕ)
    (hzero : ∀ p q, p+q=n → Subsingleton ((row K q).homology p)) :
    Subsingleton ((K.total c).homology n) := by
  have : Subsingleton (ConcreteHomology.H (K.total c) n) := by
    apply E2Leading.subsingleton_total_concrete K n
    intro p q hpq
    have := hzero p q hpq
    exact (rowHomologyIso K p q).toLinearEquiv.symm.injective.subsingleton
  exact (ConcreteHomology.iso (K.total c) n).toLinearEquiv.injective.subsingleton
end TotalFiniteness

namespace EilenbergZilber
open DiagonalResolution ModelAssembly
variable (X : Dᵒᵖ ⥤ Type)
lemma subsingleton_diagonal (n : ℕ)
    (hzero : ∀ p q, p+q=n → Subsingleton
      ((TotalFiniteness.row (twoComplex X) q).homology p)) :
    Subsingleton (SSet.homology (C:=A) (diag ⋙ X) Z n) := by
  have := TotalFiniteness.subsingleton (twoComplex X) n hzero
  exact (homologyIso X n).toLinearEquiv.injective.subsingleton
end EilenbergZilber

end

end

end OAI
