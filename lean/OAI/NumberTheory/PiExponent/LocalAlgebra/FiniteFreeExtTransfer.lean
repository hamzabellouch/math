import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

namespace OAI

noncomputable section
universe w v u

namespace PiExponentSiegelAux.W31
open Module
open CategoryTheory CategoryTheory.Abelian
open scoped BigOperators

section General
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_subsingleton_of_finite_identity_factorization
    {ι : Type*} [Fintype ι] (X F G : C) (n : ℕ)
    (p : ι → (F ⟶ G)) (j : ι → (G ⟶ F))
    (htotal : (∑ i, p i ≫ j i) = 𝟙 F)
    (h : Subsingleton (Ext X G n)) : Subsingleton (Ext X F n) := by
  apply subsingleton_of_forall_eq 0
  intro e
  have he : (∑ i, (e.comp (Ext.mk₀ (p i)) (add_zero n)).comp
      (Ext.mk₀ (j i)) (add_zero n)) = e := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      ← Ext.comp_sum, ← Ext.mk₀_sum, htotal, Ext.comp_mk₀_id]
  calc
    e = _ := he.symm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [h.elim (e.comp (Ext.mk₀ (p i)) (add_zero n)) 0, Ext.zero_comp]

end General

variable {R : Type u} [CommRing R]
variable {F : Type u} [AddCommGroup F] [Module R F]

theorem ext_subsingleton_of_finite_basis {ι : Type*} [Fintype ι]
    (b : Basis ι R F) (X : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext X (ModuleCat.of R F) n) := by
  apply ext_subsingleton_of_finite_identity_factorization X (ModuleCat.of R F)
    (ModuleCat.of R R) n
    (fun i => ModuleCat.ofHom (b.coord i))
    (fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b i))) ?_ h
  apply ModuleCat.hom_ext
  ext x
  simpa only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    ModuleCat.hom_id, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, Basis.coord_apply, LinearMap.id_apply] using
    b.sum_repr x

theorem ext_subsingleton_of_finite_free [Module.Free R F] [Module.Finite R F]
    (X : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext X (ModuleCat.of R F) n) :=
  ext_subsingleton_of_finite_basis (Module.Free.chooseBasis R F) X n h

end PiExponentSiegelAux.W31

end

end OAI
